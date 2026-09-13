"""A pool of pre-warmed Lean checker subprocesses."""

import asyncio
import contextlib
import json
import logging
import os
import signal
import sys
from dataclasses import dataclass, field
from typing import List, Optional

from ..config import settings
from ..ids import new_id

log = logging.getLogger("checker")

WORKER = os.path.join(os.path.dirname(__file__), "checker_worker.py")


class CheckerError(RuntimeError):
    pass


class CheckerWarming(RuntimeError):
    pass


@dataclass
class CheckResult:
    messages: List[dict] = field(default_factory=list)
    units: List[dict] = field(default_factory=list)

    @property
    def errors(self) -> List[dict]:
        return [m for m in self.messages if m.get("severity") == "error"]

    @property
    def warnings(self) -> List[dict]:
        return [m for m in self.messages if m.get("severity") == "warning"]

    @property
    def ok(self) -> bool:
        return not self.errors


class Checker:
    """One subprocess. Not safe for concurrent use; the pool serializes access."""

    def __init__(self, index: int):
        self.index = index
        self.proc: Optional[asyncio.subprocess.Process] = None
        self.pgid: Optional[int] = None
        self.ready = False

    async def start(self) -> None:
        env = dict(os.environ)
        env["CHECKER_IMPORTS"] = ",".join(settings.checker_imports)
        env["PROVER_PROJECT_PATH"] = str(settings.lake_root)
        env["PYTHONUNBUFFERED"] = "1"

        self.proc = await asyncio.create_subprocess_exec(
            settings.python_bin, WORKER,
            cwd=str(settings.lake_root),
            env=env,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL,
            # Own process group. SIGTERM kills the Python worker before its
            # cleanup runs, stranding the pantograph-repl child that holds
            # Mathlib -- several GB of orphan per recycled checker.
            start_new_session=True,
        )
        try:
            self.pgid = os.getpgid(self.proc.pid)
        except (ProcessLookupError, OSError):
            self.pgid = self.proc.pid

        line = await asyncio.wait_for(self.proc.stdout.readline(),
                                      timeout=settings.checker_timeout_s)
        if not line:
            raise CheckerError(f"checker {self.index} died during startup")
        payload = json.loads(line.decode("utf-8", "replace"))
        if payload.get("event") != "ready":
            raise CheckerError(f"checker {self.index} failed: {payload.get('message')}")
        self.ready = True
        log.info("checker %d ready", self.index)

    async def compile(self, code: str) -> CheckResult:
        if not self.proc or self.proc.returncode is not None:
            raise CheckerError("checker is not running")

        req_id = new_id("req")
        self.proc.stdin.write(
            (json.dumps({"id": req_id, "code": code}, ensure_ascii=False) + "\n").encode())
        await self.proc.stdin.drain()

        line = await asyncio.wait_for(self.proc.stdout.readline(),
                                      timeout=settings.checker_timeout_s)
        if not line:
            raise CheckerError("checker closed its output")

        payload = json.loads(line.decode("utf-8", "replace"))
        if not payload.get("ok"):
            raise CheckerError(payload.get("error", "unknown checker error"))
        return CheckResult(messages=payload.get("messages", []),
                           units=payload.get("units", []))

    async def stop(self) -> None:
        self.ready = False
        if not self.proc or self.proc.returncode is not None:
            return
        pgid = self.pgid or self.proc.pid

        # Closing stdin ends the worker's read loop, so it shuts its Lean
        # server down cleanly in its own `finally`. Only escalate if it hangs.
        with contextlib.suppress(Exception):
            self.proc.stdin.close()
        try:
            await asyncio.wait_for(self.proc.wait(), timeout=8)
            return
        except asyncio.TimeoutError:
            pass

        with contextlib.suppress(ProcessLookupError, PermissionError, OSError):
            os.killpg(pgid, signal.SIGTERM)
        try:
            await asyncio.wait_for(self.proc.wait(), timeout=10)
        except asyncio.TimeoutError:
            with contextlib.suppress(ProcessLookupError, PermissionError, OSError):
                os.killpg(pgid, signal.SIGKILL)


class CheckerPool:
    def __init__(self, size: int = None):
        self.size = size if size is not None else settings.checker_pool_size
        self._free: asyncio.Queue = asyncio.Queue()
        self._all: List[Checker] = []
        self._warmup: Optional[asyncio.Task] = None

    @property
    def ready_count(self) -> int:
        return sum(1 for c in self._all if c.ready)

    def start_warmup(self) -> None:
        self._warmup = asyncio.create_task(self._warm())

    async def _warm(self) -> None:
        # Warm concurrently: importing Mathlib takes ~100s, and doing that
        # serially would leave the service unusable for size*100 seconds.
        async def one(i: int) -> None:
            checker = Checker(i)
            try:
                await checker.start()
            except Exception as exc:  # noqa: BLE001
                log.error("checker %d failed to warm: %s", i, exc)
                await checker.stop()
                return
            self._all.append(checker)
            await self._free.put(checker)

        await asyncio.gather(*(one(i) for i in range(self.size)), return_exceptions=True)

    @contextlib.asynccontextmanager
    async def acquire(self):
        if self.ready_count == 0:
            raise CheckerWarming("Lean checkers are still importing Mathlib")

        checker = await self._free.get()
        recycle = False
        try:
            yield checker
        except (CheckerError, asyncio.TimeoutError):
            # A wedged or crashed checker must not go back into rotation.
            recycle = True
            raise
        finally:
            if recycle:
                asyncio.create_task(self._recycle(checker))
            else:
                await self._free.put(checker)

    async def _recycle(self, checker: Checker) -> None:
        log.warning("recycling checker %d", checker.index)
        await checker.stop()
        try:
            await checker.start()
        except Exception as exc:  # noqa: BLE001
            log.error("checker %d failed to restart: %s", checker.index, exc)
            if checker in self._all:
                self._all.remove(checker)
            return
        await self._free.put(checker)

    async def compile(self, code: str) -> CheckResult:
        async with self.acquire() as checker:
            return await checker.compile(code)

    async def stop(self) -> None:
        if self._warmup and not self._warmup.done():
            self._warmup.cancel()
            with contextlib.suppress(asyncio.CancelledError):
                await self._warmup
        await asyncio.gather(*(c.stop() for c in self._all), return_exceptions=True)


pool = CheckerPool()
