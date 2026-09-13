"""Spawn, supervise, and reliably kill a prover subprocess."""

import asyncio
import contextlib
import json
import logging
import os
import shutil
import signal
import time
from pathlib import Path
from typing import Optional

from ..config import settings
from ..lean import olean
from .statuslog import StatusTailer
from .store import Job

log = logging.getLogger("runner")

POLL_INTERVAL = 0.5
GRACE_SECONDS = 10


class JobRunner:
    def __init__(self, job: Job):
        self.job = job
        self.dir = Path(settings.runs_dir) / job.id
        self.proc: Optional[asyncio.subprocess.Process] = None

    # --- filesystem -------------------------------------------------------
    def prepare_dirs(self) -> None:
        for sub in ("status", "scratch", "verify", "result"):
            (self.dir / sub).mkdir(parents=True, exist_ok=True)
        self.job.job_dir = self.dir

    def write_inputs(self) -> Path:
        target = self.dir / "target.lean"
        target.write_text(self.job.normalized_lean, encoding="utf-8")
        if self.job.mode == "nl":
            (self.dir / "problem.txt").write_text(self.job.user_nl, encoding="utf-8")
        return target

    # --- child environment ------------------------------------------------
    async def child_env(self) -> dict:
        env = {
            "PATH": os.environ.get("PATH", ""),
            "HOME": os.environ.get("HOME", ""),
            "LANG": os.environ.get("LANG", "en_US.UTF-8"),
            "PYTHONUNBUFFERED": "1",
            "GEMINI_API_KEY": settings.gemini_api_key,
            "GOOGLE_API_KEY": settings.gemini_api_key,
            # Reuse the server-built reference olean; never let the script run
            # `lake clean` against the shared build tree.
            "PROVER_NO_LAKE_PRELUDE": "1",
            "PROVER_REUSE_OLEAN": "1",
            "PROVER_STRICT_EXIT": "1",
            "PROVER_PROJECT_PATH": str(settings.lake_root),
            "PROVER_STATUS_DIR": str(self.dir / "status"),
            "PROVER_SCRATCH_DIR": str(self.dir / "scratch"),
            "PROVER_RESULT_DIR": str(self.dir / "result"),
            "SAFEVERIFY_SCRATCH_DIR": str(self.dir / "verify"),
            "SAFEVERIFY_HEADER": "import Mathlib",
            # Exit a minute before the hard kill so a partial result flushes.
            "PROVER_WALL_SECONDS": str(max(60, settings.job_timeout_s - 60)),
        }
        if settings.model:
            env["PROVER_MODEL"] = settings.model
        if settings.max_iters:
            env["PROVER_MAX_ITERS"] = str(settings.max_iters)
        passthrough = ["SAFEVERIFY_BIN", "SAFEVERIFY_LEAN_CMD", "HTTPS_PROXY", "HTTP_PROXY",
                       "NO_PROXY", "LEAN_CC"] + list(settings.env_passthrough)
        for var in passthrough:
            if os.environ.get(var):
                env[var] = os.environ[var]
        env.update(await olean.lean_env())
        return env

    def argv(self, target: Path) -> list:
        if settings.prover_cmd:              # test hook: PROVER_CMD=/path/to/fake
            return list(settings.prover_cmd) + [str(target)]

        common = ["--libs", *settings.libs,
                  "--num_procs", str(settings.num_procs),
                  "--token_limit", str(settings.token_limit)]
        if self.job.mode == "nl":
            return [settings.python_bin, settings.script_path("whole_proof_subagent.py"),
                    str(self.dir / "problem.txt"), str(target), *common]
        return [settings.python_bin, settings.script_path("prover_subagent.py"),
                str(target), *common]

    # --- lifecycle --------------------------------------------------------
    async def run(self) -> None:
        job = self.job
        try:
            job.set_phase("preparing")
            self.prepare_dirs()
            target = self.write_inputs()

            job.set_phase("checking")
            ok, output = await olean.build_reference(target)
            if not ok:
                job.set_phase("failed", "invalid",
                              "Could not compile the reference statement.\n" + output[:2000])
                return

            if job.cancel_requested:
                job.set_phase("cancelled", "error", "Cancelled before starting.")
                return

            await self._spawn_and_watch(target)
        except asyncio.CancelledError:
            await self.kill()
            job.set_phase("cancelled", "error", "Cancelled.")
            raise
        except Exception as exc:  # noqa: BLE001
            log.exception("job %s failed", job.id)
            job.set_phase("failed", "error", f"Internal error: {exc}")
        finally:
            self._cleanup()

    async def _spawn_and_watch(self, target: Path) -> None:
        job = self.job
        env = await self.child_env()
        argv = self.argv(target)
        log_path = self.dir / "stdout.log"

        # A real file, never a PIPE: these scripts print entire sketches and
        # full model responses each turn, and an undrained pipe deadlocks the
        # child at the OS buffer limit.
        with open(log_path, "ab") as sink:
            self.proc = await asyncio.create_subprocess_exec(
                *argv,
                cwd=str(settings.lake_root),
                env=env,
                stdin=asyncio.subprocess.DEVNULL,
                stdout=sink,
                stderr=asyncio.subprocess.STDOUT,
                start_new_session=True,   # own process group -> killpg works
            )

        try:
            job.pgid = os.getpgid(self.proc.pid)
        except (ProcessLookupError, OSError):
            job.pgid = self.proc.pid

        job.set_phase("proving")
        log.info("job %s pid=%s pgid=%s", job.id, self.proc.pid, job.pgid)

        tailer = StatusTailer(job, self.dir / "status")
        deadline = time.time() + settings.job_timeout_s
        timed_out = False

        while True:
            try:
                await asyncio.wait_for(self.proc.wait(), timeout=POLL_INTERVAL)
                break
            except asyncio.TimeoutError:
                pass

            tailer.poll()

            if job.cancel_requested:
                await self.kill()
                await self.proc.wait()
                tailer.poll()
                job.set_phase("cancelled", "error", "Cancelled at your request.")
                return

            if time.time() > deadline:
                timed_out = True
                await self.kill()
                await self.proc.wait()
                break

        tailer.poll()   # final drain
        self._finish(timed_out)

    def _finish(self, timed_out: bool) -> None:
        job = self.job
        rc = self.proc.returncode if self.proc else None
        result = self._read_result()

        if result:
            job.result = result
            job.current_lean = result.get("lean") or job.current_lean
            job.current_nl = result.get("nl") or job.current_nl

        if job.cancel_requested:
            # cancel() kills the child directly, so proc.wait() can return and
            # break the watch loop before the in-loop cancel check is reached.
            job.set_phase("cancelled", "error", "Cancelled at your request.")
        elif timed_out:
            job.set_phase("timeout", "unproved",
                          f"Reached the {settings.job_timeout_s // 60}-minute limit.")
        elif result and result.get("success"):
            # The result file is authoritative; the exit code is corroboration.
            job.set_phase("succeeded", "proved")
        elif rc == 0 and job.safeverify and job.safeverify.get("success"):
            job.set_phase("succeeded", "proved")
        else:
            job.set_phase("failed", "unproved",
                          job.error_message or "No verified proof was found.")

    def _read_result(self) -> Optional[dict]:
        result_dir = self.dir / "result"
        if not result_dir.is_dir():
            return None
        for path in sorted(result_dir.glob("result_w*.json")):
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if data.get("success"):
                return data
        return None

    async def kill(self) -> None:
        """Kill the whole process group.

        proc.terminate() alone is wrong here: the script forks multiprocessing
        workers which each own a pantograph-repl holding Mathlib in memory.
        Those would survive as multi-GB orphans.
        """
        if not self.proc or self.proc.returncode is not None:
            return
        pgid = self.job.pgid or self.proc.pid

        with contextlib.suppress(ProcessLookupError, PermissionError, OSError):
            os.killpg(pgid, signal.SIGTERM)
        try:
            await asyncio.wait_for(self.proc.wait(), timeout=GRACE_SECONDS)
            return
        except asyncio.TimeoutError:
            pass
        with contextlib.suppress(ProcessLookupError, PermissionError, OSError):
            os.killpg(pgid, signal.SIGKILL)

    def _cleanup(self) -> None:
        """Shrink the job directory once the job is over."""
        for sub in ("scratch", "verify"):
            shutil.rmtree(self.dir / sub, ignore_errors=True)
        with contextlib.suppress(OSError):
            meta = {
                "id": self.job.id, "mode": self.job.mode, "phase": self.job.phase,
                "verdict": self.job.verdict, "created_at": self.job.created_at,
                "ended_at": self.job.ended_at, "iteration": self.job.iteration,
            }
            (self.dir / "meta.json").write_text(json.dumps(meta, indent=2), encoding="utf-8")
        with contextlib.suppress(OSError):
            if (self.dir / "result").is_dir() and self.job.result:
                (self.dir / "result.lean").write_text(
                    self.job.result.get("lean", ""), encoding="utf-8")
