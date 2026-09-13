"""FIFO job queue drained by a fixed pool of workers."""

import asyncio
import logging
from typing import Dict, List, Optional

from ..config import settings
from .runner import JobRunner
from .store import Job, store

log = logging.getLogger("queue")


class JobQueue:
    def __init__(self):
        self._queue: asyncio.Queue = asyncio.Queue(maxsize=settings.max_queue)
        self._pending: List[str] = []
        self._running: Dict[str, JobRunner] = {}
        self._tasks: List[asyncio.Task] = []

    # --- introspection ----------------------------------------------------
    @property
    def depth(self) -> int:
        return len(self._pending)

    @property
    def running_count(self) -> int:
        return len(self._running)

    def position(self, job_id: str) -> Optional[int]:
        try:
            return self._pending.index(job_id) + 1
        except ValueError:
            return None

    def full(self) -> bool:
        return self._queue.full()

    # --- lifecycle --------------------------------------------------------
    def start(self) -> None:
        for i in range(settings.max_concurrent_jobs):
            self._tasks.append(asyncio.create_task(self._worker(i)))
        log.info("started %d job workers", settings.max_concurrent_jobs)

    async def submit(self, job: Job) -> None:
        self._pending.append(job.id)
        try:
            self._queue.put_nowait(job.id)
        except asyncio.QueueFull:
            self._pending.remove(job.id)
            raise

    async def cancel(self, job: Job) -> None:
        job.cancel_requested = True
        job.touch()
        runner = self._running.get(job.id)
        if runner:
            await runner.kill()
        elif job.id in self._pending:
            # Still queued: mark it now, the worker will skip it.
            self._pending.remove(job.id)
            job.set_phase("cancelled", "error", "Cancelled before it started.")

    async def _worker(self, index: int) -> None:
        while True:
            job_id = await self._queue.get()
            if job_id in self._pending:
                self._pending.remove(job_id)

            job = store.get(job_id)
            try:
                if job is None:
                    continue
                if job.cancel_requested or not job.active:
                    if job.active:
                        job.set_phase("cancelled", "error", "Cancelled before it started.")
                    continue

                runner = JobRunner(job)
                self._running[job.id] = runner
                try:
                    await runner.run()
                finally:
                    self._running.pop(job.id, None)
            except asyncio.CancelledError:
                raise
            except Exception:  # noqa: BLE001
                log.exception("worker %d crashed on %s", index, job_id)
                if job and job.active:
                    job.set_phase("failed", "error", "Internal scheduling error.")
            finally:
                self._queue.task_done()

    async def shutdown(self) -> None:
        """Kill every running child before the process exits.

        Without this, systemd Restart=always leaves multi-GB pantograph
        processes behind with nothing tracking them.
        """
        for runner in list(self._running.values()):
            with_job = runner.job
            with_job.set_phase("failed", "error", "The server restarted while this job was running.")
            await runner.kill()
        for task in self._tasks:
            task.cancel()
        await asyncio.gather(*self._tasks, return_exceptions=True)


queue = JobQueue()
