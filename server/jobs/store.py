"""In-memory job records.

Everything here is lost when the process restarts. That is the chosen
tradeoff; the API surfaces it explicitly (a missing job says "the server may
have restarted" rather than a bare 404).
"""

import time
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Deque, Dict, List, Optional

from ..config import settings
from ..ids import new_id

ACTIVE_PHASES = {"queued", "preparing", "checking", "proving", "verifying"}
TERMINAL_PHASES = {"succeeded", "failed", "timeout", "cancelled"}


@dataclass
class Job:
    id: str
    mode: str                      # "lean" | "nl"
    ip_bucket: str
    title: str = ""
    phase: str = "queued"
    verdict: Optional[str] = None  # proved | unproved | invalid | error

    created_at: float = field(default_factory=time.time)
    started_at: Optional[float] = None
    ended_at: Optional[float] = None

    user_lean: str = ""
    user_nl: str = ""
    normalized_lean: str = ""
    job_dir: Optional[Path] = None

    revision: int = 1
    iteration: int = 0
    blocks_total: int = 0
    blocks_closed: int = 0

    current_lean: str = ""
    current_nl: str = ""
    errors: List[dict] = field(default_factory=list)
    last_event_ts: Optional[float] = None

    workers: Dict[int, dict] = field(default_factory=dict)
    result: Optional[dict] = None
    error_message: str = ""
    safeverify: Optional[dict] = None

    pgid: Optional[int] = None
    cancel_requested: bool = False
    event_log: Deque[dict] = field(default_factory=lambda: deque(maxlen=200))

    def touch(self) -> None:
        self.revision += 1

    @property
    def active(self) -> bool:
        return self.phase in ACTIVE_PHASES

    @property
    def elapsed(self) -> float:
        end = self.ended_at or time.time()
        start = self.started_at or self.created_at
        return max(0.0, end - start)

    def set_phase(self, phase: str, verdict: str = None, message: str = "") -> None:
        self.phase = phase
        if verdict:
            self.verdict = verdict
        if message:
            self.error_message = message
        if phase == "preparing" and self.started_at is None:
            self.started_at = time.time()
        if phase in TERMINAL_PHASES and self.ended_at is None:
            self.ended_at = time.time()
        self.touch()

    def summary(self) -> dict:
        return {
            "id": self.id,
            "mode": self.mode,
            "title": self.title,
            "phase": self.phase,
            "verdict": self.verdict,
            "created_at": self.created_at,
            "ended_at": self.ended_at,
            "elapsed_seconds": round(self.elapsed, 1),
        }

    def detail(self, queue_position: int = None, light: bool = False) -> dict:
        payload = self.summary()
        payload.update({
            "revision": self.revision,
            "started_at": self.started_at,
            "queue_position": queue_position,
            "time_budget_seconds": settings.job_timeout_s,
            "iteration": self.iteration,
            "blocks_total": self.blocks_total,
            "blocks_closed": self.blocks_closed,
            "errors": self.errors,
            "last_event_ts": self.last_event_ts,
            "error_message": self.error_message,
            "safeverify": self.safeverify,
            "workers": sorted(self.workers.values(), key=lambda w: w.get("pid", 0)),
            "result": self.result,
        })
        if light:
            payload["lean_chars"] = len(self.current_lean)
        else:
            payload["current_lean"] = self.current_lean
            payload["current_nl"] = self.current_nl
            payload["normalized_lean"] = self.normalized_lean
            payload["log_tail"] = list(self.event_log)[-40:]
        return payload


class JobStore:
    def __init__(self):
        self._jobs: Dict[str, Job] = {}

    def create(self, mode: str, ip_bucket: str, **kwargs) -> Job:
        job = Job(id=new_id("job"), mode=mode, ip_bucket=ip_bucket, **kwargs)
        self._jobs[job.id] = job
        return job

    def get(self, job_id: str) -> Optional[Job]:
        return self._jobs.get(job_id)

    def for_bucket(self, ip_bucket: str) -> List[Job]:
        jobs = [j for j in self._jobs.values() if j.ip_bucket == ip_bucket]
        return sorted(jobs, key=lambda j: j.created_at, reverse=True)

    def all(self) -> List[Job]:
        return list(self._jobs.values())

    def active_for_bucket(self, ip_bucket: str) -> List[Job]:
        return [j for j in self._jobs.values() if j.ip_bucket == ip_bucket and j.active]

    def prune(self, now: float = None) -> int:
        """Drop old terminal jobs; keep the store bounded."""
        now = now if now is not None else time.time()
        dropped = 0
        for job_id, job in list(self._jobs.items()):
            if job.active:
                continue
            if now - (job.ended_at or job.created_at) > settings.job_retention_s:
                del self._jobs[job_id]
                dropped += 1

        if len(self._jobs) > settings.max_jobs_kept:
            terminal = sorted((j for j in self._jobs.values() if not j.active),
                              key=lambda j: j.ended_at or j.created_at)
            for job in terminal[:len(self._jobs) - settings.max_jobs_kept]:
                del self._jobs[job.id]
                dropped += 1
        return dropped


store = JobStore()
