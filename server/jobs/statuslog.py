"""Merge the prover's per-worker JSONL event files into live job state."""

import json
import logging
import os
from pathlib import Path
from typing import Dict, Tuple

from .store import Job

log = logging.getLogger("statuslog")


class StatusTailer:
    """Follows every w<pid>.jsonl in a job's status directory.

    One file per worker rather than one per job: the `sketch` events carry whole
    Lean proofs, far larger than PIPE_BUF, so appends from concurrent workers to
    a single file would interleave mid-line.
    """

    def __init__(self, job: Job, status_dir: Path):
        self.job = job
        self.status_dir = status_dir
        self._offsets: Dict[str, int] = {}
        self._partial: Dict[str, str] = {}

    def poll(self) -> bool:
        """Read whatever is new. Returns True if the job changed."""
        if not self.status_dir.is_dir():
            return False

        changed = False
        try:
            entries = sorted(os.scandir(self.status_dir), key=lambda e: e.name)
        except OSError:
            return False

        for entry in entries:
            if not entry.name.endswith(".jsonl"):
                continue
            changed |= self._read_file(Path(entry.path))

        if changed:
            self.job.touch()
        return changed

    def _read_file(self, path: Path) -> bool:
        key = path.name
        offset = self._offsets.get(key, 0)
        try:
            size = path.stat().st_size
            if size < offset:      # truncated/replaced
                offset = 0
                self._partial[key] = ""
            if size == offset:
                return False
            with open(path, "rb") as handle:
                handle.seek(offset)
                chunk = handle.read()
            self._offsets[key] = offset + len(chunk)
        except OSError:
            return False

        text = self._partial.pop(key, "") + chunk.decode("utf-8", "replace")
        lines = text.split("\n")
        self._partial[key] = lines.pop()  # trailing fragment, may be incomplete

        changed = False
        for line in lines:
            line = line.strip()
            if not line:
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            changed |= self.apply(event)
        return changed

    def apply(self, event: dict) -> bool:
        job, kind = self.job, event.get("event")
        pid = event.get("pid")
        job.last_event_ts = event.get("ts")

        if kind in ("worker_start", "worker_end", "server_ready", "verify_start",
                    "proof_found", "worker_error", "worker_timeout", "run_end",
                    "llm_error"):
            job.event_log.append({
                "ts": event.get("ts"), "event": kind,
                "summary": _summarize(event),
            })

        if kind == "worker_start":
            job.workers[pid] = {"pid": pid, "worker_id": event.get("worker_id"),
                                "iteration": 0, "alive": True}
        elif kind == "worker_end":
            job.workers.setdefault(pid, {"pid": pid}).update(
                {"alive": False, "rc": event.get("rc")})
        elif kind == "iteration":
            n = event.get("n", 0)
            job.workers.setdefault(pid, {"pid": pid, "alive": True})["iteration"] = n
            job.iteration = max(job.iteration, n)
            job.event_log.append({"ts": event.get("ts"), "event": "iteration",
                                  "summary": f"iteration {n}"})
        elif kind == "sketch":
            if event.get("lean"):
                job.current_lean = event["lean"]
            if event.get("nl"):
                job.current_nl = event["nl"]
        elif kind == "compile":
            job.errors = event.get("errors", [])
            job.event_log.append({
                "ts": event.get("ts"), "event": "compile",
                "summary": f"{event.get('n_errors', 0)} error(s) in {event.get('duration_s', 0)}s",
            })
        elif kind == "blocks":
            count = event.get("count", 0)
            job.blocks_total = max(job.blocks_total, count)
            job.blocks_closed = max(0, job.blocks_total - count)
        elif kind == "block_closed":
            job.blocks_closed += 1
        elif kind == "verify_start":
            if job.phase == "proving":
                job.phase = "verifying"
        elif kind == "verify_result":
            job.safeverify = {
                "success": event.get("success"),
                "status": event.get("status"),
                "message": event.get("message"),
                "report": event.get("report"),
            }
            # A failed verification sends the model back to work.
            if job.phase == "verifying" and not event.get("success"):
                job.phase = "proving"
            job.event_log.append({
                "ts": event.get("ts"), "event": "verify_result",
                "summary": f"{event.get('status')}: {event.get('message', '')[:120]}",
            })
        elif kind == "proof_found":
            job.result = dict(job.result or {}, lean=job.current_lean, nl=job.current_nl)

        return True


def _summarize(event: dict) -> str:
    kind = event.get("event")
    if kind == "server_ready":
        return f"Lean environment ready in {event.get('startup_s')}s"
    if kind == "worker_start":
        return f"worker {event.get('worker_id')} started"
    if kind == "worker_end":
        return f"worker {event.get('worker_id')} exited rc={event.get('rc')}"
    if kind == "worker_error":
        return f"worker error: {str(event.get('message'))[:160]}"
    if kind == "worker_timeout":
        return f"worker hit its {event.get('budget_s')}s budget"
    if kind == "llm_error":
        return f"model error: {str(event.get('message'))[:160]}"
    if kind == "proof_found":
        return "proof found, verifying"
    if kind == "verify_start":
        return "running SafeVerify"
    if kind == "run_end":
        return f"run finished rc={event.get('rc')}"
    return kind or ""
