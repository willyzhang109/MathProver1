"""Structured progress events for the prover scripts.

Entirely opt-in: every function here is a no-op unless ``PROVER_STATUS_DIR`` is
set in the environment, so running the scripts from the command line behaves
exactly as it did before this module existed.

Each process writes to its own file (``w<pid>.jsonl``) inside the status
directory. One shared file would not work: the ``sketch`` events carry whole
Lean proofs, which are far larger than PIPE_BUF, so appends from the racing
workers would interleave mid-line and corrupt the stream.
"""

import json
import os
import time
from typing import Any, Optional

MAX_LEAN_CHARS = 200_000
MAX_TEXT_CHARS = 8_000
MAX_ERROR_CHARS = 2_000
MAX_ERRORS = 20

_seq = 0
_path: Optional[str] = None
_resolved = False


def _status_path() -> Optional[str]:
    """Resolve (once) the per-process JSONL path, or None when disabled."""
    global _path, _resolved
    if _resolved:
        return _path

    _resolved = True
    status_dir = os.environ.get("PROVER_STATUS_DIR")
    if status_dir:
        try:
            os.makedirs(status_dir, exist_ok=True)
            _path = os.path.join(status_dir, f"w{os.getpid()}.jsonl")
        except OSError:
            _path = None
    return _path


def truncate(value: Any, limit: int = MAX_TEXT_CHARS) -> Any:
    """Cap a string so a runaway proof cannot fill the disk."""
    if not isinstance(value, str) or len(value) <= limit:
        return value
    return value[:limit] + f"\n... [truncated, {len(value)} chars total]"


def errors_payload(messages) -> list:
    """Normalize Pantograph messages into plain dicts for the status stream."""
    out = []
    for msg in (messages or [])[:MAX_ERRORS]:
        pos = getattr(msg, "pos", None)
        pos_end = getattr(msg, "pos_end", None)
        severity = getattr(msg, "severity", None)
        out.append({
            "line": getattr(pos, "line", None),
            "column": getattr(pos, "column", None),
            "end_line": getattr(pos_end, "line", None),
            "end_column": getattr(pos_end, "column", None),
            "severity": (severity.name.lower() if hasattr(severity, "name")
                         else str(severity).lower()),
            "message": truncate(getattr(msg, "data", "") or "", MAX_ERROR_CHARS),
        })
    return out


def emit(event: str, **fields: Any) -> None:
    """Append one event. Never raises into the prover."""
    global _seq
    path = _status_path()
    if not path:
        return

    try:
        _seq += 1
        record = {
            "ts": time.time(),
            "pid": os.getpid(),
            "seq": _seq,
            "event": event,
        }
        record.update(fields)
        line = json.dumps(record, ensure_ascii=False, default=str)
        with open(path, "a", encoding="utf-8") as handle:
            handle.write(line + "\n")
            handle.flush()
    except Exception:
        # Progress reporting must never take the prover down with it.
        pass


def write_result(payload: dict) -> Optional[str]:
    """Record a verified proof where the server can find it."""
    result_dir = os.environ.get("PROVER_RESULT_DIR")
    if not result_dir:
        return None

    try:
        os.makedirs(result_dir, exist_ok=True)
        path = os.path.join(result_dir, f"result_w{os.getpid()}.json")
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, ensure_ascii=False, default=str)
        return path
    except OSError:
        return None
