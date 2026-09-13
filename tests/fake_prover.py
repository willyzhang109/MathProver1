#!/usr/bin/env python3
"""Stand-in for the real prover: speaks the JSONL protocol on a timer.

Exercises the runner, status tailer, retention and the whole frontend without
spending Gemini quota or 20 minutes per attempt.

Env knobs:
  FAKE_ROUNDS=3      how many iterations to emit
  FAKE_DELAY=0.3     seconds between iterations
  FAKE_OUTCOME=proved|unproved|crash|hang
  FAKE_FORK=1        fork a child that ignores SIGTERM (tests SIGKILL escalation)
"""
import os, signal, sys, time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from prover_events import emit, write_result

target = sys.argv[1] if len(sys.argv) > 1 else "target.lean"
rounds = int(os.environ.get("FAKE_ROUNDS", "3"))
delay = float(os.environ.get("FAKE_DELAY", "0.3"))
outcome = os.environ.get("FAKE_OUTCOME", "proved")

emit("run_start", script="fake_prover.py", num_procs=1, target=target)
emit("worker_start", worker_id=1)
emit("server_ready", imports=["Init", "Mathlib"], startup_s=0.1)

if os.environ.get("FAKE_FORK") == "1":
    if os.fork() == 0:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        while True:
            time.sleep(1)

lean = open(target, encoding="utf-8").read() if os.path.exists(target) else "theorem t : True := by sorry"

for i in range(1, rounds + 1):
    emit("iteration", n=i, tokens_used=i * 100, max_tokens=10000)
    emit("sketch", lean=lean.replace("sorry", f"-- attempt {i}\n  sorry"), chars=len(lean))
    emit("compile", duration_s=0.2, n_errors=max(0, rounds - i),
         errors=[{"line": 4, "column": 2, "end_line": 4, "end_column": 7,
                  "severity": "error", "message": f"unsolved goals (attempt {i})"}]
         if i < rounds else [])
    emit("blocks", count=max(1, rounds - i + 1))
    if i > 1:
        emit("block_closed", block_id=0, remaining=max(0, rounds - i))
    time.sleep(delay)

if outcome == "crash":
    emit("worker_error", exc_type="RuntimeError", message="synthetic crash")
    emit("worker_end", worker_id=1, rc=1)
    emit("run_end", rc=1)
    sys.exit(1)

if outcome == "hang":
    while True:
        time.sleep(1)

if outcome == "proved":
    emit("verify_start")
    emit("verify_result", success=True, status="VERIFIED",
         message="Integrity check passed.", report={"user_thm": {"failureMode": None}})
    proved = lean.replace("sorry", "trivial")
    write_result({"success": True, "lean": proved, "nl": "A synthetic proof.", "worker_pid": os.getpid()})
    emit("proof_found", chars=len(proved))
    emit("worker_end", worker_id=1, rc=0)
    emit("run_end", rc=0)
    sys.exit(0)

emit("worker_end", worker_id=1, rc=1)
emit("run_end", rc=1)
sys.exit(1)
