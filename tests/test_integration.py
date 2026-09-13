"""End-to-end API test with a stubbed prover and a stubbed checker.

Runs without Lean: the checker pool is replaced by a fake that accepts
anything. Lean-accurate normalization is covered by tests/test_normalize.py.
"""
import asyncio, os, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

os.environ.setdefault("GEMINI_API_KEY", "test-key")
os.environ["PROVER_CMD"] = f"{ROOT}/.venv/bin/python {ROOT}/tests/fake_prover.py"
os.environ["CHECKER_POOL_SIZE"] = "0"
os.environ["JOB_TIMEOUT_SECONDS"] = "20"
os.environ["MAX_CONCURRENT_JOBS"] = "2"
os.environ["FAKE_DELAY"] = "0.15"
os.environ["PER_IP_RUNNING"] = "1"
os.environ["PROVER_ENV_PASSTHROUGH"] = "FAKE_OUTCOME,FAKE_FORK,FAKE_ROUNDS,FAKE_DELAY"

from fastapi.testclient import TestClient
import server.app as appmod
from server.lean.checkers import CheckResult, pool
from server.lean import normalize
from server.jobs.store import store

FAILURES = []


def check(cond, label):
    print(("  ok   " if cond else "  FAIL ") + label)
    if not cond:
        FAILURES.append(label)


class FakeChecker:
    """Accepts anything; segments on blank-line-separated commands."""
    async def compile(self, code):
        messages, units = [], []
        offset, encoded = 0, code.encode()
        for chunk in code.split("\n\n"):
            raw = chunk.encode()
            units.append({"i_begin": offset, "i_end": offset + len(raw)})
            offset += len(raw) + 2
        if "BROKEN" in code:
            messages.append({"line": 1, "column": 0, "end_line": 1, "end_column": 5,
                             "severity": "error", "message": "synthetic error"})
        if "sorry" in code:
            messages.append({"line": 1, "column": 8, "end_line": None, "end_column": None,
                             "severity": "warning", "message": "declaration uses 'sorry'"})
        return CheckResult(messages=messages, units=units)


import contextlib


@contextlib.asynccontextmanager
async def fake_acquire():
    yield FakeChecker()


# Building the reference .olean really does import Mathlib and takes ~60s per
# job. That path is exercised for real in tests/test_reference_olean.py; here
# it is stubbed so the API behaviour can be tested in seconds.
from server.lean import olean as olean_mod


async def _fake_build(lean_file, timeout=300):
    lean_file.with_suffix(".olean").write_bytes(b"stub")
    return True, ""


async def _fake_env():
    return {}


olean_mod.build_reference = _fake_build
olean_mod.lean_env = _fake_env


pool.acquire = fake_acquire
pool.start_warmup = lambda: None
type(pool).ready_count = property(lambda self: 1)


def wait_for(client, job_id, terminal=("succeeded", "failed", "timeout", "cancelled"), limit=60):
    for _ in range(int(limit / 0.25)):
        r = client.get(f"/api/jobs/{job_id}")
        if r.status_code == 200 and r.json()["phase"] in terminal:
            return r.json()
        time.sleep(0.25)
    return client.get(f"/api/jobs/{job_id}").json()


def main():
    with TestClient(appmod.app) as client:
        print("health & limits:")
        r = client.get("/api/health")
        check(r.status_code == 200 and r.json()["ok"], "GET /api/health")
        r = client.get("/api/limits")
        check(r.json()["job"]["limit"] == 3, "GET /api/limits reports job limit 3")

        print("\nlean check:")
        r = client.post("/api/lean/check", json={"lean": "theorem foo : True := by sorry"})
        body = r.json()
        check(r.status_code == 200 and body["ok"], "valid statement -> ok")
        check(body["blocks"] == 1, "one EVOLVE block injected")
        check(body["normalized_lean"].startswith("import Mathlib"), "import header added")
        r = client.post("/api/lean/check", json={"lean": "theorem BROKEN : True := by sorry"})
        check(r.status_code == 200 and not r.json()["ok"], "broken statement -> 200 ok:false")
        r = client.post("/api/lean/check", json={"lean": "axiom bad : False\ntheorem t : True := by sorry"})
        check(any(x["code"] == "banned_axiom" for x in r.json()["rejections"]), "axiom rejected")

        print("\njob lifecycle (lean mode):")
        r = client.post("/api/jobs", json={"mode": "lean", "lean": "theorem foo : True := by sorry"})
        check(r.status_code == 201, f"POST /api/jobs -> 201 (got {r.status_code} {r.text[:120]})")
        job_id = r.json()["id"]
        final = wait_for(client, job_id)
        check(final["phase"] == "succeeded", f"job succeeded (got {final['phase']}: {final.get('error_message','')[:100]})")
        check(final["verdict"] == "proved", "verdict proved")
        check(final["iteration"] >= 3, f"iterations tailed (got {final['iteration']})")
        check(bool(final["result"] and final["result"].get("lean")), "result lean captured")
        check(final["safeverify"]["success"] is True, "safeverify report captured")
        check(any(e["event"] == "verify_result" for e in final["log_tail"]), "event log populated")

        print("\npolling protocol:")
        rev = final["revision"]
        r = client.get(f"/api/jobs/{job_id}?since={rev}")
        check(r.status_code == 304, f"since=<rev> -> 304 (got {r.status_code})")
        etag = client.get(f"/api/jobs/{job_id}").headers.get("etag")
        r = client.get(f"/api/jobs/{job_id}", headers={"If-None-Match": etag})
        check(r.status_code == 304, "If-None-Match -> 304")
        r = client.get(f"/api/jobs/{job_id}?fields=light")
        check("current_lean" not in r.json() and "lean_chars" in r.json(), "fields=light trims payload")

        print("\nartifacts & listing:")
        r = client.get(f"/api/jobs/{job_id}/artifact/result")
        check(r.status_code == 200 and "trivial" in r.text, "result artifact")
        r = client.get(f"/api/jobs/{job_id}/artifact/log")
        check(r.status_code == 200, "log artifact")
        r = client.get("/api/jobs")
        check(any(j["id"] == job_id for j in r.json()["jobs"]), "job listed for this IP")

        print("\nfailure paths:")
        os.environ["FAKE_OUTCOME"] = "crash"
        r = client.post("/api/jobs", json={"mode": "lean", "lean": "theorem c : True := by sorry"})
        crash_id = r.json()["id"]
        final = wait_for(client, crash_id)
        check(final["phase"] == "failed", f"crashing prover -> failed (got {final['phase']})")
        os.environ["FAKE_OUTCOME"] = "proved"

        print("\nnl mode:")
        r = client.post("/api/jobs", json={"mode": "nl", "lean": "theorem n : True := by sorry",
                                           "nl": "Show that True holds."})
        check(r.status_code == 201, f"nl job accepted (got {r.status_code} {r.text[:120]})")
        nl_id = r.json()["id"]
        final = wait_for(client, nl_id)
        check(final["phase"] == "succeeded", f"nl job succeeded (got {final['phase']})")
        check((Path(os.environ.get("RUNS_DIR", ROOT / "runs")) / nl_id / "problem.txt").exists(),
              "problem.txt written for nl mode")
        r = client.post("/api/jobs", json={"mode": "nl", "lean": "theorem n : True := by sorry"})
        check(r.status_code == 422, "nl mode without nl text -> 422")

        print("\nrate limiting:")
        # 3 jobs already consumed (lean, crash, nl). The 4th must be refused.
        r = client.post("/api/jobs", json={"mode": "lean", "lean": "theorem r : True := by sorry"})
        check(r.status_code == 429, f"4th job -> 429 (got {r.status_code})")
        body = r.json()["error"]
        check(body["code"] == "rate_limited", "429 envelope code")
        check(body["details"]["retry_after_seconds"] > 0, "retry_after present")
        check("Retry-After" in r.headers, "Retry-After header present")

        print("\ncancel + killpg:")
        os.environ["FAKE_OUTCOME"] = "hang"
        os.environ["FAKE_FORK"] = "1"
        appmod.limiter._hits.clear()
        r = client.post("/api/jobs", json={"mode": "lean", "lean": "theorem h : True := by sorry"})
        hang_id = r.json()["id"]
        for _ in range(40):
            if client.get(f"/api/jobs/{hang_id}").json()["phase"] == "proving":
                break
            time.sleep(0.25)
        pgid = store.get(hang_id).pgid
        client.post(f"/api/jobs/{hang_id}/cancel")
        final = wait_for(client, hang_id, limit=40)
        check(final["phase"] == "cancelled", f"cancel -> cancelled (got {final['phase']})")
        time.sleep(1)
        alive = os.system(f"pgrep -g {pgid} > /dev/null 2>&1") == 0
        check(not alive, f"process group {pgid} fully reaped (SIGTERM-ignoring child included)")
        os.environ["FAKE_FORK"] = "0"

        print("\ntimeout:")
        appmod.limiter._hits.clear()
        r = client.post("/api/jobs", json={"mode": "lean", "lean": "theorem t2 : True := by sorry"})
        to_id = r.json()["id"]
        final = wait_for(client, to_id, limit=60)
        check(final["phase"] == "timeout", f"hanging prover -> timeout (got {final['phase']})")
        os.environ["FAKE_OUTCOME"] = "proved"

        print("\nunknown job:")
        r = client.get("/api/jobs/job_deadbeef_0000")
        check(r.status_code == 404 and "restarted" in r.json()["error"]["message"],
              "404 explains in-memory loss")

    print(f"\n{'FAILED: ' + ', '.join(FAILURES) if FAILURES else 'all integration checks passed'}")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
