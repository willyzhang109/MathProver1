"""MathProver HTTP API.

Single uvicorn worker by design: jobs, rate limits and the checker pool all
live in this process, so a second worker would silently halve the rate limit
and hide half the job list.

Must be started WITHOUT --proxy-headers and with --forwarded-allow-ips=""
so that uvicorn does not rewrite request.client from X-Forwarded-For before
server.clientip gets to decide whether that header is trustworthy.
"""

import asyncio
import contextlib
import logging
import time
from pathlib import Path

from fastapi import FastAPI, Request, Response
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, PlainTextResponse

from .clientip import bucket, client_ip
from .config import settings
from .ids import new_id
from .jobs.queue import queue
from .jobs.store import store
from .lean import normalize
from .lean.checkers import CheckerError, CheckerWarming, pool
from .llm.formalizer import FormalizerUnavailable, formalizer
from .models import CheckRequest, FormalizeRequest, JobRequest
from .ratelimit import limiter

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(name)s %(message)s")
log = logging.getLogger("api")


def fail(status: int, code: str, message: str, **details) -> JSONResponse:
    body = {"error": {"code": code, "message": message}}
    if details:
        body["error"]["details"] = details
    return JSONResponse(body, status_code=status)


class RateLimited(Exception):
    def __init__(self, decision, klass):
        self.decision = decision
        self.klass = klass


def caller(request: Request) -> str:
    peer = request.client.host if request.client else None
    return bucket(client_ip(peer, request.headers))


def enforce(request: Request, klass: str) -> str:
    key = caller(request)
    decision = limiter.check(key, klass)
    if not decision.allowed:
        raise RateLimited(decision, klass)
    return key


@contextlib.asynccontextmanager
async def lifespan(app: FastAPI):
    settings.runs_dir.mkdir(parents=True, exist_ok=True)
    pool.start_warmup()
    queue.start()
    janitor = asyncio.create_task(_janitor())
    log.info("api up: lake_root=%s runs=%s", settings.lake_root, settings.runs_dir)
    try:
        yield
    finally:
        janitor.cancel()
        with contextlib.suppress(asyncio.CancelledError):
            await janitor
        # Reap children before exiting, or systemd Restart=always orphans them.
        await queue.shutdown()
        await pool.stop()


async def _janitor() -> None:
    while True:
        await asyncio.sleep(300)
        with contextlib.suppress(Exception):
            dropped = store.prune()
            limiter.sweep()
            if dropped:
                log.info("janitor dropped %d job records", dropped)


app = FastAPI(title="MathProver API", lifespan=lifespan, docs_url=None, redoc_url=None)

app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.cors_origins,
    allow_credentials=False,
    allow_methods=["GET", "POST", "OPTIONS"],
    allow_headers=["Content-Type", "If-None-Match"],
    expose_headers=["ETag", "Retry-After", "X-RateLimit-Remaining", "X-RateLimit-Reset"],
)


@app.exception_handler(RateLimited)
async def _rate_limited(request: Request, exc: RateLimited):
    d = exc.decision
    minutes = max(1, round(d.retry_after_s / 60))
    response = fail(
        429, "rate_limited",
        f"Limit is {d.limit} {exc.klass} request(s) per hour. Try again in about {minutes} minute(s).",
        **{"class": exc.klass, "limit": d.limit, "window_seconds": settings.rate_window_s,
           "remaining": 0, "retry_after_seconds": d.retry_after_s, "reset_at": d.reset_at})
    response.headers["Retry-After"] = str(d.retry_after_s)
    response.headers["X-RateLimit-Limit"] = str(d.limit)
    response.headers["X-RateLimit-Remaining"] = "0"
    response.headers["X-RateLimit-Reset"] = str(int(d.reset_at))
    return response


# --------------------------------------------------------------------------
# health and limits
# --------------------------------------------------------------------------
@app.get("/api/health")
async def health():
    return {
        "ok": True,
        "checkers_ready": pool.ready_count,
        "checkers_total": pool.size,
        "queue_depth": queue.depth,
        "jobs_running": queue.running_count,
        "max_concurrent_jobs": settings.max_concurrent_jobs,
    }


@app.get("/api/limits")
async def limits(request: Request):
    key = caller(request)
    out = {}
    for klass in ("job", "formalize", "check"):
        d = limiter.peek(key, klass)
        out[klass] = {"limit": d.limit, "remaining": d.remaining,
                      "retry_after_seconds": d.retry_after_s, "reset_at": d.reset_at}
    return out


# --------------------------------------------------------------------------
# formalize / check
# --------------------------------------------------------------------------
@app.post("/api/formalize")
async def formalize(request: Request, body: FormalizeRequest):
    enforce(request, "formalize")

    try:
        async with pool.acquire() as checker:
            result = await formalizer.formalize(body.nl, checker)
    except CheckerWarming as exc:
        return fail(503, "checker_warming", str(exc))
    except FormalizerUnavailable as exc:
        return fail(503, "llm_unavailable", str(exc))
    except CheckerError as exc:
        return fail(503, "checker_error", str(exc))

    return {
        "draft_id": new_id("drf"),
        "nl": body.nl,
        "lean": result.lean,
        "informal_restatement": result.restatement,
        "compiles": result.compiles,
        "repaired": result.repaired,
        "errors": result.errors,
        "warnings": result.warnings,
        "model": settings.formalizer_model,
    }


async def _prepare(lean: str, mode: str):
    async with pool.acquire() as checker:
        return await normalize.prepare(lean, mode, checker)


@app.post("/api/lean/check")
async def lean_check(request: Request, body: CheckRequest):
    enforce(request, "check")

    try:
        prepared = await _prepare(body.lean, "lean")
    except CheckerWarming as exc:
        return fail(503, "checker_warming", str(exc))
    except CheckerError as exc:
        return fail(503, "checker_error", str(exc))

    # A statement that fails to compile is a valid request with a negative
    # answer, not a client error -- 200 keeps the edit loop simple.
    return prepared.as_dict()


# --------------------------------------------------------------------------
# jobs
# --------------------------------------------------------------------------
@app.post("/api/jobs", status_code=201)
async def create_job(request: Request, body: JobRequest):
    key = caller(request)

    if body.mode == "nl" and not (body.nl or "").strip():
        return fail(422, "missing_nl",
                    "Natural-language mode requires the original problem text.")

    active = store.active_for_bucket(key)
    running = [j for j in active if j.phase != "queued"]
    if len(running) >= settings.per_ip_running or len(active) >= settings.per_ip_running + settings.per_ip_queued:
        return fail(429, "too_many_active",
                    "You already have a job in progress. Wait for it to finish or cancel it.")

    if queue.full():
        return fail(503, "queue_full", "The queue is full. Please try again shortly.")

    # Re-normalize server-side: a prior /check call is never trusted.
    try:
        prepared = await _prepare(body.lean, body.mode)
    except CheckerWarming as exc:
        return fail(503, "checker_warming", str(exc))
    except CheckerError as exc:
        return fail(503, "checker_error", str(exc))

    if prepared.rejections:
        first = prepared.rejections[0]
        status = 409 if first.code == "already_complete" else 400
        return fail(status, first.code, first.message,
                    reasons=[r.as_dict() for r in prepared.rejections])
    if not prepared.ok:
        return fail(400, "compile_error",
                    "The statement does not compile. Fix the errors and resubmit.",
                    errors=prepared.errors)

    enforce(request, "job")   # only charged once the submission is known good
    if not limiter.check_global_daily():
        return fail(503, "service_quota_exhausted",
                    "The service has hit its daily job cap. Please try again tomorrow.")

    title = prepared.declarations[0].name if prepared.declarations else "statement"
    job = store.create(
        mode=body.mode, ip_bucket=key, title=title,
        user_lean=body.lean, user_nl=(body.nl or ""),
        normalized_lean=prepared.normalized_lean,
        blocks_total=prepared.blocks,
    )

    try:
        await queue.submit(job)
    except asyncio.QueueFull:
        job.set_phase("failed", "error", "The queue is full.")
        return fail(503, "queue_full", "The queue is full. Please try again shortly.")

    payload = job.detail(queue_position=queue.position(job.id))
    payload["poll_url"] = f"/api/jobs/{job.id}"
    return payload


@app.get("/api/jobs")
async def list_jobs(request: Request):
    key = enforce(request, "read")
    jobs = store.for_bucket(key)
    return {"bucket": key, "total": len(jobs), "jobs": [j.summary() for j in jobs]}


@app.get("/api/jobs/{job_id}")
async def get_job(job_id: str, request: Request, response: Response,
                  since: int = 0, fields: str = "full"):
    enforce(request, "read")
    job = store.get(job_id)
    if job is None:
        return fail(404, "job_unknown",
                    "This job is no longer available. The server may have restarted, "
                    "or the job may have aged out.")

    etag = f'W/"{job.revision}"'
    if since and job.revision <= since:
        return Response(status_code=304, headers={"ETag": etag})
    if request.headers.get("if-none-match") == etag:
        return Response(status_code=304, headers={"ETag": etag})

    response.headers["ETag"] = etag
    response.headers["Cache-Control"] = "no-store"
    return job.detail(queue_position=queue.position(job.id), light=(fields == "light"))


@app.post("/api/jobs/{job_id}/cancel", status_code=202)
async def cancel_job(job_id: str, request: Request):
    job = store.get(job_id)
    if job is None:
        return fail(404, "job_unknown", "This job is no longer available.")
    if not job.active:
        return {"id": job.id, "phase": job.phase}
    await queue.cancel(job)
    return {"id": job.id, "phase": job.phase}


ARTIFACTS = {
    "lean": "current_lean",
    "nl": "current_nl",
    "target": "normalized_lean",
}


@app.get("/api/jobs/{job_id}/artifact/{kind}")
async def artifact(job_id: str, kind: str, request: Request):
    enforce(request, "read")
    job = store.get(job_id)
    if job is None:
        return fail(404, "job_unknown", "This job is no longer available.")

    if kind in ARTIFACTS:
        return PlainTextResponse(getattr(job, ARTIFACTS[kind]) or "")
    if kind == "result":
        return PlainTextResponse((job.result or {}).get("lean", ""))
    if kind == "log":
        path = Path(settings.runs_dir) / job.id / "stdout.log"
        if not path.exists():
            return fail(404, "no_artifact", "No log for this job.")
        data = path.read_bytes()[-262144:]
        return PlainTextResponse(data.decode("utf-8", "replace"))
    return fail(404, "no_artifact", f"Unknown artifact {kind!r}.")
