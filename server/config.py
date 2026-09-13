"""Runtime configuration, entirely environment-driven.

Deliberately plain os.environ rather than pydantic-settings: it keeps the
dependency footprint to fastapi + uvicorn on top of what the venv already has.
"""

import os
import shlex
from dataclasses import dataclass, field
from pathlib import Path


def _env(name: str, default: str = "") -> str:
    return os.environ.get(name, default)


def _int(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, "") or default)
    except ValueError:
        return default


def _list(name: str, default: str = "") -> list:
    raw = os.environ.get(name, default)
    return [item.strip() for item in raw.split(",") if item.strip()]


REPO_ROOT = Path(__file__).resolve().parent.parent


@dataclass
class Settings:
    # --- filesystem -------------------------------------------------------
    lake_root: Path = field(default_factory=lambda: Path(_env("LAKE_ROOT") or REPO_ROOT))
    runs_dir: Path = field(default_factory=lambda: Path(_env("RUNS_DIR") or (REPO_ROOT / "runs")))
    python_bin: str = field(default_factory=lambda: _env("PROVER_PYTHON") or str(REPO_ROOT / ".venv/bin/python"))

    # --- prover -----------------------------------------------------------
    prover_cmd: list = field(default_factory=lambda: shlex.split(_env("PROVER_CMD", "")))
    num_procs: int = field(default_factory=lambda: _int("PROVER_NUM_PROCS", 2))
    token_limit: int = field(default_factory=lambda: _int("PROVER_TOKEN_LIMIT", 200000))
    max_iters: int = field(default_factory=lambda: _int("PROVER_MAX_ITERS", 0))
    job_timeout_s: int = field(default_factory=lambda: _int("JOB_TIMEOUT_SECONDS", 1200))
    libs: list = field(default_factory=lambda: _list("PROVER_LIBS", "Mathlib"))
    model: str = field(default_factory=lambda: _env("PROVER_MODEL"))
    # Extra environment variable names to forward into prover children. The
    # child env is an explicit allowlist, so anything site-specific (LEAN_CC,
    # proxy settings, test hooks) has to be named here.
    env_passthrough: list = field(default_factory=lambda: _list("PROVER_ENV_PASSTHROUGH"))

    # --- concurrency ------------------------------------------------------
    max_concurrent_jobs: int = field(default_factory=lambda: _int("MAX_CONCURRENT_JOBS", 5))
    max_queue: int = field(default_factory=lambda: _int("MAX_QUEUE", 50))
    per_ip_running: int = field(default_factory=lambda: _int("PER_IP_RUNNING", 1))
    per_ip_queued: int = field(default_factory=lambda: _int("PER_IP_QUEUED", 2))

    # --- checker pool -----------------------------------------------------
    checker_pool_size: int = field(default_factory=lambda: _int("CHECKER_POOL_SIZE", 3))
    checker_timeout_s: int = field(default_factory=lambda: _int("CHECKER_TIMEOUT_SECONDS", 180))
    checker_imports: list = field(default_factory=lambda: _list("CHECKER_IMPORTS", "Init,Mathlib"))

    # --- llm --------------------------------------------------------------
    gemini_api_key: str = field(default_factory=lambda: _env("GEMINI_API_KEY") or _env("GOOGLE_API_KEY"))
    formalizer_model: str = field(default_factory=lambda: _env("FORMALIZER_MODEL", "gemini-3.6-flash"))
    formalizer_timeout_s: int = field(default_factory=lambda: _int("FORMALIZER_TIMEOUT_SECONDS", 90))

    # --- http -------------------------------------------------------------
    cors_origins: list = field(default_factory=lambda: _list(
        "CORS_ORIGINS", "https://willyzhang109.github.io,http://localhost:8000,http://127.0.0.1:8000"))
    trusted_proxies: list = field(default_factory=lambda: _list(
        "TRUSTED_PROXIES", "127.0.0.1/32,::1/128"))
    trust_x_real_ip: bool = field(default_factory=lambda: _env("TRUST_X_REAL_IP") == "1")

    # --- limits -----------------------------------------------------------
    limit_job: int = field(default_factory=lambda: _int("RATE_LIMIT_JOB", 3))
    limit_formalize: int = field(default_factory=lambda: _int("RATE_LIMIT_FORMALIZE", 10))
    limit_check: int = field(default_factory=lambda: _int("RATE_LIMIT_CHECK", 20))
    limit_read: int = field(default_factory=lambda: _int("RATE_LIMIT_READ", 600))
    rate_window_s: int = field(default_factory=lambda: _int("RATE_WINDOW_SECONDS", 3600))
    max_jobs_per_day: int = field(default_factory=lambda: _int("MAX_JOBS_PER_DAY", 60))

    # --- retention --------------------------------------------------------
    job_retention_s: int = field(default_factory=lambda: _int("JOB_RETENTION_SECONDS", 86400))
    max_jobs_kept: int = field(default_factory=lambda: _int("MAX_JOBS_KEPT", 300))

    # --- input caps -------------------------------------------------------
    max_nl_chars: int = field(default_factory=lambda: _int("MAX_NL_CHARS", 8000))
    max_lean_chars: int = field(default_factory=lambda: _int("MAX_LEAN_CHARS", 20000))

    def script_path(self, name: str) -> str:
        return str(self.lake_root / name)


settings = Settings()
