# MathProver API image.
#
# Large by nature: Mathlib's oleans are ~5-10 GB and are baked in so the
# container boots without network fetches. Expect a 12-18 GB image.
#
# Layer order is deliberate: the Lean toolchain and Mathlib are built before any
# application code is copied, so editing server/ or web/ does not rebuild
# Mathlib.

FROM python:3.13-slim-bookworm

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates git build-essential procps \
    && rm -rf /var/lib/apt/lists/*

# Unprivileged runtime account. Untrusted Lean executes at elaboration time, so
# nothing here should ever run as root.
RUN useradd --create-home --home-dir /srv/mathprover --shell /bin/bash --uid 1000 prover \
 && install -d -o prover -g prover /srv/mathprover/app

# NOTE: the app directory is created above, as root, with explicit ownership.
# A bare WORKDIR would create it owned by root even with USER already set,
# and every later `lake` write would fail with EACCES.
USER prover
ENV HOME=/srv/mathprover \
    PATH=/srv/mathprover/.elan/bin:/srv/mathprover/app/.venv/bin:/usr/local/bin:/usr/bin:/bin \
    PYTHONUNBUFFERED=1

WORKDIR /srv/mathprover/app

# --- Lean toolchain ---------------------------------------------------------
COPY --chown=prover:prover lean-toolchain ./
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none \
 && lake --version

# --- git, for Lake's dependency fetching ------------------------------------
# Lake reports only "external command 'git' exited with code 128" and discards
# git's stderr, so probe the clone explicitly: if git is going to fail, we want
# its actual message rather than an exit code.
# GIT_TERMINAL_PROMPT=0 turns a credential prompt into an immediate, legible
# failure instead of a hang.
ENV GIT_TERMINAL_PROMPT=0
RUN git config --global advice.detachedHead false \
 && git config --global --add safe.directory '*' \
 && git clone --depth 1 https://github.com/leanprover/lean4-cli.git /tmp/git-probe \
 && rm -rf /tmp/git-probe \
 && echo "git connectivity OK"

# --- Mathlib + safe_verify (the expensive layer) ----------------------------
COPY --chown=prover:prover lakefile.toml lake-manifest.json ./
COPY --chown=prover:prover SafeVerify ./SafeVerify
COPY --chown=prover:prover PyPantograph ./PyPantograph

# Split so a failure names the command that caused it.
RUN lake exe cache get
RUN lake build safe_verify \
 && test -x SafeVerify/.lake/build/bin/safe_verify

# --- Python environment -----------------------------------------------------
# The venv must live at $REPO_ROOT/.venv: server/config.py derives python_bin
# from it, and that is the interpreter used to spawn prover subprocesses.
COPY --chown=prover:prover requirements.txt requirements-server.txt ./
RUN python3 -m venv .venv \
 && .venv/bin/pip install --no-cache-dir --upgrade pip uv \
 && mkdir -p dist \
 && (cd PyPantograph && ../.venv/bin/uv build --wheel --out-dir ../dist) \
 && .venv/bin/pip install --no-cache-dir "$(find ./dist -name '*.whl' | head -1)" \
 && .venv/bin/pip install --no-cache-dir -r requirements.txt -r requirements-server.txt \
 && rm -rf dist

# --- Application ------------------------------------------------------------
COPY --chown=prover:prover *.py ./
COPY --chown=prover:prover server ./server
COPY --chown=prover:prover tests ./tests
# compose.yaml / Caddyfile ship in the image so the VM startup script can
# extract them instead of needing a repo checkout on the host.
COPY --chown=prover:prover deploy ./deploy
RUN mkdir -p runs

ENV SAFEVERIFY_BIN=/srv/mathprover/app/SafeVerify/.lake/build/bin/safe_verify \
    SAFEVERIFY_LEAN_CMD=lean

EXPOSE 8080

HEALTHCHECK --interval=30s --timeout=5s --start-period=300s --retries=3 \
  CMD python3 -c "import urllib.request;urllib.request.urlopen('http://127.0.0.1:8080/api/health',timeout=4)"

# One worker only: jobs, rate-limit counters and the checker pool are all
# in-process state. --forwarded-allow-ips="" keeps uvicorn from rewriting
# request.client before server/clientip.py can vet X-Forwarded-For.
CMD [".venv/bin/uvicorn", "server.app:app", \
     "--host", "0.0.0.0", "--port", "8080", "--workers", "1", \
     "--forwarded-allow-ips=", "--no-access-log"]
