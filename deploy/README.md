# Deploying MathProver

Two halves: a static site on GitHub Pages, and an API on a VM that has Lean,
Mathlib and `safe_verify`. Pages cannot run Lean, which is why the split exists.

## Prerequisites that are easy to miss

- **A domain name is mandatory.** The Pages site is HTTPS, so a plain-HTTP or
  bare-IP API is blocked by the browser as mixed content, and Let's Encrypt will
  not issue for an IP.
- **`safe_verify` has never been built in this repo.** `lake build safe_verify`
  is the long pole on a fresh machine and everything downstream depends on it.
- **Rotate the Gemini key.** The old one was hardcoded in the prover scripts and
  is in this repository's git history. Removing it from the working tree does
  not remove it from `git log`.

## VM

```bash
sudo DOMAIN=api.yourdomain.com bash deploy/provision.sh
```

Then edit `/etc/mathprover/server.env` (fresh key) and
`systemctl restart mathprover-api`.

Sizing: budget for `MAX_CONCURRENT_JOBS * PROVER_NUM_PROCS + CHECKER_POOL_SIZE`
processes that each hold Mathlib in memory. Step 9 of the provisioner measures
one so you can multiply rather than guess. Disk: 80 GB or more.

## Pages

Set the repository variable `API_BASE_URL` (Settings → Secrets and variables →
Actions → Variables) to your API origin, then run the **Deploy site to Pages**
workflow. It writes `web/config.js` at deploy time so the URL is not committed.

## Running it locally

```bash
# terminal 1 - API
export GEMINI_API_KEY=...            # omit to test everything except /api/formalize
export CHECKER_POOL_SIZE=1 MAX_CONCURRENT_JOBS=1 PROVER_NUM_PROCS=1
export CORS_ORIGINS=http://localhost:5173
.venv/bin/uvicorn server.app:app --port 8080 --forwarded-allow-ips=""

# terminal 2 - site
python3 -m http.server 5173 -d web   # config.js already points at 127.0.0.1:8080
```

The checker pool imports Mathlib on startup (~100 s per checker, warmed in
parallel). `/api/health` reports `checkers_ready`; until it is non-zero,
`/api/lean/check` returns 503 `checker_warming`.

To exercise the whole system without spending Gemini quota or 20 minutes per
attempt, point the runner at the test double:

```bash
export PROVER_CMD="$PWD/.venv/bin/python $PWD/tests/fake_prover.py"
export PROVER_ENV_PASSTHROUGH=FAKE_OUTCOME,FAKE_FORK,FAKE_ROUNDS,FAKE_DELAY
export FAKE_OUTCOME=proved       # or unproved | crash | hang
```

## Tests

```bash
.venv/bin/python tests/test_units.py        # IP extraction + rate limiting, no Lean
.venv/bin/python tests/test_integration.py  # full API, stubbed prover and checker
.venv/bin/python tests/test_normalize.py    # normalizer fixtures against real Lean (~2 min)
```

## Operational notes

- **State is in memory.** A restart drops every running job and everyone's
  rate-limit history. The shutdown hook kills child process groups first so no
  orphaned `pantograph-repl` processes survive; the API answers 404 with an
  explicit "the server may have restarted" message.
- **Startup cost per job is real:** roughly 60 s to compile the reference
  `.olean` (it imports Mathlib), then ~100 s for each prover worker to import
  Mathlib again. Out of a 20-minute budget that leaves time for perhaps 8-15
  model iterations. The UI names these phases so they do not look like a hang.
- **Trust boundary.** SafeVerify proves "this proof proves the statement that
  was submitted". It does not judge whether the statement is a faithful
  formalization of what the user meant — which is exactly why the natural
  language flow makes the user confirm the Lean before anything runs.
