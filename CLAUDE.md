# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Two halves that share one Lake project:

1. **The prover engine** (`prover_subagent.py`, `whole_proof_subagent.py`, `verify.py`) — CLI tools
   where Gemini iteratively writes Lean 4 proofs, the Lean compiler supplies error feedback each
   turn via Pantograph, and SafeVerify gates the result against a reference `.olean`.
2. **The web service** (`server/`, `web/`) — a FastAPI API and a static GitHub Pages site that let
   anyone submit a problem in natural language or Lean and watch the prover work. The API drives the
   CLI tools as subprocesses; it does not import them.

Everything must run from this directory: it is the Lake root, and Pantograph, `lake`, and the
reference-`.olean` build all depend on that.

## Commands

```bash
# tests (no pytest; each file is a standalone script)
.venv/bin/python tests/test_units.py         # IP extraction + rate limiting, no Lean needed
.venv/bin/python tests/test_integration.py   # full API, stubbed prover and checker, ~1 min
.venv/bin/python tests/test_normalize.py     # normalizer fixtures against real Lean, ~2 min

# API + site locally
export CHECKER_POOL_SIZE=1 MAX_CONCURRENT_JOBS=1 PROVER_NUM_PROCS=1
.venv/bin/uvicorn server.app:app --port 8080 --forwarded-allow-ips=""
python3 -m http.server 5173 -d web

# prover CLI, unchanged from before the web service existed
.venv/bin/python prover_subagent.py Challenge.lean --libs Mathlib --num_procs 2
.venv/bin/python whole_proof_subagent.py problem.txt problem.lean --libs Mathlib

# Lean
lake exe cache get && lake build
lake build safe_verify        # -> SafeVerify/.lake/build/bin/safe_verify
```

`.venv` is Python 3.13. **`python3` on PATH is conda 3.8.5 and cannot run any of this** — always use
`.venv/bin/python`. `pantograph` is installed from a wheel built out of `PyPantograph/`, which is why
`requirements.txt` does not list it.

To exercise the whole system without spending Gemini quota or 20 minutes per attempt, point the
runner at the test double:

```bash
export PROVER_CMD="$PWD/.venv/bin/python $PWD/tests/fake_prover.py"
export PROVER_ENV_PASSTHROUGH=FAKE_OUTCOME,FAKE_FORK,FAKE_ROUNDS,FAKE_DELAY
export FAKE_OUTCOME=proved     # or unproved | crash | hang
```

## Architecture

### The two proving strategies

**`prover_subagent.py` — evolve-block editing.** The problem file is annotated with marker comments:

```
-- EVOLVE-BLOCK-START / -- EVOLVE-BLOCK-END
-- EVOLVE-VALUE-START / -- EVOLVE-VALUE-END
```

`list_evolve_blocks()` parses these into ordered `((line,col),(line,col))` regions. The model only
ever emits one tool call, `replace_block_content`, with `{block_id, new_code}` pairs indexed
top-to-bottom; `replace_block_by_id()` splices whole lines between the marker lines.

The distinctive mechanic is **block retirement** in `prover_step()`: after each compile, a block
whose region contains no `sorry` and no error span has its two marker comments overwritten with
spaces, removing it from the next `list_evolve_blocks()` call. The walk stops at the first block
still holding a `sorry` or an error. Block IDs therefore renumber every turn, which is why the
prompt tells the model to recount. When no blocks remain the session ends and verification runs.

**`whole_proof_subagent.py` — natural-language first.** Takes a `.txt` problem and a `.lean`
statement, and the `replace_schema` tool call returns both `nl_proof` and `lean_proof` each turn.
The whole file is replaced wholesale; no markers.

Both race `--num_procs` `multiprocessing.Process` workers via `run_until_first_success`.

### The server → script contract

The API never imports the prover. It writes a job directory, spawns the CLI, and reads events back.
All new behaviour is env-gated, so running the scripts by hand behaves exactly as it did before the
web service existed:

| Variable | Effect |
|---|---|
| `PROVER_NO_LAKE_PRELUDE=1` | skip `compile_lean_file`'s `lake clean`/`update`/`cache get`/`build` |
| `PROVER_REUSE_OLEAN=1` | reuse an existing `.olean` instead of rebuilding |
| `PROVER_STATUS_DIR` | append JSONL progress events (see `prover_events.py`) |
| `PROVER_RESULT_DIR` | write the verified proof as `result_w<pid>.json` |
| `PROVER_SCRATCH_DIR` | redirect the `<target>_<n>` dumps (`-` disables them) |
| `PROVER_WALL_SECONDS` | self-exit via a `threading.Timer` before the supervisor's hard kill |
| `PROVER_STRICT_EXIT=1` | make the process exit code reflect success |
| `PROVER_MODEL`, `PROVER_MAX_ITERS`, `PROVER_PROJECT_PATH` | overrides |
| `SAFEVERIFY_BIN`, `SAFEVERIFY_LEAN_CMD`, `SAFEVERIFY_SCRATCH_DIR`, `SAFEVERIFY_HEADER` | `verify.py` |

**The lake prelude opt-out is not optional for the server.** `compile_lean_file` runs `lake clean`
on every invocation; concurrent jobs sharing one Lake root would delete each other's build tree.

**One status file per worker, not per job.** `sketch` events carry whole Lean proofs, far larger
than `PIPE_BUF`, so appends from racing workers to a single file would interleave mid-line.

### Request path

`server/app.py` holds all routes. Notable pieces:

- `server/lean/checkers.py` — pool of pre-warmed `checker_worker.py` subprocesses, each holding one
  Pantograph server with Mathlib imported. They speak JSON lines over stdio. Used for every compile
  check; `check_compile_async` passes `inheritEnv: false` so calls don't contaminate each other.
- `server/lean/normalize.py` — turns arbitrary pasted Lean into something the prover can consume:
  strips user markers and imports, renames `example` (SafeVerify matches declarations *by name*, so
  an anonymous one makes the gate vacuous), injects EVOLVE markers around each `:= by` body, rejects
  `axiom`/`unsafe`/`native_decide`, then recompiles to confirm.
- `server/lean/olean.py` — builds the reference `.olean` with `lean` directly and a cached
  `LEAN_PATH`, never through `lake`, so concurrent jobs don't contend on the workspace lock.
- `server/jobs/runner.py` — spawns the CLI with `start_new_session=True` and kills via `os.killpg`.
- `server/jobs/statuslog.py` — tails the per-worker JSONL files into live job state.

## Things that will bite you

These are non-obvious and each one caused a real failure during development.

- **`lean` refuses input outside the root directory.** Job files live at `runs/<id>/target.lean`
  inside the Lake root for exactly this reason.
- **`CompilationUnit.i_begin`/`i_end` are byte offsets**, while `Message.pos.line/column` are Lean
  codepoint positions. Slice `code.encode("utf-8")`, never the `str` — Mathlib statements are full
  of `ℕ`/`∀`. (`prover_subagent.py`'s block retirement still compares character columns against
  codepoint columns; that is pre-existing and degrades proof quality, not safety.)
- **`sorry` is a warning, not an error.** "Compiles" means no ERROR-severity messages.
- **`autoImplicit` is on.** A typo'd identifier in a submitted statement silently becomes an
  auto-bound variable rather than an error, so the user gets a proof of a *different* theorem.
  SafeVerify will not catch this: it checks the proof against the statement as submitted.
- **Startup dominates short jobs.** ~60 s to build the reference `.olean` (it imports Mathlib) plus
  ~90–100 s per prover worker to import Mathlib again. A 20-minute budget buys perhaps 8–15 model
  iterations.
- **The result file is authoritative, the exit code is corroboration.** Too much of the success path
  in these scripts is implicit to bet a verdict on `$?`.
- **Child stdout must be a real file, never a `PIPE`.** The scripts print entire sketches and full
  model responses each turn; an undrained pipe deadlocks the job at the OS buffer limit.
- **`proc.terminate()` is wrong here.** The scripts fork `multiprocessing` children that each own a
  `pantograph-repl` holding Mathlib. Kill the process group, and give every long-lived Lean
  subprocess its own session so it can be reaped.
- **Run exactly one uvicorn worker.** Jobs, rate-limit counters and the checker pool are all
  in-process; a second worker halves the effective rate limit and hides half of each user's jobs.
- **Start uvicorn with `--forwarded-allow-ips=""` and without `--proxy-headers`**, or uvicorn
  rewrites `request.client` from `X-Forwarded-For` before `server/clientip.py` can decide whether
  that header is trustworthy — which is the whole rate-limit defence.
- **`MemoryDenyWriteExecute` must stay `no`** in the systemd unit: `safe_verify` is built with
  `supportInterpreter := true` and both it and `pantograph-repl` map executable pages.
- **SafeVerify only writes its JSON report when passed `--save`**, and enforces that the submission
  imports a superset of the target's imports — so both files need the same `import Mathlib` header.

## Working in this codebase

**The two prover entrypoints are near-duplicates.** `format_messages_to_string`,
`feedback_to_error_positions`, `compile_lean_file`, `LeanCompiler`, `LlmSketcher`, `ToolCall`,
`within_budget`, `worker_function`, `_arm_wall_clock` and `run_until_first_success` are copy-pasted
with small divergences. A fix to any of them almost certainly needs applying to both files.

**Trust model.** SafeVerify proves "this proof proves the statement that was submitted". It does not
judge whether the statement is a faithful formalization of what the user meant — which is why the
natural-language flow makes the user confirm the Lean before anything runs, and why the UI says so.

`.gitignore` covers `runs/`, `*-Submission-*` and the `<target>_<n>` scratch pattern. If you see
hundreds of stray `.lean` files at the repo root again, something is running without
`PROVER_SCRATCH_DIR` set.

See `deploy/README.md` for deployment and operational notes.
