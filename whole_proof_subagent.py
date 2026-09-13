# Main Loop
import argparse
import asyncio
import bisect
import subprocess
import os
import pantograph
import random
import re
import sys
import threading
import time
from diff_match_patch import diff_match_patch
from google import genai
from google.genai import errors, types
from multiprocessing import Process, Queue
from pathlib import Path
from pantograph.server import Server
from prover_events import emit, errors_payload, truncate, write_result
from verify import SafeVerifyRunner

# The API key must come from the environment. Never print it: the server
# captures this process's stdout to a log file on disk.
if "GEMINI_API_KEY" not in os.environ and "GOOGLE_API_KEY" not in os.environ:
    raise SystemExit(
        "No Gemini credentials found. Set GEMINI_API_KEY (or GOOGLE_API_KEY) before running."
    )
os.environ.setdefault("GOOGLE_API_KEY", os.environ.get("GEMINI_API_KEY", ""))
os.environ.setdefault("GEMINI_API_KEY", os.environ.get("GOOGLE_API_KEY", ""))

lean_compiler = None
server = None
library_imports = None
nl_problem = ""
lean_problem = ""
nl_sketch = ""
lean_sketch = ""
target_lean_path = None
target_olean_path = None
temp_proof_count = 0

initial_prompt = """
# 1. Role and Goal
You are a world-class mathematician and expert.
Your goal is to solve hard mathematical problems by devising a proof strategy
and writing out a natural language proof as those in a math textbook.

# 2. Your Task
You will be given a math problem containing an unproven natural language statement along with a proof sketch in Lean 4. Your goal is to
prove the statement, and then translate the proof into Lean faithfully.

As feedback, you will be given the Lean compiler messages after each iteration, and you must fix any errors and replace
any sorrys. However, before doing so, check that the natural language proof is correct first.

Think like a mathematician: focus on the key insights, proof structure, and
creative steps (e.g., constructing an object via 'let').
If you get stuck on the main proof, try to gain insights by exploring diverse ideas:
study specific cases, or define and attempt to prove interesting generalizations,
specializations, or variants of the problem statement as new helper lemmas.
Prefer clever mathematical arguments over brute-force casework where possible.

Some of these problems are very hard, possibly even open problems in mathematics.
But don't be discouraged: approach them with curiosity and persistence.
Like George Dantzig, who solved two famous unsolved problems in statistics thinking they were homework,
you might solve a problem you think is difficult simply by not knowing it was considered impossible!
Believe in your ability to find creative solutions where others might not.

CRITICAL: You MUST use tools available to you exhaustively to refine your proof
until you either find a proof or are certain the current direction is flawed.
Do NOT give up easily, and NEVER put off work to the next session if you have more tool calls available.
Your effort in each turn must be maximal: try to solve the problem in full, as if there is no next session or tool call.

**No Imports:** The execution environment imports 'Mathlib' by default.
Do **not** add any 'import' statements in your Lean proof.

This is the original problem statement to be solved in natural language:
{nl_problem_statement}

This is the original unproven Lean statement of the same problem:
{lean_problem_statement}
"""

iter_prompt = """
First, double check that the natural language proof is correct.

If needed, rewrite the natural language proof first and make sure that it is correct; then, translate it into Lean 4 faithfully.

Here is the natural language proof from the previous iteration:
{nl_proof}

Here is the Lean translation from the previous iteration:
{lean_proof}

Here is the feedback for the Lean translation:
{feedback}
"""

async def start_server():
    global server
    project_path = os.environ.get("PROVER_PROJECT_PATH", ".")
    started = time.time()
    server = await pantograph.Server.create(project_path=project_path, imports=library_imports)
    emit("server_ready", imports=library_imports, startup_s=round(time.time() - started, 1))

def format_messages_to_string(units) -> str:
    """
    Converts compilation unit messages into a single formatted string.
    """
    output = ["Lean compiler error messages:"]
    
    for i, unit in enumerate(units):
        # Skip units that don't have any messages
        if not unit.messages:
            continue
            
        output.append(f"--- Messages for Compilation Unit {i + 1} ---")
        for msg in unit.messages:
            # Safely extract position if it exists
            pos_str = f"Line {msg.pos.line}, Col {msg.pos.column}" if hasattr(msg, 'pos') and msg.pos else "Unknown Position"
            pos_end_str = f" - Line {msg.pos_end.line}, Col {msg.pos_end.column}" if hasattr(msg, 'pos_end') and msg.pos_end else ""

            # Format the individual message entry
            severity = msg.severity.name.upper() if hasattr(msg.severity, 'name') else str(msg.severity).upper()
            text = getattr(msg, 'data', '') or getattr(msg, 'text', '')
            
            output.append(f"[{severity}] {pos_str + pos_end_str}: {text}")
            
    # Join everything with newlines, or return a success message if empty
    return "\n".join(output) if output else "No compile messages or errors found."

def feedback_to_error_positions(units):
    list_error_positions = []

    for i, unit in enumerate(units):
        # Skip units that don't have any messages
        if not unit.messages:
            continue
            
        for msg in unit.messages:
            # Safely extract position if it exists
            severity = msg.severity.name.upper() if hasattr(msg.severity, 'name') else str(msg.severity).upper()
            if severity == "ERROR":
                pos = (msg.pos.line, msg.pos.column) if hasattr(msg, 'pos') and msg.pos else None
                pos_end = (msg.pos_end.line, msg.pos_end.column) if hasattr(msg, 'pos_end') and msg.pos_end else None

                if pos:
                    if pos_end:
                        list_error_positions.append((pos, pos_end))
                    else:
                        list_error_positions.append((pos, pos))


    return list_error_positions

async def prover_subagent(initial_sketch):
    global nl_sketch, lean_sketch, target_olean_path, tokens_used
    print(f"Process {os.getpid()}.")

    lean_sketch = initial_sketch
    lean_session = LlmSketcher()
    max_iters = int(os.environ.get("PROVER_MAX_ITERS", "0")) or None
    iteration = 0

    while (tool_call := lean_session.recv()) and within_budget():
        print("Generating new natural language proof")

        feedback = ""
        iteration += 1
        emit("iteration", n=iteration, tokens_used=tokens_used, max_tokens=max_tokens)
        if max_iters and iteration > max_iters:
            print(f"Reached PROVER_MAX_ITERS={max_iters}; stopping.")
            break

        if tool_call.is_valid():
            nl_sketch = tool_call.response.function_calls[0].args["nl_proof"]
            lean_sketch = tool_call.response.function_calls[0].args["lean_proof"]

            lean_sketch_lines = lean_sketch.splitlines()
            i = 0

            while i < len(lean_sketch_lines) and lean_sketch_lines[i].startswith("import"):
                i += 1
            
            lean_sketch_lines = lean_sketch_lines[i:]

            compile_started = time.time()
            feedback = await server.check_compile_async("\n".join(lean_sketch_lines), read_header=False)
            feedback_errors = feedback_to_error_positions(feedback)

            all_messages = [m for unit in feedback for m in (unit.messages or [])]
            emit("sketch", lean=truncate(lean_sketch, 200_000), nl=truncate(nl_sketch),
                 chars=len(lean_sketch))
            emit("compile",
                 duration_s=round(time.time() - compile_started, 2),
                 n_errors=len(feedback_errors),
                 errors=errors_payload(all_messages))

            if len(feedback_errors) == 0 and "sorry" not in lean_sketch:
                emit("verify_start")
                if target_olean_path and lean_compiler.verify_integrity(lean_sketch):
                    path = write_result({
                        "success": True,
                        "lean": lean_sketch,
                        "nl": nl_sketch,
                        "worker_pid": os.getpid(),
                    })
                    emit("proof_found", path=path, chars=len(lean_sketch))
                    return nl_sketch, lean_sketch
                else:
                    lean_session.send("Proof compiled but failed to verify: hacks were found")
            else:
                lean_session.send(format_messages_to_string(feedback))
        else:
            print(f"Failure this iteration: {tool_call.response}")
            emit("llm_error", message="model returned no usable tool call")
            time.sleep(30)

    return None, None

# Todo lean_compiler, LlmSketcher, search & replace funcs, send feedback, verify_integrity, within_budget, contains_sorry
# lean_compiler instance of class

def compile_lean_file(lean_file_path: str, project_root: str = None) -> bool:
    """
    Compiles a .lean file into an .olean file using Lake.
    
    :param lean_file_path: Path to the .lean file you want to compile.
    :param project_root: The root directory containing 'lakefile.lean'. 
                        If None, defaults to the current working directory.
    :return: Path object to the compiled .olean file if successful, None otherwise.
    """

    lean_path = Path(lean_file_path).resolve()
    cwd_path = Path(project_root).resolve() if project_root else Path.cwd()

    # The server pre-builds the reference .olean and shares one Lake root across
    # concurrent jobs, where `lake clean` would delete other jobs' build trees.
    if os.environ.get("PROVER_REUSE_OLEAN") == "1":
        existing = lean_path.with_suffix('.olean')
        if existing.exists():
            print(f"Reusing existing olean: {existing}")
            return existing

    skip_prelude = os.environ.get("PROVER_NO_LAKE_PRELUDE") == "1"

    lake_clean_command = ["lake", "clean"]
    lake_update_command = ["lake", "update"]
    lake_cache_get_command = ["lake", "exe", "cache", "get"]
    lake_build_command = ["lake", "build"]

    try:
        if not skip_prelude:
            subprocess.run(
                lake_clean_command,
                cwd=cwd_path,
                capture_output=True,
                text=True,
                check=True
            )

            subprocess.run(
                lake_update_command,
                cwd=cwd_path,
                capture_output=True,
                text=True,
                check=True
            )

            subprocess.run(
                lake_cache_get_command,
                cwd=cwd_path,
                capture_output=True,
                text=True,
                check=True
            )

            subprocess.run(
                lake_build_command,
                cwd=cwd_path,
                capture_output=True,
                text=True,
                check=True
            )
    except subprocess.CalledProcessError as err:
        print(f"Lake Build failed with exit code {err.returncode}")
        print("\n--- Lake Error Output ---")
        print(err.stderr)
        print("----------------------------------")
        return None
    
    # 1. Determine the expected target .olean path
    olean_path = lean_path.with_suffix('.olean')
    
    # 2. Clear out any stale .olean file to prevent caching bugs
    if olean_path.exists():
        olean_path.unlink()
        
    # 3. Construct the Lake command
    command = ["lake", "env", "lean", "-o", olean_path, str(lean_path)]
    
    print(f"Compiling: {lean_path.name}...")
    
    try:
        # 4. Run the compilation
        subprocess.run(
            command,
            cwd=cwd_path,
            capture_output=True,
            text=True,
            check=True
        )
        
        # 5. Verify the file was actually created and return its path
        if olean_path.exists():
            print(f"Compiled successfully: {olean_path}")
            return olean_path
        else:
            print("Command exited 0, but the .olean file was not found.")
            return None
        
    except subprocess.CalledProcessError as e:
        print(f"Compilation failed with exit code {e.returncode}")
        print("\n--- Lean Compiler Error Output ---")
        print(e.stderr)
        print("----------------------------------")
        return None

class LeanCompiler:
    def __init__(self):
        self.checker = SafeVerifyRunner()

    def check(self, file):
        global lean_problem
        with open(file, 'r', encoding='utf-8') as f:
            lean_problem = f.read()
            return lean_problem
            # should we decode as utf-8?

    def verify_integrity(self, sketch):
        result = self.checker.verify_sketch(target_olean_path, lean_sketch)
        return result["success"]

replace_schema = types.FunctionDeclaration(
    name="replace_schema",
    description="The natural-language proof for the initial natural-language problem provided",
    parameters={
        "type": "OBJECT",
        "properties": {
            "nl_proof": {
                "type": "STRING",
                "description": "The natural language proof for the original problem."
            },
            "lean_proof": {
                "type": "STRING",
                "description": "The Lean 4 proof for the original problem."
            }
        },
        "required": ["nl_proof", "lean_proof"]
    }
)

tools = types.Tool(function_declarations=[replace_schema])
class LlmSketcher:
    def __init__(self):
        global max_tokens, tokens_used, tools, initial_prompt

        # check API key set
        # Format once: the template was previously passed to system_instruction
        # unformatted, so the model saw a literal "{nl_problem_statement}".
        system_prompt = initial_prompt.format(
            nl_problem_statement=nl_problem, lean_problem_statement=lean_problem)
        self.client = genai.Client()
        self.chat = self.client.chats.create(
            model=os.environ.get("PROVER_MODEL", "gemini-3.7-flash"),
            config=types.GenerateContentConfig(
                system_instruction=system_prompt,
                tools=[tools],
                tool_config=types.ToolConfig(
                    function_calling_config=types.FunctionCallingConfig(
                        mode="ANY",
                        allowed_function_names=["replace_schema"]
                    )
                ),
                temperature=0.5,
                thinking_config=types.ThinkingConfig(
                    thinking_level=types.ThinkingLevel.HIGH
                )
            )
        )
        self.last_response = self.chat.send_message(system_prompt)
        # print(self.last_response)

    def send(self, feedback):
        global temp_proof_count, tokens_used

        # Charge the budget. Without this within_budget() is permanently true
        # and the only thing that stops the loop is an external kill.
        tokens_used += len(str(feedback))

        scratch_dir = os.environ.get("PROVER_SCRATCH_DIR")
        if scratch_dir == "-":
            temp_lean_path = temp_nl_path = None
        elif scratch_dir:
            os.makedirs(scratch_dir, exist_ok=True)
            stem = os.path.join(scratch_dir, f"w{os.getpid()}_{temp_proof_count}")
            temp_lean_path, temp_nl_path = stem + ".lean", stem + ".txt"
        else:
            stem = target_olean_path.removesuffix('.olean') + "_" + str(temp_proof_count)
            temp_lean_path, temp_nl_path = stem + ".lean", stem + ".txt"
        temp_proof_count += 1
        if temp_lean_path:
            with open(temp_lean_path, "w") as temp_sketch_file:
                temp_sketch_file.write(f"""Sketch:
                                    {lean_sketch}

                                    Feedback:
                                    {feedback}
                                    """)

            with open(temp_nl_path, "w") as temp_sketch_file:
                temp_sketch_file.write(f"""Sketch:
                                        {nl_sketch}
                                        """)
        
        started = time.time()
        emit("llm_request", prompt_chars=len(str(feedback)))
        try:
            self.last_response = self.chat.send_message(iter_prompt.format(nl_proof=nl_sketch, lean_proof=lean_sketch, feedback=feedback))
            emit("llm_response", latency_s=round(time.time() - started, 2))
        except errors.APIError as err:
            print(err)
            self.last_response = None
            emit("llm_error", code=getattr(err, "code", None), message=str(err)[:500])
            if err.code == 400 or "400" in str(err):
                history = self.chat.get_history()
                total_messages = len(history)

                drop_count = int(total_messages * 0.5)
                drop_count += (drop_count % 2)
                self.chat._history = history[drop_count:]
                try:
                    self.last_response = self.chat.send_message(iter_prompt.format(nl_proof=nl_sketch, lean_proof=lean_sketch, feedback=feedback))
                except errors.APIError as retry_err:
                    print(f"Retry after history trim also failed: {retry_err}")
                    emit("llm_error", code=getattr(retry_err, "code", None),
                         message=str(retry_err)[:500], retried=True)
                    self.last_response = None

    def recv(self):
        return ToolCall(self.last_response)

class ToolCall:
    def __init__(self, response):
        self.response = response
    
    def is_valid(self):
        # send() leaves last_response None when the API call failed outright.
        if self.response is None or not getattr(self.response, "candidates", None):
            return False
        content = self.response.candidates[0].content
        if content is None or not content.parts:
            return False
        part = content.parts[0]
        return part.function_call is not None \
        and part.function_call.name == "replace_schema"

def within_budget():
    return tokens_used <= max_tokens

max_tokens = 0
tokens_used = 0
    
async def main(init_nl_file: str, init_lean_file: str):
    global server, lean_compiler, nl_problem
    await start_server()
    lean_compiler = LeanCompiler()

    with open(init_nl_file, 'r', encoding='utf-8') as f:
        nl_problem = f.read()

    nl_final_sketch, lean_final_sketch = await prover_subagent(lean_compiler.check(init_lean_file))

    github_summary_path = os.environ.get('GITHUB_STEP_SUMMARY')
    if github_summary_path and lean_final_sketch:
        with open(github_summary_path, 'a') as f:
            f.write("\n" + lean_final_sketch + "\n")

    if lean_final_sketch:
        return 0
    else:
        return 1

def worker_function(worker_id, result_queue, args):
    global server, lean_compiler, library_imports, max_tokens, target_lean_path, target_olean_path
    """The function running in parallel."""

    library_imports = args.libs
    if "Init" not in library_imports:
        library_imports.append("Init")

    max_tokens = args.token_limit
    target_lean_path = args.initial_file_lean
    initial_prob_path = args.initial_file_nl
    target_olean_path = args.initial_file_lean.removesuffix('.lean') + '.olean'
    print(f"Process {os.getpid()} (Task {worker_id}) started.")
    emit("worker_start", worker_id=worker_id)

    _arm_wall_clock(worker_id)

    rc = 1
    try:
        rc = asyncio.run(main(initial_prob_path, target_lean_path))
    except BaseException as exc:  # noqa: BLE001 - must not lose the queue slot
        import traceback
        rc = 1
        emit("worker_error", exc_type=type(exc).__name__, message=str(exc)[:500],
             traceback=traceback.format_exc()[:4000])
        print(f"Process {os.getpid()} (Task {worker_id}) failed: {exc}")
    finally:
        rc = 1 if rc is None else rc
        emit("worker_end", worker_id=worker_id, rc=rc)
        print(f"Process {os.getpid()} (Task {worker_id}) finished with rc={rc}.")
        # Always report. Without this the parent blocks forever on queue.get().
        result_queue.put((rc, worker_id))

def _arm_wall_clock(worker_id):
    """Self-terminate slightly before the supervisor's hard kill."""
    budget = int(os.environ.get("PROVER_WALL_SECONDS", "0"))
    if budget <= 0:
        return

    def expire():
        emit("worker_timeout", worker_id=worker_id, budget_s=budget)
        print(f"Wall-clock budget of {budget}s exhausted; exiting.")
        os._exit(2)

    timer = threading.Timer(budget, expire)
    timer.daemon = True
    timer.start()


def run_until_first_success(args):
    num_processes = args.num_procs
    # A thread/process-safe queue to pass messages back to the main script
    result_queue = Queue()
    processes = []

    # 1. Spin up the exact number of processes
    for i in range(num_processes):
        p = Process(target=worker_function, args=(i + 1, result_queue, args))
        processes.append(p)
        p.start()

    # 2. Block and wait for the very first message in the queue
    num_returned_procs = 0
    return_code = -1

    while return_code != 0 and num_returned_procs < num_processes:
        return_code, winning_task = result_queue.get()

        if return_code == 0:
            print(f"Task {winning_task} finished first with code 0! Killing all other processes...")
            # 3. Loop through and forcefully terminate all other running processes
            for p in processes:
                if p.is_alive():
                    print(f"Terminating process {p.pid}...")
                    p.terminate()  # Sends a SIGTERM signal to the process
                    p.join()       # Clean up the process resource out of the OS table
            
            print("\nAll other processes successfully cleaned up.")

        num_returned_procs += 1

    return return_code
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Prover subagent that uses LLM to suggest tactics and Lean compiler to verify. \
    It outputs a complete proof if it contains no sorrys and compiles, or an incomplete proof if the program runs out of tokens.")
    parser.add_argument("initial_file_nl", help="Path string for unsolved problem statement.")
    parser.add_argument("initial_file_lean", help="Path string for unsolved problem statement in Lean.")
    parser.add_argument("--libs", nargs='*', default=[], help="Optional list of additional lean libraries to compile with. Init is included by default")
    parser.add_argument("--num_procs", type=int, default=4, help="Number of independent solvers.")
    parser.add_argument("--token_limit", type=int, default=10000, help="Maximum number of tokens allowed.")

    args = parser.parse_args()
    emit("run_start", script="whole_proof_subagent.py", num_procs=args.num_procs,
         target=args.initial_file_lean)
    compile_lean_file(args.initial_file_lean)
    rc = run_until_first_success(args)
    emit("run_end", rc=rc)

    # Opt-in so plain CLI usage keeps its historical exit status.
    if os.environ.get("PROVER_STRICT_EXIT") == "1":
        sys.exit(0 if rc == 0 else 1)
