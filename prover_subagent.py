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
running_sketch = None
verified_sketch = None
blocks_exhausted = False
server = None
library_imports = None
target_lean_path = None
target_olean_path = None
temp_proof_count = 0

EVOLVE_BLOCK_START = "-- EVOLVE-BLOCK-START"
EVOLVE_BLOCK_END = "-- EVOLVE-BLOCK-END"
EVOLVE_VALUE_START = "-- EVOLVE-VALUE-START"
EVOLVE_VALUE_END = "-- EVOLVE-VALUE-END"

initial_prompt = """
# 1. Role and Goal
You are a world-class mathematician and Lean 4 expert.
Your goal is to solve hard mathematical problems by devising a proof strategy
and translating it into a Lean 4 proof.

# 2. Your Task
You will be given Lean code containing theorem statement with a partial proof. You goal is to
modify the file to continue proving the statement until there are no sorries left.

You will be getting feedback from Lean Compiler after every time you modify code.
Compilation errors will be highlighted and you need to keep iterating until the code compiles.
CRITICAL: Don't end a session with a final proof that doesn't compile. However, ensure that you still
try to make progress, even if the proof in an intermediate iteration does not compile.
But, if you can't finish the proof in the current session at least make sure it compiles 
before you wrap up the session. Put any findings, plans or solutions as
comments in the file. Only file content will be passed to the next session.

Think like a mathematician: focus on the key insights, proof structure, and
creative steps (e.g., constructing an object via 'let').
If you get stuck on the main proof, try to gain insights by exploring diverse ideas:
study specific cases, or define and attempt to prove interesting generalizations,
specializations, or variants of the problem statement as new helper lemmas.
Prefer clever mathematical arguments over brute-force casework where possible.

Do not only add comments.

Some of these problems are very hard, possibly even open problems in mathematics.
But don't be discouraged: approach them with curiosity and persistence.
Like George Dantzig, who solved two famous unsolved problems in statistics thinking they were homework,
you might solve a problem you think is difficult simply by not knowing it was considered impossible!
Believe in your ability to find creative solutions where others might not.

CRITICAL: You MUST use tools available to you exhaustively to refine your proof
until you either find a proof or are certain the current direction is flawed.
Do NOT give up easily, and NEVER put off formalization work to the next session if you have more tool calls available.
Your effort in each turn must be maximal: try to solve the problem in full, as if there is no next session.

**No Imports:** The execution environment imports 'Mathlib' by default.
Do **not** add any 'import' statements in your proof."""

iter_prompt = """
# Current proof
# This is the proof to be modified in the current session.
Start of the proof:
{sketch}
End of the proof.
Make sure that you only propose changes inside sections enclosed by
'-- EVOLVE-BLOCK-START' and '-- EVOLVE-BLOCK-END',
or '-- EVOLVE-VALUE-START' and '-- EVOLVE-VALUE-END' comments.
You may make as many edits within any of the blocks each time as you see fit.
Do not only add comments.
Make progress inside at least one block each time, do not only add comments.
After you are done making the changes, compare your newly changed proof against the old one,
and generate a tool call that is a list of edits with the new content within each -- EVOLVE block in order of blocks from top to bottom,
with the topmost block having block number 0, second topmost block having number 1, etc.
The number of blocks changes as you make progress, so please recount the blocks each time when numbering your edits.
If there are no changes within a block, you may omit it from the tool call as it is redundant.
You only send back this tool call."""

async def start_server():
    global server
    project_path = os.environ.get("PROVER_PROJECT_PATH", ".")
    started = time.time()
    server = await pantograph.Server.create(project_path=project_path, imports=library_imports)
    # Importing Mathlib takes 30-60s; report it so the UI can distinguish
    # "still starting up" from "hung".
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

def list_evolve_blocks(sketch: str):
    list_evolve = []
    list_block_start = []
    list_block_end = []
    list_value_start = []
    list_value_end = []
    list_blocks = []
    list_values = []

    line_starts = [0] + [m.end() for m in re.finditer(r'\n', sketch)]

    for block_start_line in re.finditer(EVOLVE_BLOCK_START, sketch):
        start_pos = block_start_line.start()

        block_line_no = bisect.bisect_right(line_starts, start_pos)

        block_col_no = start_pos - line_starts[block_line_no - 1] + 1
        list_block_start.append((block_line_no, block_col_no))

    for block_end_line in re.finditer(EVOLVE_BLOCK_END, sketch):
        end_pos = block_end_line.start()

        block_line_no = bisect.bisect_right(line_starts, end_pos)

        block_col_no = end_pos - line_starts[block_line_no - 1] + 1
        list_block_end.append((block_line_no, block_col_no))

    for value_start_line in re.finditer(EVOLVE_VALUE_START, sketch):
        start_pos = value_start_line.start()

        block_line_no = bisect.bisect_right(line_starts, start_pos)

        block_col_no = start_pos - line_starts[block_line_no - 1] + 1
        list_value_start.append((block_line_no, block_col_no))

    for value_end_line in re.finditer(EVOLVE_VALUE_END, sketch):
        end_pos = value_end_line.start()

        block_line_no = bisect.bisect_right(line_starts, end_pos)

        block_col_no = end_pos - line_starts[block_line_no - 1] + 1
        list_value_end.append((block_line_no, block_col_no))

    for i in range(min(len(list_block_start), len(list_block_end))):
        if (list_block_start[i][0] == list_block_end[i][0] and (list_block_start[i][1] + len(EVOLVE_BLOCK_START)) < list_block_end[i][1]) \
        or (list_block_start[i][0] < list_block_end[i][0]):
            list_blocks.append((list_block_start[i], list_block_end[i]))

    for j in range(min(len(list_value_start), len(list_value_end))):
        if (list_value_start[j][0] == list_value_end[j][0] and (list_value_start[j][1] + len(EVOLVE_VALUE_START)) < list_value_end[j][1]) \
        or (list_value_start[j][0] < list_value_end[j][0]):
            list_values.append((list_value_start[j], list_value_end[j]))

    l = 0
    m = 0

    while l < len(list_blocks):
        while m < len(list_values) and list_values[m][0] < list_blocks[l][0] and list_values[m][1] < list_blocks[l][1]:
            list_evolve.append(list_values[m])
            m += 1

        list_evolve.append(list_blocks[l])
        l += 1
    
    return list_evolve

# Basic prover subagent
async def prover_step():
    global running_sketch, tokens_used, target_olean_path, verified_sketch, blocks_exhausted
    session = LlmSketcher() # Start an LLM session
    iteration = 0
    while tool_call := session.recv():
        feedback = ""
        # print(tool_call.response)
        iteration += 1
        emit("iteration", n=iteration, tokens_used=tokens_used, max_tokens=max_tokens)

        if tool_call.is_search_replace():
            # extract feedback
            compile_started = time.time()
            running_sketch.lean_sketch, feedback = await search_replace_then_compile(tool_call)
            # update token count
            # feedback.goal_state — empty = done
            
            # print(feedback)
            feedback_errors = feedback_to_error_positions(feedback)
            unclosed_blocks = list_evolve_blocks(running_sketch.lean_sketch)

            # Snapshot progress before `feedback` is rebound to a string below.
            all_messages = [m for unit in feedback for m in (unit.messages or [])]
            emit("sketch",
                 lean=truncate(running_sketch.lean_sketch, 200_000),
                 chars=len(running_sketch.lean_sketch))
            emit("compile",
                 duration_s=round(time.time() - compile_started, 2),
                 n_errors=len(feedback_errors),
                 n_warnings=sum(1 for m in all_messages
                                if getattr(getattr(m, "severity", None), "name", "") == "WARNING"),
                 errors=errors_payload(all_messages))
            emit("blocks", count=len(unclosed_blocks))

            sketch_lines = running_sketch.lean_sketch.splitlines()
            sketch_lines = [list(line) for line in sketch_lines]

            j = 0
            for i in range(len(unclosed_blocks)):
                sorry_in_block = False

                if unclosed_blocks[i][0][0] == unclosed_blocks[i][1][0]:
                    block_line = sketch_lines[unclosed_blocks[i][0][0] - 1][unclosed_blocks[i][0][1] - 1 : unclosed_blocks[i][1][1]]
                    sorry_in_block = "sorry" in "".join(block_line)
                else:
                    first_line = sketch_lines[unclosed_blocks[i][0][0] - 1][unclosed_blocks[i][0][1] - 1:]
                    last_line = sketch_lines[unclosed_blocks[i][1][0] - 1][:unclosed_blocks[i][1][1] - 1]

                    if "sorry" in "".join(first_line) or "sorry" in "".join(last_line):
                        sorry_in_block = True
                    else:
                        for index in range(unclosed_blocks[i][0][0] - 1, unclosed_blocks[i][1][0] - 1):
                            if "sorry" in "".join(sketch_lines[index]):
                                sorry_in_block = True
                                break

                if sorry_in_block:
                    break
                
                while j < len(feedback_errors) and (feedback_errors[j][1][0] < unclosed_blocks[i][0][0] or (feedback_errors[j][1][0] == unclosed_blocks[i][0][0] and feedback_errors[j][1][1] < unclosed_blocks[i][0][1])):
                    j += 1

                if j >= len(feedback_errors) or (feedback_errors[j][0][0] > unclosed_blocks[i][1][0] or (feedback_errors[j][0][0] == unclosed_blocks[i][1][0] and feedback_errors[j][0][1] > unclosed_blocks[i][1][1])):
                    for l in range(len(EVOLVE_BLOCK_START)):
                        sketch_lines[unclosed_blocks[i][0][0] - 1][unclosed_blocks[i][0][1] - 1 + l] = ' '
                    
                    for m in range(len(EVOLVE_BLOCK_END)):
                        sketch_lines[unclosed_blocks[i][1][0] - 1][unclosed_blocks[i][1][1] - 1 + m] = ' '

                    emit("block_closed", block_id=i, remaining=len(unclosed_blocks) - i - 1)
                else:
                    break

            new_sketch = ["".join(sketch_line) for sketch_line in sketch_lines]
            running_sketch.lean_sketch = "\n".join(new_sketch)
            
            # Recompute: `unclosed_blocks` was captured before the retirement
            # pass above, so testing it here misses the iteration that closes
            # the last block. The session then keeps prodding the model with
            # empty feedback until the API rejects the request.
            remaining_blocks = list_evolve_blocks(running_sketch.lean_sketch)
            if len(remaining_blocks) == 0:
                print("All EVOLVE blocks closed; proceeding to verification.")
                blocks_exhausted = True
                break

            feedback = format_messages_to_string(feedback)
            print(feedback)
            # extract the ".messages" field of feedback and sends it as a string
            tokens_used += len(feedback)
        else:
            print("No replacements this iteration")
            emit("llm_error", message="model returned no usable tool call")
            time.sleep(30)
            # Never send an empty turn: Gemini rejects a request whose history
            # ends on a model turn with "Requests ending with a model turn are
            # not supported".
            feedback = ("No edits were received. Reply with a replace_block_content "
                        "tool call containing your changes.")

        session.send(feedback)

    print(f"Final Response: {tool_call.response}")

    print("Final Sketch: ")
    print(running_sketch.lean_sketch)

    print(f"Target olean path: {target_olean_path}")

    emit("verify_start")
    if target_olean_path and lean_compiler.verify_integrity(running_sketch): # Check for hacks
        print("sketch verified")
        verified_sketch = running_sketch
        path = write_result({
            "success": True,
            "lean": running_sketch.lean_sketch,
            "worker_pid": os.getpid(),
        })
        emit("proof_found", path=path, chars=len(running_sketch.lean_sketch))
        return running_sketch
    
    print("No valid sketch generated")
    return None

async def prover_subagent(initial_sketch):
    global running_sketch, target_olean_path, tokens_used
    running_sketch = initial_sketch
    print(f"Process {os.getpid()}.")
    max_iters = int(os.environ.get("PROVER_MAX_ITERS", "0")) or None
    rounds = 0

    while within_budget() and running_sketch.contains_sorry():
        if new_sketch := await prover_step():
            running_sketch = new_sketch

        rounds += 1
        # Guarantee the budget always advances. Several paths through
        # prover_step() return without charging any tokens, which previously
        # made this an infinite loop.
        tokens_used += 1
        if blocks_exhausted:
            print("No EVOLVE blocks remain; stopping.")
            break
        if max_iters and rounds >= max_iters:
            print(f"Reached PROVER_MAX_ITERS={max_iters}; stopping.")
            break

    # Return the *verified* sketch, or None. Returning running_sketch
    # unconditionally made main() report success even with sorries left.
    return verified_sketch

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
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=True
            )

            subprocess.run(
                lake_update_command,
                cwd=cwd_path,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=True
            )

            subprocess.run(
                lake_cache_get_command,
                cwd=cwd_path,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=True
            )

            subprocess.run(
                lake_build_command,
                cwd=cwd_path,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
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
        with open(file, 'r', encoding='utf-8') as f:
            return Sketch(f.read())
            # should we decode as utf-8?

    def verify_integrity(self, sketch):
        result = self.checker.verify_sketch(target_olean_path, running_sketch.lean_sketch)
        return result["success"]

def replace_block_by_id(block_id: int, new_code: str):
    global running_sketch
    
    # 1. Get the list of all active blocks in the file
    # Returns list of tuples: [((start_line, start_col), (end_line, end_col)), ...]
    unclosed_blocks = list_evolve_blocks(running_sketch.lean_sketch)
    
    if block_id >= len(unclosed_blocks):
        print(f"Model requested block_id {block_id}, but only {len(unclosed_blocks)} blocks exist.")
        print(f"Attempted to add {new_code} to {block_id}")
        return running_sketch.lean_sketch
        
    # 2. Extract the target block's boundaries
    target_block = unclosed_blocks[block_id]
    start_coords, end_coords = target_block
    
    start_line, start_col = start_coords
    end_line, end_col = end_coords
    
    # 3. Split your file text into lines to perform a precision surgical strike
    lines = running_sketch.lean_sketch.splitlines()
    
    # In Python lines are 0-indexed, but compiler lines are 1-indexed
    # The insertion zone starts right AFTER the start marker line, 
    # and ends right BEFORE the end marker line.
    zone_start = start_line  # Line after -- EVOLVE-BLOCK-START
    zone_end = end_line - 1  # Line before -- EVOLVE-BLOCK-END
    
    # 4. Replace the old tactics with the new tactics string
    # We slice out the inner content and insert the new lines
    new_tactic_lines = new_code.splitlines()
    lines[zone_start:zone_end] = new_tactic_lines
    
    # 5. Rejoin and save the new file state
    running_sketch.lean_sketch = "\n".join(lines)
    return running_sketch.lean_sketch

replace_block_schema = types.FunctionDeclaration(
    name="replace_block_content",
    description="Replaces the code inside multiple EVOLVE-BLOCKs in a single call.",
    parameters={
        "type": "OBJECT",
        "properties": {
            "replacements": {
                "type": "ARRAY",
                "description": "A list of block replacements to perform.",
                "items": {
                    "type": "OBJECT",
                    "properties": {
                        "block_id": {
                            "type": "INTEGER",
                            "description": "The 0-indexed ID of the EVOLVE-BLOCK you want to modify."
                        },
                        "new_code": {
                            "type": "STRING",
                            "description": "The raw Lean 4 tactics to insert strictly BETWEEN the block markers. Do not include the marker comments."
                        }
                    },
                    "required": ["block_id", "new_code"]
                }
            }
        },
        "required": ["replacements"]
    }
)

tools = types.Tool(function_declarations=[replace_block_schema])
class LlmSketcher:
    def __init__(self):
        global max_tokens, tokens_used, tools, running_sketch, initial_prompt

        # check API key set
        self.client = genai.Client()
        self.chat = self.client.chats.create(
            model=os.environ.get("PROVER_MODEL", "gemini-3.6-flash"),
            config=types.GenerateContentConfig(
                system_instruction=initial_prompt,
                tools=[tools],
                temperature=0.5,
                thinking_config=types.ThinkingConfig(
                    thinking_level=types.ThinkingLevel.HIGH
                )
            )
        )
        self.last_response = self.chat.send_message(iter_prompt.format(sketch=running_sketch.lean_sketch))
        # print(self.last_response)

    def send(self, feedback):
        global temp_proof_count
        scratch_dir = os.environ.get("PROVER_SCRATCH_DIR")
        if scratch_dir == "-":
            temp_lean_path = None
        elif scratch_dir:
            os.makedirs(scratch_dir, exist_ok=True)
            temp_lean_path = os.path.join(
                scratch_dir, f"w{os.getpid()}_{temp_proof_count}.lean")
        else:
            temp_lean_path = target_olean_path.removesuffix('.olean') + "_" + str(temp_proof_count) + '.lean'
        temp_proof_count += 1
        if temp_lean_path:
            with open(temp_lean_path, "w") as temp_sketch_file:
                temp_sketch_file.write(f"""Sketch:
                                    {running_sketch.lean_sketch}

                                    Feedback:
                                    {feedback}
                                    """)
        
        started = time.time()
        emit("llm_request", prompt_chars=len(feedback or ""))
        try:
            self.last_response = self.chat.send_message(feedback)
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
                    self.last_response = self.chat.send_message(feedback)
                except errors.APIError as retry_err:
                    # A second failure must not take the worker down: the
                    # caller still has a possibly-verifiable sketch in hand.
                    print(f"Retry after history trim also failed: {retry_err}")
                    emit("llm_error", code=getattr(retry_err, "code", None),
                         message=str(retry_err)[:500], retried=True)
                    self.last_response = None

    def recv(self):
        print(f"Tool Call response: {self.last_response}")
        return ToolCall(self.last_response)

class ToolCall:
    def __init__(self, response):
        self.response = response
    
    def is_search_replace(self):
        part = self.response.candidates[0].content.parts[0]
        if self.response is None or self.response.candidates is None or self.response.candidates[0].content is None:
            return False
        
        return part is not None \
        and part.function_call is not None \
        and part.function_call.name == "replace_block_content"

# only recompile
async def search_replace_then_compile(tool_call: ToolCall):
    global running_sketch, server
    replacements = tool_call.response.function_calls[0].args["replacements"]
    new_sketch = running_sketch.lean_sketch

    for replacement in replacements:
        print(f"block_id: {replacement["block_id"]}")
        print(f"new_code: {replacement["new_code"]}")
        new_sketch = replace_block_by_id(replacement["block_id"], replacement["new_code"])

    new_sketch_lines = new_sketch.splitlines()
    i = 0

    while i < len(new_sketch_lines) and new_sketch_lines[i].startswith("import"):
        i += 1

    new_sketch_lines = new_sketch_lines[i:]
    
    return new_sketch, await server.check_compile_async("\n".join(new_sketch_lines), read_header=False)

def within_budget():
    return tokens_used <= max_tokens

max_tokens = 0
tokens_used = 0

class Sketch:
    def __init__(self, lean_sketch: str):
        self.lean_sketch = lean_sketch
    
    def contains_sorry(self):
        return "sorry" in self.lean_sketch
    
async def main(init_file: str):
    global server, lean_compiler
    await start_server()
    lean_compiler = LeanCompiler()
    final_sketch = await prover_subagent(lean_compiler.check(init_file))

    github_summary_path = os.environ.get('GITHUB_STEP_SUMMARY')
    if github_summary_path and final_sketch:
        with open(github_summary_path, 'a') as f:
            f.write("\n" + final_sketch.lean_sketch + "\n")

    if final_sketch:
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
    target_lean_path = args.initial_file
    target_olean_path = args.initial_file.removesuffix('.lean') + '.olean'
    print(f"Process {os.getpid()} (Task {worker_id}) started.")
    emit("worker_start", worker_id=worker_id)

    _arm_wall_clock(worker_id)

    rc = 1
    try:
        rc = asyncio.run(main(target_lean_path))
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
    """Self-terminate slightly before the supervisor's hard kill.

    A loop-top deadline check is useless here: this process spends most of its
    time blocked inside a multi-minute Gemini call.
    """
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
    parser.add_argument("initial_file", help="Path string for initial file of sketch.")
    parser.add_argument("--libs", nargs='*', default=[], help="Optional list of additional lean libraries to compile with. Init is included by default")
    parser.add_argument("--num_procs", type=int, default=4, help="Number of independent solvers.")
    parser.add_argument("--token_limit", type=int, default=10000, help="Maximum number of tokens allowed.")

    args = parser.parse_args()
    emit("run_start", script="prover_subagent.py", num_procs=args.num_procs,
         target=args.initial_file)
    compile_lean_file(args.initial_file)
    rc = run_until_first_success(args)
    emit("run_end", rc=rc)

    # Opt-in so plain CLI usage keeps its historical exit status.
    if os.environ.get("PROVER_STRICT_EXIT") == "1":
        sys.exit(0 if rc == 0 else 1)
