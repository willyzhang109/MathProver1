#!/usr/bin/env python3

import os
import shlex
import subprocess
import json
from pathlib import Path
from typing import Dict, Any, Optional
from uuid import uuid4

from prover_events import emit


def _cmd_from_env(name: str, default: str) -> list:
    """Read a command line out of the environment, falling back to a default."""
    return shlex.split(os.environ.get(name) or default)


class SafeVerifyRunner:
    def __init__(self, lake_workspace_dir: Optional[str] = None,
                 scratch_dir: Optional[str] = None):
        """
        Initializes the SafeVerify pipeline runner.

        Args:
            lake_workspace_dir (str, optional): The directory where your Lean 4 project/Lake
                                                environment lives. Defaults to the current
                                                working directory.
            scratch_dir (str, optional): Where to stage submission files. Defaults to
                                         $SAFEVERIFY_SCRATCH_DIR, else the workspace. Keeping
                                         these out of the workspace is what stops concurrent
                                         jobs from littering the Lake root.
        """
        self.workspace = os.path.abspath(lake_workspace_dir) if lake_workspace_dir else os.getcwd()
        self.scratch = os.path.abspath(
            scratch_dir or os.environ.get("SAFEVERIFY_SCRATCH_DIR") or self.workspace
        )
        os.makedirs(self.scratch, exist_ok=True)

        # Calling the built binaries directly avoids serializing every concurrent
        # verification on the Lake workspace lock.
        self.lean_cmd = _cmd_from_env("SAFEVERIFY_LEAN_CMD", "lake env lean")
        self.verify_cmd = _cmd_from_env("SAFEVERIFY_BIN", "lake exe safe_verify")
        self.header = os.environ.get("SAFEVERIFY_HEADER", "")
        self.verbose = os.environ.get("SAFEVERIFY_VERBOSE") == "1"
        self.timeout = int(os.environ.get("SAFEVERIFY_TIMEOUT", "600"))

    def _ensure_header(self, proof_sketch: str) -> str:
        """Prepend the import header when the submission omits one.

        The whole-proof agent is told not to emit imports (the Pantograph server
        already holds them), but SafeVerify compiles the submission with plain
        `lean`, which has no such context, and enforces that the submission
        imports a superset of the target's imports.
        """
        if not self.header:
            return proof_sketch
        head = "\n".join(proof_sketch.splitlines()[:20])
        if any(line.startswith("import ") for line in head.splitlines()):
            return proof_sketch
        return self.header.rstrip("\n") + "\n\n" + proof_sketch

    def verify_sketch(self, target_olean_path: str, proof_sketch: str,
                      disallow_partial: bool = True) -> Dict[str, Any]:
        """
        Validates an incoming proof sketch string against the configured specification.

        Args:
            target_olean_path (str): Compiled reference specification to check against.
            proof_sketch (str): The raw text submission containing declarations/theorems.
            disallow_partial (bool): If True, flags 'partial' definitions as an immediate failure.

        Returns:
            dict: Structured status reports outlining compilation and validation metrics.
        """

        target_olean = os.path.abspath(target_olean_path)
        target_fname = Path(target_olean_path).name.removesuffix('.olean')

        if not os.path.exists(target_olean):
            raise FileNotFoundError(f"Target specification file not found at: {target_olean}")

        # Unique, shell-safe stem: the old datetime-based names contained spaces and colons.
        stem = f"{os.getpid()}-{target_fname}-submission-{uuid4().hex[:8]}"
        submission_lean = os.path.join(self.scratch, stem + ".lean")
        submission_olean = os.path.join(self.scratch, stem + ".olean")
        report_json_path = os.path.join(self.scratch, stem + "-report.json")

        # Step 1: Stage the string onto the disk
        with open(submission_lean, "w", encoding="utf-8") as f:
            f.write(self._ensure_header(proof_sketch))

        # Step 2: Compile to bytecode within the active Lake environment
        # This isolates the string formatting and guarantees type checks pass locally

        print("compiling submission")
        compile_cmd = self.lean_cmd + ["-o", submission_olean, submission_lean]
        try:
            compile_res = subprocess.run(
                compile_cmd, cwd=self.workspace,
                capture_output=True, text=True, timeout=self.timeout
            )
        except subprocess.TimeoutExpired:
            result = {
                "success": False,
                "status": "TIMEOUT",
                "message": f"Compiling the submission exceeded {self.timeout}s.",
                "details": "",
            }
            emit("verify_result", **result)
            return result

        if compile_res.returncode != 0:
            print(f"Proof failed to compile: {compile_res.stderr}")
            result = {
                "success": False,
                "status": "COMPILATION_ERROR",
                "message": "The proof sketch string failed to compile in Lean 4.",
                "details": compile_res.stderr,
                "stdout": compile_res.stdout,
            }
            emit("verify_result", **result)
            return result

        # Step 3: Run the SafeVerify binary comparison script
        verify_cmd = list(self.verify_cmd)

        if disallow_partial:
            verify_cmd.append("--disallow-partial")
        if self.verbose:
            verify_cmd.append("--verbose")

        # SafeVerify only writes its JSON report when handed --save.
        verify_cmd.extend(["--save", report_json_path])

        # Append positional file targets: [target, submission]
        verify_cmd.extend([target_olean, submission_olean])

        print("Verifying Submission")
        try:
            verify_res = subprocess.run(
                verify_cmd, cwd=self.workspace,
                capture_output=True, text=True, timeout=self.timeout
            )
        except subprocess.TimeoutExpired:
            result = {
                "success": False,
                "status": "TIMEOUT",
                "message": f"SafeVerify exceeded {self.timeout}s.",
                "details": "",
            }
            emit("verify_result", **result)
            return result

        # Step 4: Extract structural results out of SafeVerify's generated JSON map
        detailed_report = {}
        if os.path.exists(report_json_path):
            with open(report_json_path, "r", encoding="utf-8") as rf:
                try:
                    detailed_report = json.load(rf)
                except json.JSONDecodeError:
                    pass

        if verify_res.returncode == 0:
            print("Proof verified with no issues.")
            result = {
                "success": True,
                "status": "VERIFIED",
                "message": "Integrity check passed. Declarations match exactly with no exploit vectors.",
                "report": detailed_report,
                "stdout": verify_res.stdout,
            }
        else:
            print(f"Proof contained hacks or unverifiable errors: {verify_res.stderr}")
            print(f"{detailed_report}")
            result = {
                "success": False,
                "status": "VERIFICATION_FAILED",
                "message": "SafeVerify identified structural anomalies or unapproved axioms.",
                "details": verify_res.stderr,
                "stdout": verify_res.stdout,
                "report": detailed_report,
            }

        emit("verify_result", **result)
        return result
