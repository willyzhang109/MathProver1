"""Build the reference .olean that SafeVerify checks submissions against.

Done here rather than by the prover's compile_lean_file() for two reasons: that
function's return value is discarded by the scripts, so a failed reference build
surfaces much later as a FileNotFoundError inside verify_sketch; and its
`lake clean` prelude would delete the shared build tree out from under every
other running job.

`lean` is invoked directly with a cached LEAN_PATH rather than through
`lake env`, so concurrent jobs never contend on the Lake workspace lock.
"""

import asyncio
import logging
import os
from pathlib import Path
from typing import Dict, Optional, Tuple

from ..config import settings

log = logging.getLogger("olean")

_lean_env: Optional[Dict[str, str]] = None


async def _capture(*cmd: str) -> Tuple[int, str, str]:
    proc = await asyncio.create_subprocess_exec(
        *cmd, cwd=str(settings.lake_root),
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
    out, err = await proc.communicate()
    return proc.returncode, out.decode("utf-8", "replace"), err.decode("utf-8", "replace")


async def lean_env() -> Dict[str, str]:
    """Capture LEAN_PATH / LD_LIBRARY_PATH once at startup."""
    global _lean_env
    if _lean_env is not None:
        return _lean_env

    env = {}
    for var in ("LEAN_PATH", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
        rc, out, _ = await _capture("lake", "env", "printenv", var)
        if rc == 0 and out.strip():
            env[var] = out.strip()

    _lean_env = env
    log.info("captured lean env: %s", ", ".join(env) or "(none)")
    return env


async def build_reference(lean_file: Path, timeout: int = 300) -> Tuple[bool, str]:
    """Compile `lean_file` to a sibling .olean. Returns (ok, output)."""
    olean = lean_file.with_suffix(".olean")
    if olean.exists():
        olean.unlink()

    env = dict(os.environ)
    env.update(await lean_env())

    cmd = ["lean", "-o", str(olean), str(lean_file)]
    if not (await lean_env()):
        # No cached LEAN_PATH: fall back to going through lake.
        cmd = ["lake", "env"] + cmd

    proc = await asyncio.create_subprocess_exec(
        *cmd, cwd=str(settings.lake_root), env=env,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
    try:
        out, _ = await asyncio.wait_for(proc.communicate(), timeout=timeout)
    except asyncio.TimeoutError:
        proc.kill()
        return False, f"Building the reference specification exceeded {timeout}s."

    text = out.decode("utf-8", "replace")
    if proc.returncode != 0:
        return False, text
    if not olean.exists():
        return False, "lean exited 0 but produced no .olean\n" + text
    return True, text
