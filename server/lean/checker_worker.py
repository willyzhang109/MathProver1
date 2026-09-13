#!/usr/bin/env python3
"""A single long-lived Lean checker.

Starts one Pantograph server (which imports Mathlib once, ~30-60s) and then
answers compile requests forever over stdin/stdout, one JSON object per line.

Kept as a separate process rather than run inside the API for two reasons: the
Lean elaborator executes attacker-supplied code, and a wedged or OOM-killed
checker must be recyclable without taking the API down with it.

Request:  {"id": "...", "code": "..."}
Response: {"id": "...", "ok": true, "messages": [...], "units": [...]}
"""

import asyncio
import json
import os
import sys


def _severity(msg) -> str:
    sev = getattr(msg, "severity", None)
    return sev.name.lower() if hasattr(sev, "name") else str(sev).lower()


def _message_dict(msg) -> dict:
    pos = getattr(msg, "pos", None)
    pos_end = getattr(msg, "pos_end", None)
    return {
        "line": getattr(pos, "line", None),
        "column": getattr(pos, "column", None),
        "end_line": getattr(pos_end, "line", None),
        "end_column": getattr(pos_end, "column", None),
        "severity": _severity(msg),
        "message": getattr(msg, "data", "") or "",
    }


async def main() -> int:
    import pantograph

    imports = [s for s in os.environ.get("CHECKER_IMPORTS", "Init,Mathlib").split(",") if s]
    project_path = os.environ.get("PROVER_PROJECT_PATH", ".")

    try:
        server = await pantograph.Server.create(
            project_path=project_path,
            imports=imports,
            timeout=int(os.environ.get("CHECKER_LEAN_TIMEOUT", "180")),
        )
    except Exception as exc:  # noqa: BLE001
        print(json.dumps({"id": None, "event": "fatal", "message": str(exc)}), flush=True)
        return 1

    print(json.dumps({"id": None, "event": "ready", "imports": imports}), flush=True)

    loop = asyncio.get_running_loop()
    reader = asyncio.StreamReader()
    await loop.connect_read_pipe(lambda: asyncio.StreamReaderProtocol(reader), sys.stdin)

    while True:
        raw = await reader.readline()
        if not raw:
            break
        line = raw.decode("utf-8", "replace").strip()
        if not line:
            continue

        try:
            request = json.loads(line)
        except json.JSONDecodeError:
            continue

        req_id = request.get("id")
        code = request.get("code") or ""

        try:
            units = await server.check_compile_async(code, read_header=False)
            messages, unit_spans = [], []
            for unit in units:
                # i_begin/i_end are BYTE offsets into the source, not character
                # indices. Callers must slice code.encode("utf-8").
                unit_spans.append({"i_begin": unit.i_begin, "i_end": unit.i_end})
                for msg in (unit.messages or []):
                    messages.append(_message_dict(msg))
            response = {"id": req_id, "ok": True, "messages": messages, "units": unit_spans}
        except Exception as exc:  # noqa: BLE001
            response = {"id": req_id, "ok": False, "error": str(exc)[:2000]}

        print(json.dumps(response, ensure_ascii=False), flush=True)

    try:
        server._close()
    except Exception:  # noqa: BLE001
        pass
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
