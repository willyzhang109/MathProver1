"""Natural language -> Lean 4 statement, via Gemini."""

import asyncio
import logging
import re
from dataclasses import dataclass, field
from typing import List, Optional

from ..config import settings

log = logging.getLogger("formalizer")

SYSTEM_PROMPT = """You are an expert in Lean 4 and Mathlib formalization.

Given a mathematical problem in natural language, produce the Lean 4 *statement*
of that problem as a single theorem with an unfinished proof.

Rules, all mandatory:
- Output exactly one `theorem` declaration. Give it a short descriptive snake_case name.
- End it with `:= by sorry`. Do NOT attempt to prove it.
- Do NOT emit any `import` lines. Mathlib is already imported.
- Do NOT emit `axiom`, `unsafe`, `partial`, or `native_decide`.
- Use idiomatic Mathlib: bind every variable explicitly, prefer `ℕ`/`ℤ`/`ℝ` and
  Mathlib's standard predicates over ad-hoc definitions.
- State the problem faithfully. If it asks to *find* a value, state that the
  specific value satisfies the property. If it asks to *prove*, state the claim.
- The statement must be a faithful formalization: a reader comparing it to the
  original problem should agree they say the same thing.

Respond with the Lean code only, in a single ```lean fenced block, followed by a
one-paragraph plain-English restatement of exactly what your Lean statement says,
under a line reading `RESTATEMENT:`.
"""

REPAIR_PROMPT = """That Lean statement does not compile. The Lean compiler reported:

{errors}

Fix the statement. Same rules as before: one theorem, `:= by sorry`, no imports.
Respond in the same format."""

FENCE = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.DOTALL)


@dataclass
class Formalization:
    lean: str = ""
    restatement: str = ""
    compiles: bool = False
    repaired: bool = False
    errors: List[dict] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


class FormalizerUnavailable(RuntimeError):
    pass


def _extract(text: str):
    lean, restatement = "", ""
    match = FENCE.search(text or "")
    if match:
        lean = match.group(1).strip()
        tail = text[match.end():]
    else:
        # No fence: take everything up to RESTATEMENT as code.
        parts = re.split(r"^RESTATEMENT:\s*", text or "", flags=re.MULTILINE)
        lean = parts[0].strip()
        tail = parts[1] if len(parts) > 1 else ""

    rest = re.split(r"^RESTATEMENT:\s*", tail, flags=re.MULTILINE)
    restatement = (rest[1] if len(rest) > 1 else tail).strip()
    # Belt and braces: the model is told not to, but strip imports anyway.
    lean = "\n".join(l for l in lean.splitlines() if not l.strip().startswith("import "))
    return lean.strip(), restatement


class Formalizer:
    def __init__(self):
        self._client = None

    def _get_client(self):
        if self._client is None:
            if not settings.gemini_api_key:
                raise FormalizerUnavailable("No Gemini API key is configured.")
            from google import genai
            self._client = genai.Client(api_key=settings.gemini_api_key)
        return self._client

    async def _ask(self, contents, system: str) -> str:
        from google.genai import types

        client = self._get_client()

        def call():
            return client.models.generate_content(
                model=settings.formalizer_model,
                contents=contents,
                config=types.GenerateContentConfig(
                    system_instruction=system,
                    temperature=0.2,
                ),
            )

        try:
            response = await asyncio.wait_for(
                asyncio.to_thread(call), timeout=settings.formalizer_timeout_s)
        except asyncio.TimeoutError:
            raise FormalizerUnavailable("The formalizer timed out.")
        except Exception as exc:  # noqa: BLE001
            raise FormalizerUnavailable(f"The formalizer is unavailable: {exc}")

        return getattr(response, "text", "") or ""

    async def formalize(self, nl: str, checker=None) -> Formalization:
        text = await self._ask(nl, SYSTEM_PROMPT)
        lean, restatement = _extract(text)
        out = Formalization(lean=lean, restatement=restatement)

        if not lean:
            raise FormalizerUnavailable("The model returned no Lean code.")
        if checker is None:
            return out

        result = await checker.compile(lean)
        out.compiles = result.ok
        out.errors = result.errors
        if result.ok:
            return out

        # One automatic repair round before handing the user a broken draft.
        rendered = "\n".join(
            f"line {e.get('line')}: {e.get('message', '')[:400]}" for e in result.errors[:6])
        text = await self._ask(
            [nl, text, REPAIR_PROMPT.format(errors=rendered)], SYSTEM_PROMPT)
        lean2, restatement2 = _extract(text)
        if lean2:
            result2 = await checker.compile(lean2)
            out.repaired = True
            if result2.ok or len(result2.errors) < len(result.errors):
                out.lean = lean2
                out.restatement = restatement2 or out.restatement
                out.compiles = result2.ok
                out.errors = result2.errors

        if not out.compiles:
            out.warnings.append(
                "The generated statement does not compile yet. Edit it below before submitting.")
        return out


formalizer = Formalizer()
