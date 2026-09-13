"""Turn arbitrary user-submitted Lean into a file the prover can consume.

`prover_subagent.py` only edits regions delimited by EVOLVE markers, and with
zero blocks it never charges the token budget, so the whole run spins forever.
Users paste plain theorem statements. This module bridges the two.

Lean is not parsed with regexes here. Pantograph segments the source into
top-level commands and reports exact byte boundaries; we classify and rewrite
whole commands. All slicing happens on the utf-8 encoded bytes, because
Mathlib statements are full of characters like ℕ and ∀ where byte offsets and
string indices diverge.
"""

import re
from dataclasses import dataclass, field
from typing import List, Optional

from ..config import settings

BLOCK_START = "-- EVOLVE-BLOCK-START"
BLOCK_END = "-- EVOLVE-BLOCK-END"
VALUE_START = "-- EVOLVE-VALUE-START"
VALUE_END = "-- EVOLVE-VALUE-END"
HEADER = "import Mathlib"

MARKER_LINE = re.compile(
    r"^[ \t]*--[ \t]*EVOLVE-(?:BLOCK|VALUE)-(?:START|END)[ \t]*$", re.MULTILINE)
IMPORT_LINE = re.compile(r"^[ \t]*import[ \t]+(\S+)[ \t]*$")
ALLOWED_IMPORT = re.compile(r"^(Init|Mathlib)(\.[A-Za-z0-9_.]+)?$")

DECL_KEYWORDS = ("theorem", "lemma", "example")
PASSTHROUGH_KEYWORDS = (
    "def", "abbrev", "structure", "inductive", "instance", "class",
    "open", "namespace", "end", "variable", "variables", "section",
    "set_option", "noncomputable", "attribute", "notation", "local", "universe",
    "@[", "macro", "syntax", "declare_syntax_cat", "deriving",
)

# Elaboration-time escapes and axiom smuggling. `axiom` matters most: the user
# supplies the reference statement, so `axiom cheat : False` in the target would
# make it an *allowed* axiom of the spec and neuter SafeVerify entirely.
BANNED = [
    (re.compile(r"^\s*axiom\s", re.MULTILINE), "axiom",
     "`axiom` declarations are not allowed in a submitted statement."),
    (re.compile(r"^\s*unsafe\s", re.MULTILINE), "unsafe",
     "`unsafe` declarations are not allowed."),
    (re.compile(r"\bnative_decide\b"), "native_decide",
     "`native_decide` is not allowed: it trusts compiled code."),
    (re.compile(r"\bimplemented_by\b"), "implemented_by",
     "`implemented_by` is not allowed."),
    (re.compile(r"^\s*#exit\b", re.MULTILINE), "exit",
     "`#exit` is not allowed."),
    (re.compile(r"\bmaxHeartbeats\s+0\b"), "unbounded_heartbeats",
     "`set_option maxHeartbeats 0` is not allowed."),
]


@dataclass
class Rejection:
    code: str
    message: str
    line: Optional[int] = None

    def as_dict(self) -> dict:
        return {"code": self.code, "message": self.message, "line": self.line}


@dataclass
class Declaration:
    name: str
    kind: str
    has_sorry: bool
    wrapped: bool

    def as_dict(self) -> dict:
        return {"name": self.name, "kind": self.kind,
                "has_sorry": self.has_sorry, "wrapped": self.wrapped}


@dataclass
class Prepared:
    ok: bool = False
    normalized_lean: str = ""
    body: str = ""
    blocks: int = 0
    has_sorry: bool = False
    declarations: List[Declaration] = field(default_factory=list)
    errors: List[dict] = field(default_factory=list)
    warnings: List[dict] = field(default_factory=list)
    rejections: List[Rejection] = field(default_factory=list)

    def as_dict(self) -> dict:
        return {
            "ok": self.ok,
            "normalized_lean": self.normalized_lean,
            "blocks": self.blocks,
            "has_sorry": self.has_sorry,
            "declarations": [d.as_dict() for d in self.declarations],
            "errors": self.errors,
            "warnings": self.warnings,
            "rejections": [r.as_dict() for r in self.rejections],
        }


def strip_comments(text: str) -> str:
    """Blank out comments so keyword scanning does not trip over prose.

    Notably, `prover_subagent.py` decides a block is still open by substring-
    matching "sorry", so the word appearing in a comment would keep a block
    open forever. We detect sorries on the comment-stripped text.
    """
    out, i, n = [], 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append(" " if text[i] != "\n" else "\n")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def has_sorry(text: str) -> bool:
    return re.search(r"\bsorry\b", strip_comments(text)) is not None


def hard_rejections(raw: str) -> List[Rejection]:
    """Checks that run before anything is compiled."""
    out: List[Rejection] = []

    if not raw.strip():
        out.append(Rejection("empty", "The submission is empty."))
        return out

    if len(raw) > settings.max_lean_chars:
        out.append(Rejection(
            "too_large",
            f"Submission is {len(raw)} characters; the limit is {settings.max_lean_chars}."))

    for idx, line in enumerate(raw.splitlines(), start=1):
        m = IMPORT_LINE.match(line)
        if m and not ALLOWED_IMPORT.match(m.group(1)):
            out.append(Rejection(
                "bad_import",
                f"Only Mathlib and Init may be imported (found `{m.group(1)}`). "
                "The prover runs with Mathlib already imported.",
                idx))

    stripped = strip_comments(raw)
    for pattern, code, message in BANNED:
        m = pattern.search(stripped)
        if m:
            out.append(Rejection(
                "banned_construct" if code != "axiom" else "banned_axiom",
                message,
                stripped[:m.start()].count("\n") + 1))

    if not re.search(r"\b(theorem|lemma|example)\b", stripped):
        out.append(Rejection(
            "no_theorem",
            "No `theorem`, `lemma`, or `example` found. Submit a statement to prove."))

    return out


def strip_preamble(raw: str) -> str:
    """Remove existing EVOLVE markers and all import lines."""
    text = raw.replace("\r\n", "\n").replace("\r", "\n").lstrip("﻿")
    # User-supplied markers are never trusted: list_evolve_blocks pairs them
    # positionally with no balance check, so a malformed pair would let the
    # model splice over arbitrary code.
    text = MARKER_LINE.sub("", text)
    kept = [line for line in text.split("\n") if not IMPORT_LINE.match(line)]
    return "\n".join(kept).strip("\n")


def _decl_kind_and_name(unit: str):
    m = re.match(r"\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|nonrec\s+)*"
                 r"(theorem|lemma|example|def|abbrev|instance|structure|inductive|class)\b"
                 r"\s*([A-Za-z_α-ω][^\s:({\[]*)?", unit)
    if not m:
        return None, None
    return m.group(1), (m.group(2) or "")


def _wrap_tactic_block(unit: str) -> str:
    """Insert EVOLVE markers around the tactic body of a `:= by` proof.

    Produces exactly the shape the repo already uses (see Challenge.lean):
    markers alone on their own lines at column 1. That is the only layout in
    which both `replace_block_by_id` (which splices whole lines between the
    markers) and the block-retirement code (which blanks len(marker) characters
    from the marker's column) are unambiguous.

    The split point is the end of the *line* containing `by`, not the `by`
    token itself. Tactics already sharing that line stay on it, so the
    indentation of a multi-line tactic block is preserved exactly -- re-indenting
    only the first tactic would misalign it against the rest of the block.
    """
    m = re.search(r":=\s*by\b", unit)
    if not m:
        return unit

    # Preserve whatever whitespace separated this command from the next one;
    # without it the END marker comments out the following declaration.
    stripped = unit.rstrip()
    trailing = unit[len(stripped):] or "\n"
    if not trailing.startswith("\n"):
        trailing = "\n" + trailing

    newline = stripped.find("\n", m.end())
    if newline == -1:
        # Everything is on the `by` line: move the tactics down one line.
        head = stripped[:m.end()]
        body = stripped[m.end():].strip()
        body = f"  {body}" if body else "  sorry"
    else:
        head = stripped[:newline]
        body = stripped[newline + 1:]
        if not body.strip():
            body = "  sorry"

    return f"{head}\n{BLOCK_START}\n{body}\n{BLOCK_END}{trailing}"


def rewrite_unit(unit: str, index: int, inject_markers: bool):
    """Return (new_text, Declaration|None, Rejection|None)."""
    kind, name = _decl_kind_and_name(unit)
    if kind is None:
        return unit, None, None

    text = unit
    unit_has_sorry = has_sorry(text)

    if kind in ("def", "abbrev", "instance") and unit_has_sorry:
        return unit, None, Rejection(
            "sorry_in_def",
            f"`{kind} {name}` contains `sorry`. Definitions in the statement must be complete; "
            "only theorems may be left unproved.")

    if kind not in DECL_KEYWORDS:
        return unit, Declaration(name, kind, False, False), None

    if kind == "example":
        # An `example` produces no named constant, and SafeVerify matches
        # declarations by name -- an anonymous one makes the anti-cheat gate
        # vacuous. Give it a name.
        name = f"user_thm_{index}"
        text = re.sub(r"\bexample\b", f"theorem {name}", text, count=1)
        kind = "theorem"

    stripped = strip_comments(text)

    if ":=" not in stripped:
        # Bare statement, no proof at all.
        text = text.rstrip() + " := by"
        unit_has_sorry = False
    elif re.search(r":=\s*sorry\s*$", stripped):
        # Term-mode sorry -> tactic mode, so there is a block to edit.
        text = re.sub(r":=\s*sorry\s*$", ":= by\n  sorry", text.rstrip())
        unit_has_sorry = True
    elif not re.search(r":=\s*by\b", stripped):
        if unit_has_sorry:
            return unit, None, Rejection(
                "unsupported_proof_shape",
                f"`{name}` uses a term-mode proof containing `sorry`. "
                "Write the statement as `:= by sorry` instead.")
        # A complete term-mode proof: nothing to do.
        return text, Declaration(name, kind, False, False), None

    if re.search(r":=\s*by\s*$", text.rstrip()):
        text = text.rstrip() + "\n  sorry"
        unit_has_sorry = True

    if not unit_has_sorry:
        # Already a complete tactic proof; leave it closed.
        return text, Declaration(name, kind, False, False), None

    if inject_markers:
        text = _wrap_tactic_block(text)

    return text, Declaration(name, kind, True, inject_markers), None


async def prepare(raw: str, mode: str, checker) -> Prepared:
    """Normalize, then compile, a user submission.

    mode "lean"  -> inject EVOLVE markers (prover_subagent.py requires them)
    mode "nl"    -> no markers (whole_proof_subagent.py rewrites the whole file)
    """
    result = Prepared()

    result.rejections = hard_rejections(raw)
    if result.rejections:
        return result

    body = strip_preamble(raw)
    inject = (mode == "lean")

    probe = await checker.compile(body)

    encoded = body.encode("utf-8")
    spans = probe.units or [{"i_begin": 0, "i_end": len(encoded)}]

    pieces: List[str] = []
    cursor = 0
    for i, span in enumerate(spans):
        begin, end = span.get("i_begin", 0), span.get("i_end", 0)
        if begin < cursor or end > len(encoded) or end < begin:
            continue
        if begin > cursor:  # whitespace between commands
            pieces.append(encoded[cursor:begin].decode("utf-8", "replace"))
        unit = encoded[begin:end].decode("utf-8", "replace")
        cursor = end

        new_text, decl, rejection = rewrite_unit(unit, i, inject)
        if rejection:
            result.rejections.append(rejection)
        if decl:
            result.declarations.append(decl)
        pieces.append(new_text)

    if cursor < len(encoded):
        pieces.append(encoded[cursor:].decode("utf-8", "replace"))

    if result.rejections:
        return result

    new_body = "".join(pieces).strip("\n")
    result.body = new_body
    result.normalized_lean = f"{HEADER}\n\n{new_body}\n"
    result.blocks = new_body.count(BLOCK_START)
    result.has_sorry = has_sorry(new_body)

    verify = await checker.compile(new_body)
    result.errors = verify.errors
    result.warnings = verify.warnings

    if not verify.ok:
        result.ok = False
        return result

    if not result.has_sorry:
        result.rejections.append(Rejection(
            "already_complete",
            "This statement already compiles with no `sorry` -- there is nothing left to prove."))
        return result

    if inject and result.blocks == 0:
        result.rejections.append(Rejection(
            "zero_blocks",
            "Could not find a tactic proof to work on. Write the statement as "
            "`theorem name : statement := by sorry`."))
        return result

    result.ok = True
    return result
