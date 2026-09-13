"""Normalizer fixtures. Requires a working Lean toolchain (uses a real checker)."""

import asyncio, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from server.lean.checkers import Checker
from server.lean.normalize import prepare, BLOCK_START, BLOCK_END, has_sorry, strip_comments

CASES = [
    # (name, input, mode, expect_ok, expect_blocks, expect_rejection_code)
    ("bare statement", "theorem foo : 1 + 1 = 2", "lean", True, 1, None),
    ("by sorry", "theorem foo : 1 + 1 = 2 := by sorry", "lean", True, 1, None),
    ("trailing by", "theorem foo : 1 + 1 = 2 := by", "lean", True, 1, None),
    ("term sorry", "theorem foo : 1 + 1 = 2 := sorry", "lean", True, 1, None),
    ("unicode", "theorem u (n : ℕ) : n + 0 = n := by sorry", "lean", True, 1, None),
    ("multi-line proof",
     "theorem foo (n : ℕ) : n + 0 = n := by\n  induction n with\n  | zero => sorry\n  | succ k ih => sorry",
     "lean", True, 1, None),
    ("two theorems",
     "theorem a1 : True := by sorry\n\ntheorem a2 : False ∨ True := by sorry",
     "lean", True, 2, None),
    ("theorem plus def",
     "def dbl (n : ℕ) : ℕ := 2 * n\n\ntheorem t : dbl 2 = 4 := by sorry",
     "lean", True, 1, None),
    ("example renamed", "example : 1 + 1 = 2 := by sorry", "lean", True, 1, None),
    ("user imports stripped",
     "import Mathlib\nimport Mathlib.Tactic\n\ntheorem foo : 1 + 1 = 2 := by sorry",
     "lean", True, 1, None),
    ("pre-existing markers",
     "theorem foo : 1 + 1 = 2 := by\n-- EVOLVE-BLOCK-START\n  sorry\n-- EVOLVE-BLOCK-END",
     "lean", True, 1, None),
    ("unbalanced markers",
     "theorem foo : 1 + 1 = 2 := by\n-- EVOLVE-BLOCK-END\n  sorry\n-- EVOLVE-BLOCK-END",
     "lean", True, 1, None),
    ("nl mode gets no markers", "theorem foo : 1 + 1 = 2 := by sorry", "nl", True, 0, None),
    # rejections
    ("already complete", "theorem foo : 1 + 1 = 2 := by norm_num", "lean", False, 0, "already_complete"),
    ("no theorem", "def f (n : ℕ) : ℕ := n", "lean", False, 0, "no_theorem"),
    ("bad import", "import Lean.Elab\ntheorem foo : True := by sorry", "lean", False, 0, "bad_import"),
    ("axiom", "axiom cheat : False\ntheorem foo : True := by sorry", "lean", False, 0, "banned_axiom"),
    ("native_decide", "theorem foo : True := by native_decide", "lean", False, 0, "banned_construct"),
    ("unsafe", "unsafe def f : Nat := 0\ntheorem foo : True := by sorry", "lean", False, 0, "banned_construct"),
    ("sorry in def", "def f : ℕ := sorry\ntheorem foo : f = 0 := by sorry", "lean", False, 0, "sorry_in_def"),
    ("empty", "   ", "lean", False, 0, "empty"),
    ("does not compile", "theorem foo : (1 : ℕ) = (True : Prop) := by sorry", "lean", False, 0, None),
    ("syntax error", "theorem foo : 1 + = 2 := by sorry", "lean", False, 0, None),
]


def test_pure_helpers():
    fails = []
    if has_sorry("-- this mentions sorry in a comment\ntheorem t : True := trivial"):
        fails.append("comment-only 'sorry' must not count as a sorry")
    if not has_sorry("theorem t : True := by sorry"):
        fails.append("real sorry must be detected")
    if has_sorry("/- block\n sorry\n-/\ntheorem t : True := trivial"):
        fails.append("block-comment 'sorry' must not count")
    if strip_comments("a -- b\nc").splitlines()[0].rstrip() != "a":
        fails.append("line comment not stripped")
    return fails


async def main() -> int:
    print("pure helpers:")
    fails = test_pure_helpers()
    for f in fails:
        print(f"  FAIL {f}")
    if not fails:
        print("  ok  4 checks")

    checker = Checker(0)
    await checker.start()
    print("\nfixtures:")

    bad = list(fails)
    for name, src, mode, want_ok, want_blocks, want_reject in CASES:
        got = await prepare(src, mode, checker)
        codes = [r.code for r in got.rejections]
        problems = []
        if got.ok != want_ok:
            problems.append(f"ok={got.ok} want {want_ok} (errors={got.errors[:1]}, rej={codes})")
        if want_ok and got.blocks != want_blocks:
            problems.append(f"blocks={got.blocks} want {want_blocks}")
        if want_reject and want_reject not in codes:
            problems.append(f"rejections={codes} want {want_reject!r}")
        if want_ok:
            if got.normalized_lean.count(BLOCK_START) != got.normalized_lean.count(BLOCK_END):
                problems.append("unbalanced markers in output")
            if not got.normalized_lean.startswith("import Mathlib"):
                problems.append("missing import header")
            if mode == "lean" and got.blocks and BLOCK_START + "\n" not in got.normalized_lean:
                problems.append("marker not alone on its line")

        if problems:
            bad.append(name)
            print(f"  FAIL {name}: {'; '.join(problems)}")
        else:
            print(f"  ok   {name}")

    await checker.stop()
    print(f"\n{len(CASES) + 4 - len(bad)}/{len(CASES) + 4} passed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
