"""Positive controls for every escape hatch the policy gate must reject."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_lean_policy import (  # noqa: E402
    FORBIDDEN,
    code_without_comments_or_strings,
    scanned_paths,
)


def detects(snippet: str) -> bool:
    return bool(FORBIDDEN.search(code_without_comments_or_strings(snippet)))


class EscapeHatchTests(unittest.TestCase):
    def test_sorry_ax_is_detected(self) -> None:
        # `\bsorry\b` cannot match `sorryAx`, so the original pattern let this
        # through while `lake env lean` exited 0.
        self.assertTrue(detects("theorem t : P := sorryAx _ false"))

    def test_bare_sorry_is_detected(self) -> None:
        self.assertTrue(detects("theorem t : P := by sorry"))

    def test_axiom_behind_an_attribute_is_detected(self) -> None:
        self.assertTrue(detects("@[simp] axiom foo : P"))

    def test_axiom_behind_a_modifier_is_detected(self) -> None:
        self.assertTrue(detects("private axiom foo : P"))

    def test_unsafe_and_partial_definitions_are_detected(self) -> None:
        self.assertTrue(detects("unsafe def f : Nat := 0"))
        self.assertTrue(detects("partial def f : Nat := 0"))

    def test_native_decide_is_detected(self) -> None:
        self.assertTrue(detects("theorem t : P := by native_decide"))

    def test_opaque_and_implemented_by_are_detected(self) -> None:
        self.assertTrue(detects("opaque f : Nat"))
        self.assertTrue(detects("@[implemented_by g] def f : Nat := 0"))


class HistoricalProseTests(unittest.TestCase):
    def test_transcribed_prose_is_exempt(self) -> None:
        # PM's Introduction contains the words "admit" and "axiom"; those files
        # must keep passing.
        prose = (
            "/- we must admit (what seems impossible) that the axiom holds -/\n"
            "theorem t : P := trivial"
        )
        self.assertFalse(detects(prose))

    def test_string_literals_are_exempt(self) -> None:
        self.assertFalse(detects('def s : String := "sorry"'))


class ScopeTests(unittest.TestCase):
    def test_prover_context_tree_is_scanned(self) -> None:
        # `.github/workflows/lean.yml` kernel-checks aristotle/contexts/*.lean,
        # which the previous walk never inspected.
        scanned = {path.as_posix() for path in scanned_paths()}
        self.assertTrue(
            any("aristotle/" in path for path in scanned),
            "the prover-context tree is not scanned",
        )
        self.assertTrue(any(path.endswith("Principia.lean") for path in scanned))


class StripperTests(unittest.TestCase):
    def test_line_numbers_are_preserved(self) -> None:
        source = "-- comment\n/- block\nblock -/\ntheorem t : P := trivial\n"
        stripped = code_without_comments_or_strings(source)
        self.assertEqual(source.count("\n"), stripped.count("\n"))

    def test_nested_block_comments_close_correctly(self) -> None:
        source = "/- outer /- inner -/ still outer -/ axiom foo : P"
        self.assertTrue(detects(source))


if __name__ == "__main__":
    unittest.main()
