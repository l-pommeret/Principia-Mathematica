"""The witness's LaTeX must become PM's notation, or fail visibly."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from latex_to_diplomatic import convert  # noqa: E402


class ConnectiveTests(unittest.TestCase):
    def test_assertion_and_connectives(self) -> None:
        self.assertEqual(
            convert(r"\(\vdash\colon p\supset q.\equiv.\sim p\lor q\)"),
            "⊢: p⊃ q.≡.∼ p∨ q",
        )

    def test_scope_dots_survive(self) -> None:
        # PM's punctuation carries the logical structure; losing the hierarchy
        # of `::`, `:.`, `:`, `.` would lose the proposition.
        rendered = convert(r"\(\vdash\colon\colon p.\supset\colon\ldotp q.\supset.r\)")
        self.assertEqual(rendered, "⊢:: p.⊃:. q.⊃.r")


class CombiningMarkTests(unittest.TestCase):
    def test_converse_mark(self) -> None:
        self.assertEqual(convert(r"\(\breve{R}\)"), "Ř")

    def test_class_abstraction_circumflex(self) -> None:
        self.assertEqual(convert(r"\(\hat{z}\)"), "ẑ")

    def test_dotted_operator(self) -> None:
        self.assertEqual(convert(r"\(\dot{\exists}\)"), "∃̇")


class StructureTests(unittest.TestCase):
    def test_substitution_bracket_is_a_solidus(self) -> None:
        # PM sets its substitution bracket as a fraction: the substituted terms
        # above the variables they replace.
        self.assertEqual(convert(r"\(\frac{S,\breve{S}}{Q,R}\)"), "S,Š/Q,R")

    def test_nested_fractions(self) -> None:
        self.assertEqual(convert(r"\(\frac{\frac{a}{b}}{c}\)"), "a/b/c")

    def test_pm_braces_are_kept(self) -> None:
        # `\{ \}` are PM's own braces, not LaTeX grouping.
        self.assertEqual(convert(r"\(\sim\{p.q\}\)"), "∼{p.q}")

    def test_grouping_braces_are_dropped(self) -> None:
        self.assertEqual(convert(r"\({\sim}p\)"), "∼p")


class SafetyTests(unittest.TestCase):
    def test_unknown_command_survives_as_a_visible_failure(self) -> None:
        # The converter must never guess: an unmapped command has to remain so
        # the caller can refuse to write a half-converted reading.
        self.assertIn("\\", convert(r"\(\notacommand{x}\)"))

    def test_unicode_escapes_are_resolved(self) -> None:
        self.assertEqual(convert(r"\(\unicode{x2129}\)"), "℩")

    def test_plain_text_is_untouched(self) -> None:
        self.assertEqual(convert("⊢ : p ⊃ ∼p . ⊃ . ∼p"), "⊢ : p ⊃ ∼p . ⊃ . ∼p")


if __name__ == "__main__":
    unittest.main()
