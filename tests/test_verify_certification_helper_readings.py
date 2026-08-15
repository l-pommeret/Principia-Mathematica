"""Regression coverage for T4 readings built through local helpers."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_lean_index import Declaration  # noqa: E402
import verify_certification_tier as gate  # noqa: E402


class HelperReadingTests(unittest.TestCase):
    def test_helper_reading_is_audited_before_its_arguments_count(self) -> None:
        path = "Principia/Example.lean"
        theorem = Declaration(
            "example",
            "theorem",
            path,
            1,
            ": ⊢ₚ (p ⊃ₚ q)",
            "some_derivation",
        )
        helper = Declaration(
            "make_reading",
            "def",
            path,
            2,
            "(printed : String) (formula : Formula signature real [] order) : "
            "ClaimReading signature real",
            """
  printed := printed
  parsed := .assertion formula
""",
        )
        item = {
            "id": "PM1:✱example",
            "kind": "derived-proposition",
            "printed": "⊢ : p ⊃ q",
            "lean_path": path,
            "declaration": "PM.example",
            "formal_status": gate.TIER_TYPECHECKED,
            "formalization_level": gate.REQUIRED_FORMALIZATION_LEVEL,
        }

        def result(printed: str, current_helper: Declaration) -> tuple[list[str], str]:
            reading = Declaration(
                "example_reading",
                "def",
                path,
                3,
                "(p q : Elementary Γ)",
                f'make_reading "{printed}" (p ⊃ₚ q)',
            )
            index = {
                theorem.name: theorem,
                reading.name: reading,
                current_helper.name: current_helper,
            }
            with (
                mock.patch.object(gate, "import_closure", return_value=frozenset({path})),
                mock.patch.object(gate, "declarations", return_value=index),
            ):
                _tier, failed, notes = gate.compute(item, [])
            return failed, notes.get("T4", "")

        with self.subTest("matching catalogue string"):
            failed, note = result("⊢ : p ⊃ q", helper)
            self.assertNotIn("T4", failed, note)

        with self.subTest("different catalogue string"):
            failed, note = result("⊢ : q ⊃ p", helper)
            self.assertIn("T4", failed)
            self.assertIn("printed reading differs from the catalogue", note)

        with self.subTest("helper does not construct a true reading"):
            false_helper = Declaration(
                helper.name,
                helper.kind,
                helper.path,
                helper.line,
                helper.statement,
                helper.body.replace(
                    "printed := printed",
                    'printed := "unrelated"',
                ),
            )
            failed, note = result("⊢ : p ⊃ q", false_helper)
            self.assertIn("T4", failed)
            self.assertIn("reading helper `make_reading` does not forward printed", note)


if __name__ == "__main__":
    unittest.main()
