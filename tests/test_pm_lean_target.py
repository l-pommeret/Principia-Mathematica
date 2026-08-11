import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_lean_target import render_elementary_assertion


class PMLeanTargetTests(unittest.TestCase):
    def test_target_is_generated_from_dot_scoped_statement(self):
        source = """✱2·73. ⊢ : p ⊃ q . ⊃ : p ∨ q ∨ r . ⊃ . q ∨ r [✱2·621·38]
"""
        target = render_elementary_assertion(
            source, "PM.FirstEdition.Volume1.Star2.star_2_73"
        )
        self.assertIn("theorem star_2_73 {Γ} (p q r : PM.Elementary Γ)", target)
        self.assertIn("((p ⊃ₚ q) ⊃ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (q ∨ₚ r)))", target)

    def test_star_3_12_preserves_left_associated_marked_disjunction(self):
        target = render_elementary_assertion(
            "✱3·12.  ⊢ : ∼p . ∨ . ∼q . ∨ . p . q     [✱2·11 (∼p ∨ ∼q)/p]",
            "PM.FirstEdition.Volume1.Star3.star_3_12",
        )
        self.assertIn("(((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ (p ∧ₚ q))", target)
        self.assertNotIn("((∼ₚ p) ∨ₚ ((∼ₚ q) ∨ₚ (p ∧ₚ q)))", target)

    def test_non_elementary_target_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "non-elementary AST node forall"):
            render_elementary_assertion(
                "✱9·2. ⊢ : (x).φx .⊃. φy",
                "PM.FirstEdition.Volume1.Star9.star_9_2",
            )


if __name__ == "__main__":
    unittest.main()
