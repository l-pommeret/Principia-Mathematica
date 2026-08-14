"""The certification tier computation must not be foolable by shape alone."""

from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_lean_index import (  # noqa: E402
    judgement_relations,
    normalise_formula,
    normalise_printed,
    reading_types,
)
from verify_certification_tier import (  # noqa: E402
    PREMISED_KINDS,
    _hypothesised_judgements,
    _is_vacuous,
    _statement_formula,
)


class ConditionalDerivationTests(unittest.TestCase):
    """A derivation under an undischarged hypothesis is not a derivation.

    `_statement_formula` searches the whole statement, so it finds the
    judgement of `(h : ⊢ₚ A) : ⊢ₚ B` in the hypothesis and reports the theorem
    as a judgement.  Criterion T12 exists to stop that from certifying.
    """

    def test_a_judgement_hypothesis_is_detected(self) -> None:
        self.assertTrue(_hypothesised_judgements("theorem t (h : ⊢ₚ p) : ⊢ₚ q"))

    def test_the_ramified_judgement_is_detected_too(self) -> None:
        self.assertTrue(_hypothesised_judgements("theorem t (h : ⊢ᵣ A) : ⊢ᵣ B"))

    def test_a_categorical_theorem_has_no_hypothesis(self) -> None:
        statement = (
            "theorem star_2_01 {Γ : PM.RealContext} (p : PM.Elementary Γ) : "
            "⊢ₚ ((p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p)"
        )
        self.assertEqual(_hypothesised_judgements(statement), [])

    def test_ordinary_syntactic_binders_are_not_hypotheses(self) -> None:
        # A formula or a signature argument is data the theorem quantifies over,
        # not a judgement it assumes.
        statement = (
            "theorem star_9_34 (universal : signature.Universal argument 0) "
            "(p : Formula signature real [] 0) : ⊢ᵣ star_9_34_formula universal p"
        )
        self.assertEqual(_hypothesised_judgements(statement), [])

    def test_pm_s_own_rules_may_carry_premises(self) -> None:
        """✱1·1 reads "anything implied by a true elementary proposition is
        true": its premises are the rule, not a debt."""
        self.assertIn("primitive-inference-rule", PREMISED_KINDS)
        self.assertIn("derived-metalinguistic-rule", PREMISED_KINDS)


class NormalisationTests(unittest.TestCase):
    def test_redundant_outer_parentheses_are_peeled(self) -> None:
        self.assertEqual(
            normalise_formula("((p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p)"),
            normalise_formula("(p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p"),
        )

    def test_non_wrapping_parentheses_are_kept(self) -> None:
        # `(a) ⊃ₚ (b)` must not collapse to `a ⊃ₚ b`: the outer parentheses do
        # not wrap the whole expression, so peeling them would equate distinct
        # formulae.
        self.assertNotEqual(normalise_formula("(a) ⊃ₚ (b)"), normalise_formula("a"))

    def test_printed_whitespace_is_collapsed_but_glyphs_survive(self) -> None:
        self.assertEqual(
            normalise_printed("⊢ :  p ⊃ ∼p .  ⊃ . ∼p"), "⊢ : p ⊃ ∼p . ⊃ . ∼p"
        )


class JudgementTests(unittest.TestCase):
    def test_reference_calculus_is_a_judgement_relation(self) -> None:
        self.assertIn("Derivation", judgement_relations())

    def test_structure_certificate_is_not_a_judgement(self) -> None:
        # `Star_11_42Derivation` is a structure whose fields the caller supplies,
        # so it is inhabited without any derivation having taken place.
        self.assertNotIn("Star_11_42Derivation", judgement_relations())

    def test_notation_is_recognised_as_a_judgement(self) -> None:
        found = _statement_formula("(p : Elementary Γ) : ⊢ₚ ((p ∨ₚ p) ⊃ₚ p)")
        self.assertIsNotNone(found)
        assert found is not None
        self.assertEqual(found[0], "⊢ₚ")
        self.assertEqual(normalise_formula(found[1]), normalise_formula("(p ∨ₚ p) ⊃ₚ p"))

    def test_plain_lean_proposition_is_not_a_judgement(self) -> None:
        self.assertIsNone(_statement_formula("(a b : Set α) : Similar a b ↔ Similar b a"))


class ReadingTypeTests(unittest.TestCase):
    def test_elementary_reading_is_accepted(self) -> None:
        self.assertIn("ElementaryReading", reading_types())

    def test_printed_formula_is_not_a_reading_type(self) -> None:
        # It carries no `parsed` field; an earlier windowing bug picked it up
        # from a neighbouring structure's body.
        self.assertNotIn("PrintedFormula", reading_types())


class VacuityTests(unittest.TestCase):
    def test_self_equality_is_vacuous(self) -> None:
        self.assertIsNotNone(
            _is_vacuous(": star_11_42_target φ ψ = star_11_42_target φ ψ", "rfl")
        )

    def test_self_biconditional_is_vacuous(self) -> None:
        self.assertIsNotNone(
            _is_vacuous(": Nc a b ↔ Nc a b", "Iff.rfl")
        )

    def test_identity_on_a_self_implication_is_vacuous(self) -> None:
        self.assertIsNotNone(
            _is_vacuous(": Similar a b → Similar a b", "fun h=>h")
        )

    def test_a_real_statement_is_not_vacuous(self) -> None:
        self.assertIsNone(
            _is_vacuous(": ⊢ₚ ((p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p)", "PM.Derivation.star_1_2 (∼ₚ p)")
        )


class GateBehaviourTests(unittest.TestCase):
    def test_report_mode_exits_zero_and_prints_a_census(self) -> None:
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts/verify_certification_tier.py"), "--report"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("tier census", result.stdout)

    def test_check_and_write_are_mutually_exclusive(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                str(ROOT / "scripts/verify_certification_tier.py"),
                "--check",
                "--write",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
