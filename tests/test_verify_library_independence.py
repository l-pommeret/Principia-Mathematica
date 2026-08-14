"""PM's system must stand on its own primitives; Lean is only the metalanguage."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_library_independence import (  # noqa: E402
    CORE_TREES,
    LIBRARY_TACTICS,
    _strip_comments,
    REMEDY,
    core_files,
    declared_names,
    tactic_findings,
)


def _lean(body: str) -> Path:
    handle = tempfile.NamedTemporaryFile(
        "w", suffix=".lean", delete=False, encoding="utf-8"
    )
    handle.write(body)
    handle.close()
    return Path(handle.name)


class TacticDetectionTests(unittest.TestCase):
    def test_a_library_tactic_is_reported(self) -> None:
        path = _lean("theorem t : True := by simp\n")
        self.assertEqual(len(tactic_findings([path])), 1)

    def test_every_listed_tactic_is_detected(self) -> None:
        for tactic in LIBRARY_TACTICS:
            path = _lean(f"theorem t : True := by {tactic}\n")
            self.assertTrue(
                tactic_findings([path]), f"`{tactic}` must be detected"
            )

    def test_an_explicit_proof_is_clean(self) -> None:
        # This is what a purified proof looks like: no library consulted.
        path = _lean(
            "theorem natMaxSelf : ∀ n : Nat, max n n = n\n"
            "  | 0 => rfl\n"
            "  | Nat.succ n => congrArg Nat.succ (natMaxSelf n)\n"
        )
        self.assertEqual(tactic_findings([path]), [])

    def test_a_tactic_named_in_prose_is_not_a_finding(self) -> None:
        """The gate reads code, not commentary.

        `Nat.max_self` is proved in the library through the simplifier, so it
        carries `propext`; saying so in a docstring must not itself fail.
        """
        path = _lean(
            "/-- `Nat.max_self` is proved by simp upstream and so carries\n"
            "`propext`; we reprove it here. -/\n"
            "theorem t : True := trivially_named\n"
            "-- avoid simp here\n"
        )
        self.assertEqual(tactic_findings([path]), [])

    def test_an_identifier_merely_containing_a_tactic_name_is_not_a_finding(
        self,
    ) -> None:
        # `simpleOrder` and `Formula.decideScope` are names, not tactic calls.
        path = _lean(
            "def simpleOrder : Nat := 0\n"
            "def Formula.decideScope : Nat := 0\n"
            "theorem t : simpleOrder = 0 := rfl\n"
        )
        self.assertEqual(tactic_findings([path]), [])

    def test_a_simp_attribute_is_not_a_discharged_goal(self) -> None:
        """`@[simp]` only tags a lemma for someone else's simp set."""
        path = _lean("@[simp] theorem t : True := True.intro\n")
        self.assertEqual(tactic_findings([path]), [])


class CommentStrippingTests(unittest.TestCase):
    def test_nested_block_comments_are_removed(self) -> None:
        self.assertNotIn("simp", _strip_comments("/- outer /- inner simp -/ -/ rfl"))

    def test_code_after_a_comment_survives(self) -> None:
        self.assertIn("rfl", _strip_comments("-- a note\nrfl"))


class DeclarationScanTests(unittest.TestCase):
    def test_names_are_qualified_by_their_namespace(self) -> None:
        path = _lean(
            "namespace PM.RamifiedSyntax\n\n"
            "theorem star_9_34 : True := True.intro\n\n"
            "end PM.RamifiedSyntax\n"
        )
        self.assertIn("PM.RamifiedSyntax.star_9_34", declared_names([path]))

    def test_definitions_are_audited_too(self) -> None:
        """The gap this gate exists to close.

        `Nat.max_self` reached every ramified connective through `implication`,
        which is a `def`. Auditing only theorems would miss the carrier.
        """
        path = _lean("def implication : Nat := 0\n")
        self.assertIn("implication", declared_names([path]))


class ScopeTests(unittest.TestCase):
    def test_the_object_calculus_is_what_is_audited(self) -> None:
        self.assertEqual(CORE_TREES, ("Principia/Syntax", "Principia/Deduction"))

    def test_the_scope_is_not_empty_in_this_repository(self) -> None:
        # A gate that silently audits nothing would pass vacuously.
        self.assertTrue(core_files())


class RemedyTests(unittest.TestCase):
    """The failure message must name the trap, not just the symptom.

    Seven declarations here depended on `propext` without mentioning Lean's
    library once: the carrier was the structural recursion compiler, whose
    `brecOn` and generated matchers depend on it. An author reading only
    "depends on propext" hunts for a borrowed lemma and finds none.
    """

    def test_the_message_points_at_structural_recursion_first(self) -> None:
        self.assertIn("brecOn", REMEDY)
        self.assertIn("match", REMEDY)

    def test_the_message_names_the_primitive_recursors(self) -> None:
        self.assertIn("Nat.rec", REMEDY)
        self.assertIn("casesOn", REMEDY)

    def test_the_message_also_covers_the_borrowed_lemma_case(self) -> None:
        # `Nat.max_self` is proved upstream by the simplifier and so carries
        # `propext`; the cure there is to reprove it locally.
        self.assertIn("Nat.max_self", REMEDY)


if __name__ == "__main__":
    unittest.main()
