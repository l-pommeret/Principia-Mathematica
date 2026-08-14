"""A proof must follow the demonstration PM prints, not merely reach its conclusion."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_printed_citations import (  # noqa: E402
    INTERFACE_LEMMAS,
    PRINTED_TITLES,
    _reachable_form,
    cited_propositions,
    used_propositions,
)


class UsageExtractionTests(unittest.TestCase):
    def test_numbered_constants_are_seen(self) -> None:
        term = "fun p => PM.FirstEdition.Volume1.Star2.star_2_05 p"
        self.assertIn("✱2·05", used_propositions("Star9.star_9_1", term))

    def test_the_declarations_own_name_is_not_a_dependency(self) -> None:
        term = "theorem PM.X.star_2_01 : ... := PM.Derivation.star_1_2 p"
        used = used_propositions("PM.X.star_2_01", term)
        self.assertNotIn("✱2·01", used)
        self.assertIn("✱1·2", used)

    def test_the_detachment_interface_counts_as_the_printed_rules(self) -> None:
        # `detach` combines ✱1·1 and ✱1·11 without identifying them; using it is
        # using those rules, which PM leaves implicit in every demonstration.
        used = used_propositions("X.star_2_15", "PM.Derivation.detach a b")
        self.assertEqual(used, INTERFACE_LEMMAS["PM.Derivation.detach"])

    def test_a_printed_title_counts_as_its_number(self) -> None:
        # PM writes `[Taut ∼p/p]`, not `[✱1·2]`.
        used = used_propositions("X.star_2_01", "PM.Derivation.Taut (∼ₚ p)")
        self.assertIn(PRINTED_TITLES["PM.Derivation.Taut"], used)


class CitationReadingTests(unittest.TestCase):
    def test_volume_prefix_is_stripped(self) -> None:
        item = {"printed_dependencies": ["PM1:✱2·05", "PM2:✱100·1"]}
        self.assertEqual(cited_propositions(item), {"✱2·05", "✱100·1"})

    def test_non_numbered_citations_are_ignored(self) -> None:
        # PM also cites by title (`Fact`, `Syll`); those carry no number.
        item = {"printed_dependencies": ["Fact", "PM1:✱3·45"]}
        self.assertEqual(cited_propositions(item), {"✱3·45"})


class CompoundCitationTests(unittest.TestCase):
    def test_a_compound_citation_is_satisfied_by_any_component(self) -> None:
        # PM compresses several numbers into one bracket: `✱5·3·32` cites both
        # ✱5·3 and ✱5·32.  Treating the compound as one missing citation would
        # be a false positive.
        self.assertFalse(_reachable_form("✱5·3·32", {"✱5·3"}))
        self.assertFalse(_reachable_form("✱4·62·51", {"✱4·51"}))

    def test_a_compound_none_of_whose_parts_is_used_still_counts(self) -> None:
        self.assertTrue(_reachable_form("✱5·3·32", {"✱2·05"}))

    def test_a_simple_citation_is_always_judgeable(self) -> None:
        self.assertTrue(_reachable_form("✱4·38", set()))


class DirectionTests(unittest.TestCase):
    def test_the_gate_judges_cited_but_unused_not_the_converse(self) -> None:
        """PM abbreviates, so a term legitimately mentions more than the page.

        The demonstration cites the substantive steps and leaves routine
        transitions implicit — PM says so itself ("this process ... will
        therefore be abbreviated").  So `used - cited` is expected and must not
        fail; `cited - used` means the proof took another route entirely.
        """
        cited = {"✱4·38"}
        used = {"✱1·1", "✱1·11", "✱2·05", "✱3·2"}
        self.assertTrue(cited - used, "the missing citation must be detectable")
        self.assertTrue(used - cited, "extra usage is normal and must be tolerated")


if __name__ == "__main__":
    unittest.main()
