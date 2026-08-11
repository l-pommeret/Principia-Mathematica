import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import pm_proof_skeleton as skeleton


class PMProofSkeletonTests(unittest.TestCase):
    def test_aliases_are_loaded_from_editorial_registry(self):
        self.assertEqual(
            skeleton.PRINTED_ALIASES["Transp"], ["PM1:✱2·16", "PM1:✱2·17"]
        )
        self.assertIn("Syll", skeleton.ALIAS_REGISTRY["historical_scopes"])

    def test_inline_bracket_is_a_demonstration_step(self):
        result = skeleton.parse_demonstration(
            "✱2·45. ⊢ : ∼(p ∨ q) . ⊃ . ∼p [✱2·2.Transp.]",
            current_item="PM1:✱2·45",
        )
        self.assertEqual(len(result["steps"]), 1)
        self.assertEqual(
            [event["printed"] for event in result["steps"][0]["events"]],
            ["✱2·2", "Transp"],
        )

    def test_compressed_reference_expands_without_losing_printed_form(self):
        self.assertEqual(skeleton.expand_reference("✱4·84·85"),
                         ["PM1:✱4·84", "PM1:✱4·85"])

    def test_ordered_events_alias_substitution_and_line_labels(self):
        source = """
Dem.
⊢ . ✱4·1 . ⊃ ⊢ :. p ⊃ q . ≡ . ∼q ⊃ ∼p                         (1)
⊢ . (1) . ✱4·71 [∼q,∼p / p,q] . Transp . ⊃ ⊢ . Prop            (2)
"""
        parsed = skeleton.parse_demonstration(source)
        self.assertEqual(len(parsed["steps"]), 2)
        second = parsed["steps"][1]
        self.assertEqual([event["kind"] for event in second["events"]],
                         ["line-reference", "printed-reference", "printed-alias"])
        self.assertEqual(second["substitutions"], ["∼q,∼p / p,q"])
        self.assertEqual(second["uses_lines"], ["1"])
        self.assertEqual(second["produces_line"], "2")

    def test_known_aliases_resolve_to_reviewed_candidates(self):
        parsed = skeleton.parse_step(
            "⊢ . Simp . Syll . Comp . ⊃ ⊢ . Prop", current_item="PM1:✱5·3"
        )
        aliases = {event["printed"]: event["normalized_candidates"]
                   for event in parsed["events"]}
        self.assertEqual(aliases["Simp"], ["PM1:✱3·26", "PM1:✱3·27"])
        self.assertEqual(aliases["Syll"], ["PM1:✱3·33", "PM1:✱3·34"])
        self.assertEqual(aliases["Comp"], ["PM1:✱3·43"])

    def test_syll_resolution_is_locus_sensitive(self):
        early = skeleton.parse_step("⊢ . Syll . ⊃ ⊢ . Prop",
                                    current_item="PM1:✱2·44")
        late = skeleton.parse_step("⊢ . Syll . ⊃ ⊢ . Prop",
                                   current_item="PM1:✱5·3")
        unknown = skeleton.parse_step("⊢ . Syll . ⊃ ⊢ . Prop")
        self.assertEqual(early["events"][0]["normalized_candidates"],
                         ["PM1:✱2·05", "PM1:✱2·06"])
        self.assertEqual(late["events"][0]["normalized_candidates"],
                         ["PM1:✱3·33", "PM1:✱3·34"])
        self.assertEqual(unknown["events"][0]["resolution_status"], "locus-required")

    def test_continuation_citation_line_stays_in_same_step(self):
        source = """
⊢ . ✱3·26 . ⊃ ⊢ : p · q . ⊃ . p
[✱2·43]          ⊃ ⊢ : p . ⊃ . p · p                    (1)
"""
        parsed = skeleton.parse_demonstration(source)
        self.assertEqual(len(parsed["steps"]), 1)
        references = [event["printed"] for event in parsed["steps"][0]["events"]
                      if event["kind"] == "printed-reference"]
        self.assertEqual(references, ["✱3·26", "✱2·43"])

    def test_reviewed_reference_override_preserves_diplomatic_reading(self):
        parsed = skeleton.parse_demonstration(
            "⊢ . (2) . (✱3·03) . ⊃ ⊢ . Prop",
            current_item="PM1:✱3·03",
        )
        corrected = skeleton.apply_reference_overrides(parsed, [{
            "printed": "✱3·03",
            "replacement": "PM1:✱3·01",
            "reason": "printed circular reference; definition required",
        }])
        event = corrected["steps"][0]["events"][1]
        self.assertEqual(event["printed"], "✱3·03")
        self.assertEqual(event["diplomatic_candidates"], ["PM1:✱3·03"])
        self.assertEqual(event["normalized_candidates"], ["PM1:✱3·01"])
        self.assertEqual(event["resolution_status"], "reviewed-source-correction")


if __name__ == "__main__":
    unittest.main()
