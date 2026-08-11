import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from pm_constraint_audit import ReconstructionAuditError, classify_reconstruction


MANIFEST = {
    "kind": "pm-constrained-prover-manifest",
    "current_item": "PM1:✱2·61",
    "allowed_pm_items": ["PM1:✱2·04", "PM1:✱2·6"],
    "proof_permissions": [
        {"step": 1, "event": 1, "printed": "✱2·6", "candidates": ["PM1:✱2·6"]},
        {"step": 1, "event": 2, "printed": "Comm", "candidates": ["PM1:✱2·04"]},
    ],
}


class ConstraintAuditTests(unittest.TestCase):
    def test_strict_closure_covers_every_printed_event(self):
        audit = classify_reconstruction(MANIFEST, ["PM1:✱2·6", "PM1:✱2·04"])
        self.assertEqual(audit["classification"], "strict-closure")
        self.assertTrue(audit["faithful_by_printed_dependency_constraint"])

    def test_relaxation_records_only_added_items(self):
        audit = classify_reconstruction(
            MANIFEST, ["PM1:✱2·6", "PM1:✱2·04", "PM1:✱2·05"]
        )
        self.assertEqual(audit["classification"], "relaxed-closure")
        self.assertEqual(audit["added_beyond_print"], ["PM1:✱2·05"])

    def test_unused_printed_citation_is_not_called_strict_closure(self):
        audit = classify_reconstruction(MANIFEST, ["PM1:✱2·6"])
        self.assertEqual(
            audit["classification"], "strict-subset-with-unused-printed-citations"
        )
        self.assertEqual(audit["uncovered_printed_events"][0]["printed"], "Comm")

    def test_alias_family_needs_only_one_candidate(self):
        manifest = dict(MANIFEST)
        manifest["allowed_pm_items"] = ["PM1:✱2·16", "PM1:✱2·17"]
        manifest["proof_permissions"] = [
            {"step": 1, "event": 1, "printed": "Transp",
             "candidates": ["PM1:✱2·16", "PM1:✱2·17"]}
        ]
        audit = classify_reconstruction(manifest, ["PM1:✱2·17"])
        self.assertEqual(audit["classification"], "strict-closure")

    def test_documented_relaxation_is_never_reported_as_strict(self):
        manifest = dict(MANIFEST)
        manifest["policy"] = {"strict": False}
        manifest["allowed_pm_items"] = ["PM1:✱2·04", "PM1:✱2·6", "PM1:✱2·05"]
        manifest["documented_relaxations"] = ["PM1:✱2·05"]
        audit = classify_reconstruction(
            manifest, ["PM1:✱2·6", "PM1:✱2·04", "PM1:✱2·05"]
        )
        self.assertEqual(audit["classification"], "documented-relaxed-closure")
        self.assertEqual(audit["approved_relaxations_used"], ["PM1:✱2·05"])
        self.assertFalse(audit["faithful_by_printed_dependency_constraint"])

    def test_duplicate_used_item_is_rejected(self):
        with self.assertRaisesRegex(ReconstructionAuditError, "unique"):
            classify_reconstruction(MANIFEST, ["PM1:✱2·6", "PM1:✱2·6"])


if __name__ == "__main__":
    unittest.main()
