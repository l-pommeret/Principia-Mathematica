import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_context_bundle import build_bundle


class ContextBundleTests(unittest.TestCase):
    def test_real_pm_2_45_bundle_is_minimal_and_provenanced(self):
        from pm_constraint_manifest import compile_manifest, load_item_registry
        from pm_proof_skeleton import parse_demonstration

        registry = load_item_registry(ROOT / "metadata/items")
        skeleton = parse_demonstration(
            "✱2·45. ⊢ : ∼(p ∨ q) . ⊃ . ∼p [✱2·2.Transp.]",
            current_item="PM1:✱2·45",
        )
        manifest = compile_manifest(
            skeleton, registry, global_conventions=["PM1:✱1·11"]
        )
        bundle = build_bundle(manifest, registry, ROOT)
        source = bundle["lean_source"]
        self.assertIn("inductive Elementary", source)
        self.assertIn("inductive Derivation", source)
        self.assertIn("theorem star_2_2", source)
        self.assertIn("theorem star_2_16", source)
        self.assertNotIn("theorem star_2_45", source)
        self.assertNotIn("PM-VERBATIM", source)
        self.assertLess(bundle["source_bytes"], 15000)
        self.assertTrue(bundle["policy"]["grants_no_additional_proof_permission"])
        self.assertEqual(len(bundle["source_sha256"]), 64)

    def test_unknown_context_item_is_rejected(self):
        manifest = {
            "kind": "pm-constrained-prover-manifest",
            "context_closure": ["PM1:✱99·99"],
            "allowed_pm_items": [],
        }
        with self.assertRaisesRegex(ValueError, "unknown context items"):
            build_bundle(manifest, {}, ROOT)

    def test_batch_bundle_contains_external_closure_but_not_local_targets(self):
        from pm_constraint_manifest import compile_batch_manifest, load_item_registry
        from pm_proof_skeleton import parse_demonstration

        registry = load_item_registry(ROOT / "metadata/items")
        first = parse_demonstration(
            "✱2·45. ⊢ : p [✱2·2]", current_item="PM1:✱2·45"
        )
        second = parse_demonstration(
            "✱2·46. ⊢ : p [✱2·45]", current_item="PM1:✱2·46"
        )
        # These IDs already exist in the registry, so use future local IDs in
        # the fixture while retaining a real external dependency.
        first["current_item"] = "PM1:✱8·91"
        second["current_item"] = "PM1:✱8·92"
        second["steps"][0]["events"][0]["normalized_candidates"] = ["PM1:✱8·91"]
        batch = compile_batch_manifest(
            [first, second], registry,
            {"PM1:✱8·91": "PM.Test.star_8_91", "PM1:✱8·92": "PM.Test.star_8_92"},
        )
        bundle = build_bundle(batch, registry, ROOT)
        self.assertIn("theorem star_2_2", bundle["lean_source"])
        self.assertNotIn("star_8_91", bundle["lean_source"])
        self.assertEqual(bundle["target_order"], ["PM1:✱8·91", "PM1:✱8·92"])


if __name__ == "__main__":
    unittest.main()
