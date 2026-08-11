import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_context_bundle import build_bundle, interface_stub, preserve_historical_container_hashes


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

    def test_interface_stub_is_an_axiom_for_a_proof_target(self):
        from pm_constraint_manifest import load_item_registry

        stub, signature = interface_stub(
            load_item_registry(ROOT / "metadata/items")["PM1:✱3·37"], ROOT
        )
        self.assertTrue(stub.lstrip().startswith("axiom star_3_37"))
        self.assertTrue(signature.lstrip().startswith("theorem star_3_37"))

    def test_interface_syntax_precedes_a_dependent_stub(self):
        from pm_constraint_manifest import load_item_registry

        manifest = json.loads((ROOT / "aristotle/manifests/Q228.json").read_text())
        source = build_bundle(
            manifest, load_item_registry(ROOT / "metadata/items"), ROOT
        )["lean_source"]
        target = (
            "axiom star_4_13"
            if "axiom star_4_13" in source
            else "theorem star_4_13"
        )
        self.assertLess(
            source.index('infix:53 " ≡ₚ "'),
            source.index(target),
        )

    def test_q230_interface_closure_contains_equiv_chain(self):
        from pm_constraint_manifest import load_item_registry

        manifest = json.loads((ROOT / "aristotle/manifests/Q230.json").read_text())
        source = build_bundle(
            manifest, load_item_registry(ROOT / "metadata/items"), ROOT
        )["lean_source"]
        self.assertLess(source.index("axiom equivChain"), source.index("axiom star_4_22"))

    def test_formation_profile_contains_separate_judgement(self):
        manifest = {
            "kind": "pm-constrained-prover-manifest",
            "foundation_profile": "elementary-formation-pm1",
            "context_closure": [],
            "allowed_pm_items": [],
        }
        bundle = build_bundle(manifest, {}, ROOT)
        self.assertEqual(bundle["profile"], "elementary-formation-pm1")
        self.assertIn("inductive Formation", bundle["lean_source"])
        self.assertIn("structure FormedDerivation", bundle["lean_source"])

    def test_description_profile_contains_de_bruijn_scope_without_term_description(self):
        manifest = {
            "kind": "pm-constrained-prover-manifest",
            "foundation_profile": "description-scope-pm1",
            "context_closure": [],
            "allowed_pm_items": [],
        }
        bundle = build_bundle(manifest, {}, ROOT)
        self.assertEqual(bundle["profile"], "description-scope-pm1")
        self.assertIn("inductive Var", bundle["lean_source"])
        self.assertIn("| descriptionScope :", bundle["lean_source"])
        term_region = bundle["lean_source"].split("inductive Term", 1)[1].split(
            "inductive Arguments", 1
        )[0]
        self.assertNotIn("description", term_region.lower())

    def test_description_definitions_profile_adds_only_reductional_scope_forms(self):
        manifest = {
            "kind": "pm-constrained-prover-manifest",
            "foundation_profile": "description-definitions-pm1",
            "context_closure": [],
            "allowed_pm_items": [],
        }
        bundle = build_bundle(manifest, {}, ROOT)
        source = bundle["lean_source"]
        self.assertIn("def descriptionExists", source)
        self.assertIn("def descriptionScopePair", source)
        self.assertIn("def laterDescriptionOuterScope", source)
        self.assertNotIn("namespace PM.Experimental", source)

    def test_local_architecture_context_is_hashed_without_proof_permission(self):
        manifest = {
            "kind": "pm-constrained-prover-manifest",
            "foundation_profile": "ordered-first-order-pm1",
            "context_closure": [],
            "allowed_pm_items": [],
            "policy": {"interface_gated": True},
            "local_context_paths": ["Principia/Architecture/FirstOrderQ259.lean"],
        }
        bundle = build_bundle(manifest, {}, ROOT)
        local = [
            source for source in bundle["sources"]
            if source["kind"] == "local-architecture-context"
        ]
        self.assertEqual(len(local), 1)
        self.assertEqual(local[0]["path"], "Principia/Architecture/FirstOrderQ259.lean")
        self.assertEqual(len(local[0]["source_sha256"]), 64)
        self.assertFalse(local[0]["grants_proof_permission"])
        self.assertIn("def star_9_3_target", bundle["lean_source"])

    def test_local_architecture_context_requires_interface_gate(self):
        manifest = {
            "kind": "pm-constrained-prover-manifest",
            "context_closure": [],
            "allowed_pm_items": [],
            "local_context_paths": ["Principia/Architecture/FirstOrderQ259.lean"],
        }
        with self.assertRaisesRegex(ValueError, "requires interface-gated policy"):
            build_bundle(manifest, {}, ROOT)

    def test_parent_traversal_is_rejected_for_local_architecture_context(self):
        manifest = {
            "kind": "pm-constrained-prover-manifest",
            "context_closure": [],
            "allowed_pm_items": [],
            "policy": {"interface_gated": True},
            "local_context_paths": ["../outside.lean"],
        }
        with self.assertRaisesRegex(ValueError, "invalid local context path"):
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

    def test_preserved_hashes_tolerate_a_reviewed_bundle_expansion(self):
        recorded = {"sources": [
            {"kind": "item-declaration", "id": "PM1:✱2·1", "path": "Star2.lean",
             "slice_sha256": "same", "source_sha256": "historic"},
        ]}
        rebuilt = {"sources": [
            {"kind": "item-declaration", "id": "PM1:✱2·1", "path": "Star2.lean",
             "slice_sha256": "same", "source_sha256": "current"},
            {"kind": "item-declaration", "id": "PM1:✱2·2", "path": "Star2.lean",
             "slice_sha256": "new", "source_sha256": "current"},
        ]}
        preserve_historical_container_hashes(recorded, rebuilt)
        self.assertEqual(rebuilt["sources"][0]["source_sha256"], "historic")
        self.assertEqual(rebuilt["sources"][1]["source_sha256"], "current")


if __name__ == "__main__":
    unittest.main()
