import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from pm_constraint_manifest import ConstraintError, compile_manifest
from pm_proof_skeleton import parse_demonstration


def item(identifier, declaration, dependencies=(), status="kernel-checked"):
    return {
        "id": identifier,
        "declaration": declaration,
        "lean_path": "Principia/Test.lean",
        "normalized_dependencies": list(dependencies),
        "formal_status": status,
    }


class ConstraintManifestTests(unittest.TestCase):
    def setUp(self):
        self.registry = {
            "PM1:✱2·05": item("PM1:✱2·05", "PM.star_2_05", ["PM1:✱1·2"]),
            "PM1:✱2·06": item("PM1:✱2·06", "PM.star_2_06", ["PM1:✱1·2"]),
            "PM1:✱1·2": item("PM1:✱1·2", "PM.star_1_2"),
            "PM1:✱2·16": item("PM1:✱2·16", "PM.star_2_16"),
            "PM1:✱2·17": item("PM1:✱2·17", "PM.star_2_17"),
        }

    def test_permissions_are_separate_from_context_closure(self):
        skeleton = parse_demonstration(
            "⊢ . ✱2·05 . ⊃ ⊢ : p ⊃ q                            (1)",
            current_item="PM1:✱2·16",
        )
        manifest = compile_manifest(skeleton, self.registry)
        self.assertEqual(manifest["allowed_pm_items"], ["PM1:✱2·05"])
        self.assertEqual(manifest["context_closure"], ["PM1:✱1·2", "PM1:✱2·05"])
        self.assertFalse(manifest["policy"]["context_closure_grants_proof_permission"])

    def test_historical_alias_family_is_permission_not_silent_choice(self):
        skeleton = parse_demonstration(
            "⊢ . Transp . ⊃ ⊢ : p ⊃ q",
            current_item="PM1:✱2·18",
        )
        manifest = compile_manifest(skeleton, self.registry)
        self.assertEqual(
            manifest["allowed_pm_items"], ["PM1:✱2·16", "PM1:✱2·17"]
        )
        self.assertEqual(
            manifest["proof_permissions"][0]["resolution_status"], "form-family"
        )

    def test_strict_mode_rejects_missing_or_unchecked_items(self):
        skeleton = parse_demonstration(
            "⊢ . ✱2·05 . ✱2·06 . ⊃ ⊢ : p",
            current_item="PM1:✱2·16",
        )
        registry = dict(self.registry)
        registry["PM1:✱2·06"] = item(
            "PM1:✱2·06", "PM.star_2_06", status="awaiting-ci"
        )
        with self.assertRaisesRegex(ConstraintError, "not kernel-checked"):
            compile_manifest(skeleton, registry)

    def test_strict_mode_rejects_alias_without_locus(self):
        skeleton = parse_demonstration("⊢ . Syll . ⊃ ⊢ : p")
        with self.assertRaisesRegex(ConstraintError, "current PM locus"):
            compile_manifest(skeleton, self.registry)

    def test_substitutions_remain_explicit_audit_data(self):
        skeleton = parse_demonstration(
            "⊢ . ✱2·16 [∼q/q] . ⊃ ⊢ : p",
            current_item="PM1:✱2·18",
        )
        manifest = compile_manifest(skeleton, self.registry)
        self.assertEqual(manifest["substitutions"], [{"step": 1, "printed": "∼q/q"}])


if __name__ == "__main__":
    unittest.main()
