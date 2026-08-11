import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from pm_constraint_manifest import ConstraintError, compile_batch_manifest, compile_manifest
from pm_proof_skeleton import parse_demonstration
from pm_aristotle_prompt import render_batch_prompt


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
            "PM1:✱1·3": item("PM1:✱1·3", "PM.star_1_3"),
            "PM1:✱2·05": item("PM1:✱2·05", "PM.star_2_05", ["PM1:✱1·2"]),
            "PM1:✱2·06": item("PM1:✱2·06", "PM.star_2_06", ["PM1:✱1·2"]),
            "PM1:✱1·2": item("PM1:✱1·2", "PM.star_1_2"),
            "PM1:✱2·15": item("PM1:✱2·15", "PM.star_2_15"),
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
            manifest["allowed_pm_items"],
            ["PM1:✱2·15", "PM1:✱2·16", "PM1:✱2·17"],
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

    def test_inline_tuple_and_unbracketed_substitutions_are_preserved(self):
        skeleton = parse_demonstration(
            "✱2·74. ⊢ : p [✱2·16 (q,p)/(p,q) . ✱2·17 ∼q/q]",
            current_item="PM1:✱2·18",
        )
        manifest = compile_manifest(skeleton, self.registry)
        self.assertEqual(
            [entry["printed"] for entry in manifest["substitutions"]],
            ["(q,p)/(p,q)", "∼q/q"],
        )

    def test_ordered_batch_allows_only_preceding_local_targets(self):
        first = parse_demonstration(
            "✱2·18. ⊢ : p [✱2·16]", current_item="PM1:✱2·18"
        )
        second = parse_demonstration(
            "✱2·19. ⊢ : p [✱2·18 . ✱2·17]", current_item="PM1:✱2·19"
        )
        batch = compile_batch_manifest(
            [first, second], self.registry,
            {
                "PM1:✱2·18": "PM.star_2_18",
                "PM1:✱2·19": "PM.star_2_19",
            },
        )
        self.assertEqual(batch["target_order"], ["PM1:✱2·18", "PM1:✱2·19"])
        self.assertEqual(batch["batch_items"][1]["local_proof_items"], ["PM1:✱2·18"])
        self.assertNotIn("PM1:✱2·18", batch["context_closure"])

    def test_batch_rejects_forward_local_reference(self):
        first = parse_demonstration(
            "✱2·18. ⊢ : p [✱2·19]", current_item="PM1:✱2·18"
        )
        second = parse_demonstration(
            "✱2·19. ⊢ : p [✱2·16]", current_item="PM1:✱2·19"
        )
        with self.assertRaisesRegex(ConstraintError, "missing metadata"):
            compile_batch_manifest(
                [first, second], self.registry,
                {"PM1:✱2·18": "PM.star_2_18", "PM1:✱2·19": "PM.star_2_19"},
            )

    def test_batch_prompt_keeps_per_target_whitelists_separate(self):
        first = parse_demonstration(
            "✱2·18. ⊢ : p [✱2·16]", current_item="PM1:✱2·18"
        )
        second = parse_demonstration(
            "✱2·19. ⊢ : p [✱2·18 . ✱2·17]", current_item="PM1:✱2·19"
        )
        batch = compile_batch_manifest(
            [first, second], self.registry,
            {"PM1:✱2·18": "PM.star_2_18", "PM1:✱2·19": "PM.star_2_19"},
        )
        prompt = render_batch_prompt(
            batch,
            printed_targets={"PM1:✱2·18": "printed 18", "PM1:✱2·19": "printed 19"},
            lean_targets={"PM1:✱2·18": "lean 18", "PM1:✱2·19": "lean 19"},
            context="inductive Context where",
        )
        second_section = prompt.split("### 2. PM1:✱2·19", 1)[1]
        self.assertIn("PM1:✱2·18", second_section)
        self.assertIn("Earlier local targets licensed here: PM1:✱2·18", second_section)

    def test_reviewed_global_convention_is_allowed_but_not_a_printed_event(self):
        skeleton = parse_demonstration(
            "✱2·45. ⊢ : p [✱2·05]", current_item="PM1:✱2·45"
        )
        manifest = compile_manifest(
            skeleton, self.registry, global_conventions=["PM1:✱1·2"]
        )
        self.assertIn("PM1:✱1·2", manifest["allowed_pm_items"])
        self.assertEqual(manifest["global_conventions"], ["PM1:✱1·2"])
        self.assertEqual(len(manifest["proof_permissions"]), 1)

    def test_reference_bracket_before_assertion_starts_a_demonstration_line(self):
        skeleton = parse_demonstration(
            "[Add . Syll] ⊢ : p ⊃ q (1)\n⊢ . (1) . ⊃ ⊢ . Prop",
            current_item="PM1:✱2·85",
        )
        manifest = compile_manifest(skeleton, self.registry)
        self.assertEqual(
            manifest["allowed_pm_items"],
            ["PM1:✱1·3", "PM1:✱2·05", "PM1:✱2·06"],
        )


if __name__ == "__main__":
    unittest.main()
