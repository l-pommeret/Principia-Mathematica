import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from pm_aristotle_prompt import PromptError, render_prompt


BASE = {
    "kind": "pm-constrained-prover-manifest",
    "current_item": "PM1:✱2·61",
    "allowed_lean_declarations": {
        "PM1:✱2·04": "PM.Star2.star_2_04",
        "PM1:✱2·6": "PM.Star2.star_2_6",
    },
    "context_closure": ["PM1:✱1·2", "PM1:✱2·04", "PM1:✱2·6"],
    "diagnostics": {
        "missing_items": [], "non_kernel_checked_items": [],
        "unresolved_aliases": [],
    },
    "substitutions": [{"step": 1, "printed": "∼q/q"}],
}


class AristotlePromptTests(unittest.TestCase):
    def test_compact_prompt_names_only_whitelisted_theorems_as_permissions(self):
        prompt = render_prompt(
            BASE,
            printed_target="✱2·61. ⊢ ...",
            lean_target="theorem star_2_61 : Goal := by",
            context="private theorem dependency : P := proof",
        )
        whitelist = prompt.split("## Exact historical proof whitelist", 1)[1].split(
            "No other PM theorem", 1
        )[0]
        self.assertIn("PM.Star2.star_2_04", whitelist)
        self.assertIn("PM.Star2.star_2_6", whitelist)
        self.assertNotIn("dependency", whitelist)
        self.assertIn("step 1: `∼q/q`", prompt)
        self.assertIn("context below grants no additional proof permission", prompt)

    def test_nonempty_closure_requires_reviewed_context(self):
        with self.assertRaisesRegex(PromptError, "reviewed isolated Lean context"):
            render_prompt(BASE, printed_target="p", lean_target="theorem t : P := by")

    def test_definition_without_closure_needs_no_context(self):
        manifest = dict(BASE)
        manifest["context_closure"] = []
        manifest["allowed_lean_declarations"] = {}
        prompt = render_prompt(manifest, printed_target="p .=. q Df", lean_target="abbrev t := q")
        self.assertIn("none (definition/primitive target)", prompt)

    def test_unresolved_manifest_cannot_render(self):
        manifest = dict(BASE)
        manifest["diagnostics"] = dict(BASE["diagnostics"])
        manifest["diagnostics"]["missing_items"] = ["PM1:✱9·99"]
        with self.assertRaisesRegex(PromptError, "unresolved"):
            render_prompt(manifest, printed_target="p", lean_target="t", context="ctx")


if __name__ == "__main__":
    unittest.main()
