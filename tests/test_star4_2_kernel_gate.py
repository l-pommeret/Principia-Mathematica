import json
import unittest

import sys
from pathlib import Path as _Path
sys.path.insert(0, str(_Path(__file__).resolve().parent))
from pm_tier_assertions import assert_tier_consistent
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class Star42KernelGateTests(unittest.TestCase):
    def test_candidate_has_explicit_inference_branches(self):
        metadata = json.loads(
            (ROOT / "metadata/items/PM1-star-4-kernel-Q228-2.json").read_text(
                encoding="utf-8"
            )
        )
        item = metadata["items"][0]
        self.assertEqual(item["id"], "PM1:✱4·2")
        assert_tier_consistent(self, metadata, item)
        self.assertNotIn("PM.Derivation.detach", item["lean_dependencies"])
        self.assertIn("PM.Derivation.star_1_1", item["lean_dependencies"])
        self.assertIn("PM.Derivation.star_1_11", item["lean_dependencies"])

    def test_body_uses_id_twice_and_no_forbidden_construct(self):
        source = (
            ROOT / "Principia/FirstEdition/Volume1/Part1/SectionA/Star4.lean"
        ).read_text(encoding="utf-8")
        body = source[source.index("theorem star_4_2") : source.index("theorem star_4_11")]
        self.assertEqual(body.count("Star2.star_2_08 p"), 2)
        self.assertIn("Star3.star_3_2 (p ⊃ₚ p) (p ⊃ₚ p)", body)
        for forbidden in ("axiom", "sorry", "admit", "unsafe", "Classical"):
            self.assertNotIn(forbidden, body)


if __name__ == "__main__":
    unittest.main()
