import json
import unittest

import sys
from pathlib import Path as _Path
sys.path.insert(0, str(_Path(__file__).resolve().parent))
from pm_tier_assertions import assert_tier_consistent
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class Star4KernelGateTests(unittest.TestCase):
    def test_star_4_77_is_kernel_checked(self):
        metadata = json.loads(
            (ROOT / "metadata/items/PM1-star-4-kernel-Q239-77.json").read_text(
                encoding="utf-8"
            )
        )
        item = metadata["items"][0]
        self.assertEqual(item["id"], "PM1:✱4·77")
        assert_tier_consistent(self, metadata, item)
        self.assertNotIn("PM.Derivation.detach", item["lean_dependencies"])

    def test_third_group_is_kernel_checked_together(self):
        cases = (
            ("Q240-8", "PM1:✱4·8"),
            ("Q240-81", "PM1:✱4·81"),
            ("Q231-36", "PM1:✱4·36"),
        )
        for suffix, item_id in cases:
            metadata = json.loads(
                (ROOT / f"metadata/items/PM1-star-4-kernel-{suffix}.json").read_text(
                    encoding="utf-8"
                )
            )
            item = metadata["items"][0]
            self.assertEqual(item["id"], item_id)
            assert_tier_consistent(self, metadata, item)
            self.assertNotIn("PM.Derivation.detach", item["lean_dependencies"])
        source = (
            ROOT / "Principia/FirstEdition/Volume1/Part1/SectionA/Star4.lean"
        ).read_text(encoding="utf-8")
        start = source.index("theorem star_4_8")
        end = source.index("/-- Audited scope reading of ✱4·81.", start)
        body = source[start:end]
        self.assertNotIn("PM.Derivation.detach", body)


if __name__ == "__main__":
    unittest.main()
