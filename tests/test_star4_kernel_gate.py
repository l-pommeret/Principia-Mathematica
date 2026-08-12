import json
import unittest
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
        self.assertEqual(item["formal_status"], "kernel-checked")
        self.assertEqual(metadata["ci_evidence"], {
            "commit": "9cf0db084ad6ee4baa542aab1be9080e3d395690",
            "run": "31551057810",
            "conclusion": "success",
        })
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
            self.assertEqual(item["formal_status"], "kernel-checked")
            self.assertEqual(metadata["ci_evidence"], {
                "commit": "8da5d1fdec9a8c765fdcbc8c38fb46d042944f34",
                "run": "31552231965",
                "conclusion": "success",
            })
            self.assertNotIn("PM.Derivation.detach", item["lean_dependencies"])
        source = (
            ROOT / "Principia/FirstEdition/Volume1/Part1/SectionA/Star4.lean"
        ).read_text(encoding="utf-8")
        body = source[source.index("theorem star_4_8") :]
        self.assertNotIn("PM.Derivation.detach", body)


if __name__ == "__main__":
    unittest.main()
