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

    def test_star_4_8_candidate_has_no_generic_detach(self):
        metadata = json.loads(
            (ROOT / "metadata/items/PM1-star-4-kernel-Q240-8.json").read_text(
                encoding="utf-8"
            )
        )
        item = metadata["items"][0]
        self.assertEqual(item["id"], "PM1:✱4·8")
        self.assertEqual(item["formal_status"], "awaiting-ci")
        source = (
            ROOT / "Principia/FirstEdition/Volume1/Part1/SectionA/Star4.lean"
        ).read_text(encoding="utf-8")
        body = source[source.index("theorem star_4_8") :]
        self.assertNotIn("PM.Derivation.detach", body)


if __name__ == "__main__":
    unittest.main()
