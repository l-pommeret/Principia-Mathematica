import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class Star5KernelGateTests(unittest.TestCase):
    def test_star_5_13_is_kernel_checked_with_immutable_ci_evidence(self):
        metadata = json.loads(
            (ROOT / "metadata/items/PM1-star-5-kernel-Q243-13.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(metadata["ci_evidence"], {
            "commit": "9cc9628f02f0efc06138463480c66c04c8d455d9",
            "run": "31545695849",
            "conclusion": "success",
        })
        self.assertEqual(len(metadata["items"]), 1)
        item = metadata["items"][0]
        self.assertEqual(item["id"], "PM1:✱5·13")
        self.assertEqual(item["formal_status"], "kernel-checked")
        self.assertEqual(item["printed_dependencies"], ["PM1:✱2·521"])
        self.assertEqual(
            item["historical_dependency_relaxation"]["added_beyond_print"],
            ["PM1:✱1·1", "PM1:✱1·11", "PM1:✱2·54"],
        )

    def test_star_5_25_explicit_inference_is_kernel_checked(self):
        metadata = json.loads(
            (ROOT / "metadata/items/PM1-star-5-kernel-Q246-25.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(metadata["ci_evidence"], {
            "commit": "312fc3c1b375a11d02415a02428b025856496aae",
            "run": "31546934083",
            "conclusion": "success",
        })
        self.assertEqual(len(metadata["items"]), 1)
        item = metadata["items"][0]
        self.assertEqual(item["id"], "PM1:✱5·25")
        self.assertEqual(item["formal_status"], "kernel-checked")
        self.assertEqual(item["printed_dependencies"], ["PM1:✱2·62", "PM1:✱2·68"])

    def test_star_5_13_keeps_the_scan_citation_and_closed_term_dependencies(self):
        source = (ROOT / "Principia/FirstEdition/Volume1/Part1/SectionA/Star5.lean").read_text(
            encoding="utf-8"
        )
        kernel = (ROOT / "Principia/FirstEdition/Volume1/Part1/SectionA/Star5Kernel.lean").read_text(
            encoding="utf-8"
        )
        self.assertIn("[✱2·521]", source)
        self.assertNotIn("✱5·13.  ⊢ : p ⊃ q . ∨ . q ⊃ p   [✱2·5·21]", source)
        self.assertIn("theorem star_5_13", kernel)
        self.assertIn("Star2.star_2_521 p q", kernel)
        self.assertIn("Star2.star_2_54 (p ⊃ₚ q) (q ⊃ₚ p)", kernel)
        for forbidden in ("axiom", "sorry", "admit", "unsafe", "Classical"):
            self.assertNotIn(forbidden, kernel)


if __name__ == "__main__":
    unittest.main()
