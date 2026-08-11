import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from inventory_aristotle_remap_candidates import inventory


class AristotleRemapInventoryTests(unittest.TestCase):
    def test_repository_inventory_is_fail_closed_for_every_unmapped_batch(self):
        report = inventory(ROOT)
        self.assertIsNone(report["first_transplant_candidate"])
        blocker = report["first_exact_blocker"]
        self.assertIsNotNone(blocker)
        self.assertRegex(blocker["batch"], r"^Q(?:22[8-9]|2[3-4][0-9]|25[0-1])$")
        self.assertTrue(blocker["status"].startswith("blocked-"))
        self.assertFalse(blocker["interface_mapping_possible"])

    def test_matching_file_is_not_automatically_a_mapping_candidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "aristotle/results").mkdir(parents=True)
            (root / "reviews").mkdir()
            archive = root / "aristotle/results/Q228-final.tar.gz"
            archive.write_bytes(b"immutable fixture")
            digest = hashlib.sha256(archive.read_bytes()).hexdigest()
            (root / "reviews/Q228-Q244-aristotle-archive-audit.json").write_text(json.dumps({
                "archives": [{"batch": "Q228", "sha256": digest,
                              "integration": "blocked by archive-local helper"}],
            }), encoding="utf-8")
            (root / "reviews/Q235-Q251-kernel-link-audit.json").write_text(json.dumps({
                "batches": [{"batch": "Q228", "status": "not-linkable",
                              "reason": "local helper"}],
            }), encoding="utf-8")
            report = inventory(root)
            record = report["batches"][0]
            self.assertEqual(record["status"], "available-hash-matched")
            self.assertFalse(record["interface_mapping_possible"])
            self.assertIsNone(report["first_transplant_candidate"])


if __name__ == "__main__":
    unittest.main()
