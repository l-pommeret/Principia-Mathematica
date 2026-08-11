import sys
import unittest
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_queue_inventory import inventory


class PMQueueInventoryTests(unittest.TestCase):
    def test_inventory_distinguishes_catalogue_from_campaign_planning(self):
        result = inventory(ROOT)
        counts = result["counts"]
        self.assertGreaterEqual(counts["catalogued_items"], 75)
        self.assertEqual(
            counts["catalogued_items"],
            counts["object_language_ast_parsed"] + counts["metalinguistic_routes"],
        )
        self.assertGreaterEqual(counts["all_proof_skeleton_targets"], 17)
        self.assertGreater(counts["planned_uncatalogued_pm_ids"], 0)
        self.assertGreater(counts["catalogued_items_without_campaign_question"], 0)
        self.assertNotIn("PM1:✱3·26", result["planned_but_uncatalogued"])
        self.assertNotIn("PM2:✱1", result["pm_section_coverage"]["planned"])

    def test_catalogued_skeleton_record_keeps_artifact_boundary_explicit(self):
        result = inventory(ROOT)
        records = {item["id"]: item for item in result["catalogued_items"]}
        self.assertEqual(records["PM1:✱3·03"]["proof_skeleton"]["batch"], "Q217")
        self.assertEqual(records["PM1:✱3·26"]["proof_skeleton"]["batch"], "Q223")
        self.assertEqual(records["PM1:✱2·01"]["proof_skeleton"], {"status": "missing"})

    def test_tracked_inventory_is_reproducible(self):
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts/pm_queue_inventory.py"),
             "--check", "metadata/queue_inventory.json"],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
