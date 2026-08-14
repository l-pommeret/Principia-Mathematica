import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_queue_inventory import inventory
from verify_pm_parser_coverage import ParserCoverageError, audit


class ParserCoverageTests(unittest.TestCase):
    def test_repository_formal_catalogue_is_fully_routed(self):
        result = inventory(ROOT)
        counts = result["counts"]
        self.assertEqual(
            counts["catalogued_items"],
            counts["object_language_ast_parsed"] + counts["metalinguistic_routes"] +
            counts["architecture_gated_source_routes"],
        )
        for item in result["catalogued_items"]:
            ast = item["ast"]
            self.assertIn(
                ast["status"],
                {"parsed", "metalinguistic-route", "parser-gap", "reviewed-parser-gap",
                 "architecture-gated-source-route"},
                item["id"],
            )
            if ast["status"] == "parsed":
                self.assertEqual(len(ast["sha256"]), 64, item["id"])
            elif ast["status"] == "parser-gap":
                self.assertTrue(item["source_catalogue"], item["id"])
                self.assertTrue(ast.get("detail"), item["id"])
            elif ast["status"] == "reviewed-parser-gap":
                self.assertTrue(ast.get("evidence"), item["id"])
            elif ast["status"] == "architecture-gated-source-route":
                self.assertTrue(item["source_catalogue"], item["id"])
                self.assertNotEqual(item["formal_status"], "kernel-checked", item["id"])

    def test_unparsed_object_item_fails_the_gate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "metadata/items").mkdir(parents=True)
            payload = {
                "items": [{
                    "id": "PM1:✱1·99", "kind": "derived-proposition",
                    "printed": "this is not PM object syntax",
                }]
            }
            (root / "metadata/items/bad.json").write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaisesRegex(ParserCoverageError, "PM1:✱1·99"):
                audit(root)


if __name__ == "__main__":
    unittest.main()
