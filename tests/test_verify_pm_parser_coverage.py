import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_pm_parser_coverage import ParserCoverageError, audit


class ParserCoverageTests(unittest.TestCase):
    def test_repository_formal_catalogue_is_fully_routed(self):
        result = audit(ROOT)
        self.assertGreaterEqual(result["counts"]["object_language"], 73)
        self.assertEqual(
            result["metalinguistic_rules"],
            [
                "PM1:✱1·1", "PM1:✱1·11", "PM1:✱1·7", "PM1:✱1·71",
                "PM1:✱1·72", "PM1:✱3·03", "PM1:✱9·12", "PM1:✱9·13",
            ],
        )
        self.assertEqual(
            result["counts"]["total"],
            result["counts"]["object_language"] + len(result["metalinguistic_rules"]) +
            result["counts"]["architecture_gated"],
        )

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
