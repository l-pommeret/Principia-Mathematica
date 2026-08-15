import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_dependencies as dependencies


class MissingDeclarationTests(unittest.TestCase):
    def write_fixture(self, root: Path, item: dict) -> None:
        items = root / "metadata/items"
        items.mkdir(parents=True)
        (items / "catalogue.json").write_text(
            json.dumps({"items": [item]}), encoding="utf-8"
        )
        (root / "metadata/assumptions.json").write_text(
            json.dumps({"schema_version": 1, "assumptions": []}), encoding="utf-8"
        )
        (root / "metadata/dependency_aliases.json").write_text(
            json.dumps({"aliases": {}, "lean_realizations": {}}), encoding="utf-8"
        )

    def test_catalogued_item_without_declaration_is_ignored(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_fixture(root, {
                "id": "PM1:✱1·01",
                "kind": "proposition",
                "formal_status": "catalogued",
                "normalized_dependencies": [],
            })

            graph = dependencies.audit(root)

            self.assertEqual(graph["coverage"]["total_metadata_items"], 1)
            self.assertEqual(graph["coverage"]["audited_items"], 0)
            self.assertEqual(graph["historical_graph"]["edges"], [])
            self.assertEqual(graph["lean_graph"]["edges"], [])

    def test_formalization_level_without_declaration_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_fixture(root, {
                "id": "PM1:✱1·01",
                "kind": "proposition",
                "formal_status": "prepared",
                "formalization_level": "pm-derivation-v1",
                "normalized_dependencies": [],
            })

            with self.assertRaisesRegex(
                dependencies.DependencyError,
                "formalization_level is present but declaration is missing",
            ):
                dependencies.audit(root)


if __name__ == "__main__":
    unittest.main()
