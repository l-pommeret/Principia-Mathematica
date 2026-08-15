import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_editorial as editorial


class UnformalizedItemMetadataTests(unittest.TestCase):
    def write_fixture(self, root: Path, item: dict) -> None:
        items = root / "metadata/items"
        items.mkdir(parents=True)
        (items / "catalogue.json").write_text(
            json.dumps({
                "items": [item],
                "ci_evidence": {
                    "commit": "pending",
                    "run": "pending",
                    "conclusion": "pending",
                },
            }),
            encoding="utf-8",
        )

    def item(self) -> dict:
        return {
            "id": "PM1:✱1·01",
            "kind": "proposition",
            "printed": "⊢ p",
            "formal_scope": "catalogued source only",
            "source_status": "source-catalogued",
            "formal_status": "prepared",
        }

    def test_catalogued_item_without_formalization_pointers_passes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_fixture(root, self.item())

            with patch.object(editorial, "ROOT", root):
                editorial.check_item_metadata()

    def test_formalization_level_without_pointers_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            item = self.item()
            item["formalization_level"] = "pm-derivation-v1"
            self.write_fixture(root, item)

            with patch.object(editorial, "ROOT", root):
                with self.assertRaisesRegex(
                    editorial.EditorialError,
                    "has formalization_level but lacks required formalization "
                    "pointers: \\['declaration', 'lean_path'\\]",
                ):
                    editorial.check_item_metadata()


if __name__ == "__main__":
    unittest.main()
