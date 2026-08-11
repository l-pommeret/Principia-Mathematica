import importlib.util
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "verify_errata_registry", ROOT / "scripts/verify_errata_registry.py")
errata = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(errata)


class ErrataRegistryTests(unittest.TestCase):
    def test_repository_registry_is_complete_and_linked(self):
        payload = errata.verify_registry()
        self.assertEqual(len(payload["entries"]), 13)

    def test_integrated_locus_cannot_lose_its_apparatus_link(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative in ("metadata/errata", "metadata/apparatus", "metadata/source_blocks"):
                shutil.copytree(ROOT / relative, root / relative)
            path = root / "metadata/errata/PM1-1910-errata.json"
            payload = json.loads(path.read_text(encoding="utf-8"))
            payload["entries"][0]["integration"].pop("apparatus_id")
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(SystemExit):
                errata.verify_registry(root)

    def test_future_locus_must_remain_unlinked_while_pending(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative in ("metadata/errata", "metadata/apparatus", "metadata/source_blocks"):
                shutil.copytree(ROOT / relative, root / relative)
            path = root / "metadata/errata/PM1-1910-errata.json"
            payload = json.loads(path.read_text(encoding="utf-8"))
            payload["entries"][6]["integration"]["apparatus_id"] = "FAKE"
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(SystemExit):
                errata.verify_registry(root)


if __name__ == "__main__":
    unittest.main()
