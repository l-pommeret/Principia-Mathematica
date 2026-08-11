import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("verify_retry_registry", ROOT / "scripts/verify_retry_registry.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RetryRegistryTests(unittest.TestCase):
    def test_registry_is_valid(self):
        self.assertEqual(MODULE.verify()["kind"], "pm-operational-retry-registry")

    def test_retry_cannot_promote_itself(self):
        data = json.loads((ROOT / "metadata/retry_registry.json").read_text())
        data["retries"][0]["promotion_key"] = "Q9001"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "registry.json"
            path.write_text(json.dumps(data))
            with self.assertRaises(SystemExit):
                MODULE.verify(path)

    def test_duplicate_canonical_is_rejected(self):
        data = json.loads((ROOT / "metadata/retry_registry.json").read_text())
        data["retries"][1]["retry_of"] = data["retries"][0]["retry_of"]
        data["retries"][1]["promotion_key"] = data["retries"][0]["retry_of"]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "registry.json"
            path.write_text(json.dumps(data))
            with self.assertRaises(SystemExit):
                MODULE.verify(path)
