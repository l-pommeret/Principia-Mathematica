import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_context_bundles import ContextBundleVerificationError, verify


class VerifyContextBundlesTests(unittest.TestCase):
    def test_repository_bundle_reproduces_exactly(self):
        self.assertGreaterEqual(verify(ROOT), 1)

    def test_missing_bundle_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "metadata/context_bundles").mkdir(parents=True)
            with self.assertRaisesRegex(ContextBundleVerificationError, "no isolated"):
                verify(root)


if __name__ == "__main__":
    unittest.main()
