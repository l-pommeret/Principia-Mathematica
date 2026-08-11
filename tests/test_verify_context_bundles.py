import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_context_bundles import ContextBundleVerificationError, report_all, verify


class VerifyContextBundlesTests(unittest.TestCase):
    def test_repository_bundle_reproduces_exactly(self):
        self.assertGreaterEqual(verify(ROOT), 1)

    def test_missing_bundle_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "metadata/context_bundles").mkdir(parents=True)
            with self.assertRaisesRegex(ContextBundleVerificationError, "no isolated"):
                verify(root)

    def test_report_all_collects_multiple_independent_mutations_in_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            metadata = root / "metadata/context_bundles"
            metadata.mkdir(parents=True)
            for stem, marker in (("Q300", "source-drift"), ("Q299", "metadata-drift"),
                                 ("Q301", "clean")):
                (metadata / f"{stem}.json").write_text(marker, encoding="utf-8")

            def mutated_verify(path, registry, check_root):
                marker = path.read_text(encoding="utf-8")
                if marker == "metadata-drift":
                    raise ContextBundleVerificationError("context metadata drift")
                if marker == "source-drift":
                    raise ContextBundleVerificationError("generated Lean context drift")

            with patch("verify_context_bundles.load_item_registry", return_value={}), \
                    patch("verify_context_bundles.verify_one", side_effect=mutated_verify):
                checked, errors = report_all(root)

            self.assertEqual(checked, 1)
            self.assertEqual(errors, [
                "Q299: context metadata drift",
                "Q300: generated Lean context drift",
            ])


if __name__ == "__main__":
    unittest.main()
