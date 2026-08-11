import importlib.util
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "verify_description_architecture",
    ROOT / "scripts/verify_description_architecture.py",
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class DescriptionArchitecturePolicyTests(unittest.TestCase):
    def test_canonical_gate_passes(self):
        MODULE.main()

    def test_hoas_is_rejected(self):
        bad = """inductive Formula where
  | descriptionScope : (condition : Object → Formula) → Formula
"""
        code = MODULE.code_without_comments_or_strings(bad)
        self.assertRegex(code, r"condition\s*:\s*[^)\n]*→")

    def test_description_term_is_rejected(self):
        bad = """inductive Term where
  | description : Term
inductive Formula where
  | atom : Formula
"""
        code = MODULE.code_without_comments_or_strings(bad)
        self.assertRegex(code, r"inductive\s+Term[\s\S]*?\|\s+description\b")


if __name__ == "__main__":
    unittest.main()
