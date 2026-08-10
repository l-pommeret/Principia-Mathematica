import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "verify_typical_ambiguity_toy",
    ROOT / "scripts/verify_typical_ambiguity_toy.py")
typical = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(typical)


class TypicalAmbiguityToyPolicyTests(unittest.TestCase):
    def test_architecture_guard_accepts_repository(self):
        typical.main()

    def test_guard_inspects_code_not_prose(self):
        source = '"axiom" /- unsafeCast -/\ndef safe := True\n'
        code = typical.code_without_comments_or_strings(source)
        self.assertNotIn("axiom", code)
        self.assertNotIn("unsafeCast", code)
        self.assertIn("def safe", code)


if __name__ == "__main__":
    unittest.main()
