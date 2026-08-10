import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "verify_description_scope_toy",
    ROOT / "scripts/verify_description_scope_toy.py")
scope = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(scope)


class DescriptionScopeToyPolicyTests(unittest.TestCase):
    def test_architecture_guard_accepts_repository(self):
        scope.main()

    def test_guard_inspects_code_not_prose(self):
        source = '"axiom DescriptionTerm" /- description : Object -/\ndef safe := True\n'
        code = scope.code_without_comments_or_strings(source)
        self.assertNotIn("axiom", code)
        self.assertNotIn("DescriptionTerm", code)
        self.assertIn("def safe", code)


if __name__ == "__main__":
    unittest.main()
