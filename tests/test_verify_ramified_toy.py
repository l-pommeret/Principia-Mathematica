import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "verify_ramified_toy", ROOT / "scripts/verify_ramified_toy.py")
ramified = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(ramified)


class RamifiedToyPolicyTests(unittest.TestCase):
    def test_architecture_guard_accepts_repository(self):
        ramified.main()

    def test_comment_and_string_stripping_prevents_false_positives(self):
        source = '"axiom reducibility" /- ∀ semantic prose -/\nstructure Safe where\n'
        code = ramified.code_without_comments_or_strings(source)
        self.assertNotIn("axiom reducibility", code)
        self.assertNotIn("∀", code)
        self.assertIn("structure Safe", code)


if __name__ == "__main__":
    unittest.main()
