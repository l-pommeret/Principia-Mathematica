import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class SubstitutionArchitectureTests(unittest.TestCase):
    def test_static_architecture_contract(self):
        completed = subprocess.run(
            [sys.executable, str(ROOT / "scripts/verify_substitution_architecture.py")],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("checks passed", completed.stdout)


if __name__ == "__main__":
    unittest.main()
