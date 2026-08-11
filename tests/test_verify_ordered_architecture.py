import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class OrderedArchitectureTests(unittest.TestCase):
    def test_static_contract(self):
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts/verify_ordered_architecture.py")],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("checks passed", result.stdout)


if __name__ == "__main__":
    unittest.main()
