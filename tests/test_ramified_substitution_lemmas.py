import subprocess
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_TEST = ROOT / "tests/lean/RamifiedSubstitutionLemmas.lean"


class RamifiedSubstitutionLemmaTests(unittest.TestCase):
    def test_public_substitution_lemmas_are_kernel_checked(self):
        built = subprocess.run(
            ["lake", "build", "Principia.Syntax.Ramified"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        completed = subprocess.run(
            ["lake", "env", "lean", str(LEAN_TEST.relative_to(ROOT))],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)


if __name__ == "__main__":
    unittest.main()
