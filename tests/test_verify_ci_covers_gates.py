"""Regression tests for equivalence between repository gates and CI."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "verify_ci_covers_gates.py"


class CIGateCoverageTests(unittest.TestCase):
    def run_checker(self, files: dict[str, str]) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative, content in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(textwrap.dedent(content), encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(CHECKER), "--root", str(root)],
                text=True,
                capture_output=True,
                check=False,
            )

    def test_gate_absent_from_workflows_fails_and_is_named(self) -> None:
        result = self.run_checker(
            {
                "scripts/verify_present.py": "print('present')\n",
                "scripts/verify_fictitious_orphan.py": "print('orphan')\n",
                ".github/workflows/ci.yml": """
                    jobs:
                      check:
                        steps:
                          - run: python3 scripts/verify_present.py
                """,
            }
        )

        self.assertEqual(result.returncode, 1)
        self.assertIn("scripts/verify_fictitious_orphan.py", result.stderr)
        self.assertIn("Add it directly to a workflow", result.stderr)

    def test_aggregators_are_followed_transitively(self) -> None:
        result = self.run_checker(
            {
                "scripts/verify_outer.py": """
                    import subprocess
                    import sys

                    GATES = (("inner", ["verify_inner.py"]),)
                    for _name, command in GATES:
                        subprocess.run([sys.executable, *command], check=True)
                """,
                "scripts/verify_inner.py": """
                    import subprocess
                    import sys

                    GATES = (("leaf", ["verify_leaf.py"]),)
                    for _name, command in GATES:
                        subprocess.run([sys.executable, *command], check=True)
                """,
                "scripts/verify_leaf.py": "print('leaf')\n",
                ".github/workflows/ci.yml": """
                    jobs:
                      check:
                        steps:
                          - run: python3 scripts/verify_outer.py
                """,
            }
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("3/3 gates reached", result.stdout)


if __name__ == "__main__":
    unittest.main()
