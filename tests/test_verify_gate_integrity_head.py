"""Regression tests for the HEAD-backed gate authorisation boundary."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "verify_gate_integrity.py"


class GateIntegrityHeadTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name)
        (self.repo / "scripts").mkdir()
        (self.repo / "metadata").mkdir()
        shutil.copy2(CHECKER, self.repo / "scripts" / CHECKER.name)
        self.fixture = self.repo / "scripts" / "verify_fixture.py"
        self.fixture.write_text("print('baseline')\n", encoding="utf-8")
        self._git("init", "-q")
        self._git("config", "user.email", "gate-test@example.invalid")
        self._git("config", "user.name", "Gate Test")
        self._write_manifest()
        self._git("add", "scripts", "metadata/gate_integrity.json")
        self._git("commit", "-q", "-m", "establish gate baseline")
        update = subprocess.run(
            [
                sys.executable,
                "scripts/verify_gate_integrity.py",
                "--update",
                "--authorised-by",
                "Test Maintainer",
                "--reason",
                "establish the HEAD-backed test boundary",
            ],
            cwd=self.repo,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(update.returncode, 0, update.stdout + update.stderr)
        self._git("add", "metadata/gate_integrity.json")
        self._git("commit", "-q", "-m", "authorise committed gate baseline")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _git(self, *arguments: str) -> None:
        subprocess.run(
            ["git", *arguments],
            cwd=self.repo,
            check=True,
            capture_output=True,
        )

    @staticmethod
    def _digest(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def _write_manifest(self) -> None:
        paths = (
            self.repo / "scripts" / "verify_gate_integrity.py",
            self.fixture,
        )
        manifest = self.repo / "metadata" / "gate_integrity.json"
        if manifest.is_file():
            payload = json.loads(manifest.read_text(encoding="utf-8"))
        else:
            payload = {"note": "test trust base", "authorisations": []}
        payload["digests"] = {
            str(path.relative_to(self.repo)): self._digest(path) for path in paths
        }
        manifest.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    def test_gate_and_repinned_digest_in_same_commit_remain_rejected(self) -> None:
        self.fixture.write_text("print('weakened')\n", encoding="utf-8")
        self._write_manifest()
        self._git("add", "scripts/verify_fixture.py", "metadata/gate_integrity.json")
        self._git("commit", "-q", "-m", "change gate and re-pin together")
        (self.repo / "README.md").write_text("later unrelated work\n", encoding="utf-8")
        self._git("add", "README.md")
        self._git("commit", "-q", "-m", "unrelated follow-up")

        result = subprocess.run(
            [sys.executable, "scripts/verify_gate_integrity.py"],
            cwd=self.repo,
            capture_output=True,
            text=True,
            check=False,
        )

        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 1, output)
        self.assertIn("même commit", output)
        self.assertIn("contrôle vide (vacuous)", output)
        self.assertIn("commit séparé", output)


if __name__ == "__main__":
    unittest.main()
