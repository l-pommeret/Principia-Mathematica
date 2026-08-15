"""Regression coverage for protected files outside scripts/ in Git snapshots."""

from __future__ import annotations

import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_gate_integrity


class CommittedProtectedPathsTests(unittest.TestCase):
    def test_committed_at_includes_protected_metadata_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            protected = repo / "metadata" / "assumptions.json"
            protected.parent.mkdir()
            committed_content = b'{"source": "HEAD"}\n'
            protected.write_bytes(committed_content)

            self._git(repo, "init", "-q")
            self._git(repo, "add", "metadata/assumptions.json")
            self._git(
                repo,
                "-c",
                "user.name=Gate Test",
                "-c",
                "user.email=gate-test@example.invalid",
                "commit",
                "-q",
                "-m",
                "add protected metadata fixture",
            )
            protected.write_text('{"source": "worktree"}\n', encoding="utf-8")

            with patch.object(verify_gate_integrity, "ROOT", repo):
                committed = verify_gate_integrity.committed_at("HEAD")

            self.assertEqual(
                committed["metadata/assumptions.json"],
                hashlib.sha256(committed_content).hexdigest(),
            )

    @staticmethod
    def _git(repo: Path, *arguments: str) -> None:
        subprocess.run(
            ["git", *arguments],
            cwd=repo,
            check=True,
            capture_output=True,
        )


if __name__ == "__main__":
    unittest.main()
