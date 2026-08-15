"""Ensure the local lock covers every gate-integrity normative input."""

from __future__ import annotations

import stat
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_gate_integrity import PROTECTED_GLOBS


class GateLockCoverageTests(unittest.TestCase):
    def test_every_protected_file_is_read_only_after_locking(self) -> None:
        subprocess.run(
            [ROOT / "tools" / "gate-lock"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )

        writable_bits = stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH
        protected = {
            path
            for pattern in PROTECTED_GLOBS
            for path in ROOT.glob(pattern)
            if path.is_file()
        }
        self.assertTrue(protected, "PROTECTED_GLOBS did not match any files")

        writable = sorted(
            str(path.relative_to(ROOT))
            for path in protected
            if path.stat().st_mode & writable_bits
        )
        self.assertEqual(
            [],
            writable,
            "gate-lock left protected files writable: " + ", ".join(writable),
        )


if __name__ == "__main__":
    unittest.main()
