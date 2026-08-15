"""Regression tests for the fail-closed textual tactic gate."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_library_independence import core_files, tactic_findings  # noqa: E402


def _lean(body: str) -> Path:
    handle = tempfile.NamedTemporaryFile(
        "w", suffix=".lean", delete=False, encoding="utf-8"
    )
    handle.write(body)
    handle.close()
    return Path(handle.name)


class SealedTacticPatternTests(unittest.TestCase):
    def test_library_and_search_tactics_are_all_detected(self) -> None:
        tactics = (
            "simp",
            "simp_all",
            "simpa",
            "decide",
            "native_decide",
            "bv_decide",
            "omega",
            "grind",
            "norm_cast",
            "norm_num1",
            "exact?",
            "apply?",
            "aesop?",
            "hint",
        )
        for tactic in tactics:
            with self.subTest(tactic=tactic):
                path = _lean(f"theorem sealed : True := by {tactic}\n")
                self.assertTrue(tactic_findings([path]))

    def test_prefix_families_cannot_evade_the_pattern(self) -> None:
        for tactic in ("simp_future", "compiler_decide", "norm_future"):
            with self.subTest(tactic=tactic):
                path = _lean(f"theorem sealed : True := by {tactic}\n")
                self.assertTrue(tactic_findings([path]))

    def test_an_unlisted_future_tactic_fails_closed(self) -> None:
        proofs = (
            "theorem sealed : True := by\n"
            "  exact True.intro\n"
            "  future_library_search\n",
            "theorem sealed : True ∧ True := by\n"
            "  constructor\n"
            "  · exact True.intro\n"
            "  · future_library_search\n",
            "theorem sealed (n : Nat) : True := by\n"
            "  induction n with\n"
            "  | zero =>\n"
            "    future_library_search\n"
            "  | succ _ _ => exact True.intro\n",
        )
        for proof in proofs:
            with self.subTest(proof=proof):
                findings = tactic_findings([_lean(proof)])
                self.assertTrue(findings)
                self.assertTrue(
                    any("not an approved explicit tactic" in item for item in findings)
                )


class RootModuleScopeTests(unittest.TestCase):
    def test_principia_root_module_is_audited(self) -> None:
        self.assertIn(ROOT / "Principia.lean", core_files())


if __name__ == "__main__":
    unittest.main()
