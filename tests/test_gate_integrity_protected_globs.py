"""Regression coverage for normative inputs to the gate-integrity check."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_gate_integrity


class ProtectedGlobTests(unittest.TestCase):
    def test_exemption_registries_are_protected(self) -> None:
        registries = (
            "metadata/two_sided_exemptions.json",
            "metadata/judgement_constructors.json",
            "metadata/assumptions.json",
            "metadata/dependency_aliases.json",
        )

        for registry in registries:
            with self.subTest(registry=registry):
                self.assertTrue(verify_gate_integrity._is_protected(registry))

    def test_test_harness_is_protected(self) -> None:
        test_sources = (
            "tests/test_example.py",
            "tests/unit/test_nested_example.py",
            "tests/lean/Example.lean",
        )

        for source in test_sources:
            with self.subTest(source=source):
                self.assertTrue(verify_gate_integrity._is_protected(source))


if __name__ == "__main__":
    unittest.main()
