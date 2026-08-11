#!/usr/bin/env python3
"""Run independent repository gates in aggregate-report mode."""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GATES = (
    ("editorial", ["verify_editorial.py", "--report-all"]),
    ("dependencies", ["verify_dependencies.py", "--report-all"]),
    ("contexts", ["verify_context_bundles.py", "--report-all"]),
    ("constrained-batches", ["verify_constrained_batches.py"]),
    ("errata-registry", ["verify_errata_registry.py"]),
    ("anomaly-registry", ["verify_anomaly_registry.py"]),
    ("apparent-architecture", ["verify_apparent_architecture.py"]),
    ("ordered-architecture", ["verify_ordered_architecture.py"]),
    ("substitution-architecture", ["verify_substitution_architecture.py"]),
    ("elementary-formation", ["verify_elementary_formation_toy.py"]),
    ("ramified-types", ["verify_ramified_toy.py"]),
    ("typical-ambiguity", ["verify_typical_ambiguity_toy.py"]),
    ("description-scope", ["verify_description_scope_toy.py"]),
    ("predicative-gate", ["verify_predicative_gate_toy.py"]),
    ("parser-coverage", ["verify_pm_parser_coverage.py"]),
    ("lean-policy", ["verify_lean_policy.py"]),
)


def main() -> None:
    failures = []

    def run_gate(name: str, command: list[str]) -> None:
        result = subprocess.run(
            command, cwd=ROOT, text=True, capture_output=True, check=False,
        )
        if result.returncode:
            failures.append((name, result.returncode, result.stderr.strip() or result.stdout.strip()))

    for name, command in GATES:
        run_gate(
            name,
            [sys.executable, str(ROOT / "scripts" / command[0]), *command[1:]],
        )
    run_gate("unit-tests", [sys.executable, "-m", "unittest", "discover", "-s", "tests"])
    with tempfile.TemporaryDirectory(prefix="pm-preflight-site-") as directory:
        site = Path(directory) / "site"
        run_gate("build-edition", [sys.executable, str(ROOT / "scripts/build_edition.py"),
                                    "--output", str(site)])
        run_gate("verify-site", [sys.executable, str(ROOT / "scripts/verify_site.py"),
                                   "--site", str(site)])
    run_gate("diff-check", ["git", "diff", "--check"])
    if failures:
        for name, exit_code, output in failures:
            print(f"preflight {name} (exit {exit_code}):\n{output}", file=sys.stderr)
        raise SystemExit(1)
    print(f"aggregate preflight passed ({len(GATES) + 4} gates)")


if __name__ == "__main__":
    main()
