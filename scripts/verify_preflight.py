#!/usr/bin/env python3
"""Run independent repository gates in aggregate-report mode."""

from __future__ import annotations

import subprocess
import sys
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
    for name, command in GATES:
        result = subprocess.run(
            [sys.executable, *(str(ROOT / "scripts" / part) if index == 0 else part
                               for index, part in enumerate(command))],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        if result.returncode:
            failures.append((name, result.returncode, result.stderr.strip() or result.stdout.strip()))
    if failures:
        for name, exit_code, output in failures:
            print(f"preflight {name} (exit {exit_code}):\n{output}", file=sys.stderr)
        raise SystemExit(1)
    print(f"aggregate preflight passed ({len(GATES)} gates)")


if __name__ == "__main__":
    main()
