#!/usr/bin/env python3
"""Run independent repository gates in aggregate-report mode."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GATES = (
    "verify_editorial.py",
    "verify_dependencies.py",
    "verify_context_bundles.py",
)


def main() -> None:
    failures = []
    for gate in GATES:
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / gate), "--report-all"],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        if result.returncode:
            failures.append((gate, result.stderr.strip() or result.stdout.strip()))
    if failures:
        for gate, output in failures:
            print(f"preflight {gate}:\n{output}", file=sys.stderr)
        raise SystemExit(1)
    print(f"aggregate preflight passed ({len(GATES)} gates)")


if __name__ == "__main__":
    main()
