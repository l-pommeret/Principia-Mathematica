#!/usr/bin/env python3
"""Run independent repository gates in aggregate-report mode."""

from __future__ import annotations

import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GATES = (
    ("lean-source-coverage", ["report_lean_source_coverage.py", "--verify-pipeline"]),
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
    ("description-architecture", ["verify_description_architecture.py"]),
    ("predicative-gate", ["verify_predicative_gate_toy.py"]),
    ("parser-coverage", ["verify_pm_parser_coverage.py"]),
    ("lean-policy", ["verify_lean_policy.py"]),
)


def main() -> None:
    failures = []

    def run_gate(name: str, command: list[str]) -> tuple[str, int, str] | None:
        result = subprocess.run(
            command, cwd=ROOT, text=True, capture_output=True, check=False,
        )
        if result.returncode:
            return name, result.returncode, result.stderr.strip() or result.stdout.strip()
        return None

    independent = [
        (
            name,
            [sys.executable, str(ROOT / "scripts" / command[0]), *command[1:]],
        )
        for name, command in GATES
    ]
    independent.append(
        ("unit-tests", [sys.executable, "-m", "unittest", "discover", "-s", "tests"])
    )
    # These gates only read repository state and are independent.  Keep the
    # worker count modest so CI remains deterministic on the two-core runner.
    with ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(lambda gate: run_gate(*gate), independent))
    failures.extend(result for result in results if result is not None)
    with tempfile.TemporaryDirectory(prefix="pm-preflight-site-") as directory:
        site = Path(directory) / "site"
        build_failure = run_gate(
            "build-edition",
            [sys.executable, str(ROOT / "scripts/build_edition.py"), "--output", str(site)],
        )
        if build_failure is not None:
            failures.append(build_failure)
        else:
            site_failure = run_gate(
                "verify-site",
                [sys.executable, str(ROOT / "scripts/verify_site.py"), "--site", str(site)],
            )
            if site_failure is not None:
                failures.append(site_failure)
    diff_failure = run_gate("diff-check", ["git", "diff", "--check"])
    if diff_failure is not None:
        failures.append(diff_failure)
    if failures:
        for name, exit_code, output in failures:
            print(f"preflight {name} (exit {exit_code}):\n{output}", file=sys.stderr)
        raise SystemExit(1)
    print(f"aggregate preflight passed ({len(GATES) + 4} gates)")


if __name__ == "__main__":
    main()
