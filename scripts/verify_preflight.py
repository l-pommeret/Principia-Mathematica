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
    # First, and deliberately so.  Every gate below judges the edition; this one
    # judges the gates.  If a verifier has been edited without the editor's
    # express authorisation, nothing the others report can be trusted, so the
    # answer to "did the checks pass?" has to begin with "are these still the
    # checks?".
    ("gate-integrity", ["verify_gate_integrity.py", "--report-all"]),
    ("lean-source-coverage", ["report_lean_source_coverage.py", "--verify-pipeline"]),
    ("editorial", ["verify_editorial.py", "--report-all"]),
    ("dependencies", ["verify_dependencies.py", "--report-all"]),
    ("contexts", ["verify_context_bundles.py", "--report-all"]),
    ("constrained-batches", ["verify_constrained_batches.py"]),
    ("errata-registry", ["verify_errata_registry.py"]),
    ("anomaly-registry", ["verify_anomaly_registry.py"]),
    ("apparent-architecture", ["verify_apparent_architecture.py"]),
    ("elementary-formation", ["verify_elementary_formation_toy.py"]),
    ("typical-ambiguity", ["verify_typical_ambiguity_toy.py"]),
    ("description-scope", ["verify_description_scope_toy.py"]),
    ("description-architecture", ["verify_description_architecture.py"]),
    ("predicative-gate", ["verify_predicative_gate_toy.py"]),
    ("parser-coverage", ["verify_pm_parser_coverage.py"]),
    ("lean-policy", ["verify_lean_policy.py"]),
    # Certification gates.  These decide what `formal_status` a catalogue item
    # is allowed to claim, so they must run on every commit, not only on the
    # commits that happen to touch Lean sources.
    ("certification-tier", ["verify_certification_tier.py", "--check"]),
    ("ci-evidence", ["verify_ci_evidence.py", "--report-all"]),
    ("judgement-primitives", ["verify_judgement_primitives.py", "--report-all"]),
    # Previously written but wired nowhere, so they enforced nothing while
    # suggesting coverage.  Their invariants are still live, so they are
    # connected rather than archived.
    ("statement-only-interfaces", ["verify_statement_only_interfaces.py"]),
    ("experimental-interfaces", ["verify_architecture_experimental_interfaces.py"]),
    ("q301-gate", ["verify_q301_gate.py"]),
    ("second-order-bridge", ["verify_second_order_bridge.py"]),
    ("retry-registry", ["verify_retry_registry.py"]),
    # PM's system must stand on its own primitives; Lean is only the
    # metalanguage that checks the work.  The textual half runs here because it
    # needs no build: it catches the library-consulting tactic *before* it
    # becomes an axiom dependency, and it catches it in infrastructure lemmas
    # that no catalogue item references yet — which is precisely how
    # `Nat.max_self` carried `propext` into every ramified connective while the
    # catalogued-declaration audit stayed green.
    # A proposition PM prints as an equivalence has two sides to prove.  Three
    # theorems were written whose statement named one side twice, collapsing to
    # `N ≡ N` — pure, in PM's notation, compiling, and false to the page.  Every
    # other gate is blind to it: the axiom audit sees a pure proof, T11 sees PM's
    # connectives, and T4 compares the printed string against the already
    # collapsed AST it is handed.
    ("two-sided-readings", ["verify_two_sided_readings.py", "--report-all"]),
    (
        "library-independence",
        ["verify_library_independence.py", "--tactics-only", "--report-all"],
    ),
)
# Two gates are deliberately absent from GATES because they shell out to
# `lake env lean` and therefore need a warm `.lake/build`: the axiom audit, and
# the printed-citation check that asks whether a proof follows the demonstration
# PM prints rather than merely reaching the printed proposition.  The workflows
# run both as serial steps after `lake build`, never from here.
EXCLUDED_GATES = ("verify_axiom_audit.py", "verify_printed_citations.py")

# `verify_library_independence.py` appears in GATES above, but only in its
# textual `--tactics-only` form, which needs no build.  Its kernel half — one
# `#print axioms` for every declaration of the object calculus, catalogued or
# not — is a post-build step alongside EXCLUDED_GATES, since it shells out to
# `lake env lean` in the same way.
POST_BUILD_GATES = (
    "verify_axiom_audit.py",
    "verify_printed_citations.py",
    ("verify_library_independence.py", "--report-all"),
)


def missing_gate_scripts() -> list[str]:
    """Return the ``name: path`` of every configured gate with no script."""
    return [
        f"{name}: scripts/{command[0]}"
        for name, command in GATES
        if not (ROOT / "scripts" / command[0]).is_file()
    ]


def main() -> None:
    failures: list[tuple[str, int, str]] = []
    # An empty or partially installed gate set must never pass vacuously: a
    # missing script would otherwise raise deep inside the executor and report
    # as an opaque traceback rather than as a named gate failure.
    if not GATES:
        print("preflight is configured with no gates", file=sys.stderr)
        raise SystemExit(1)
    missing = missing_gate_scripts()
    if missing:
        print(
            "preflight gate scripts are missing:\n  " + "\n  ".join(missing),
            file=sys.stderr,
        )
        raise SystemExit(1)

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
