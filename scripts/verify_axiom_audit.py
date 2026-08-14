#!/usr/bin/env python3
"""Kernel-level axiom audit: what each catalogued declaration actually assumes.

``scripts/verify_lean_policy.py`` is a textual sieve; it can only see what is
written.  This gate asks the kernel instead.  ``#print axioms D`` reports the
axioms ``D``'s proof term depends on transitively, so a proof that reaches an
assumption through ten helper lemmas is caught exactly as one that states it.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ITEMS = ROOT / "metadata" / "items"

#: Axioms a tier-MAX declaration may depend on.
#:
#: Empty by intent.  The reconstructed object calculus is an inductive family
#: over an inductive syntax; deriving a printed PM proposition inside it needs no
#: classical principle.  ``Classical.choice`` in particular must never appear:
#: PM's propositional fragment is constructive as printed, so its presence would
#: mean the Lean proof took a route the printed demonstration does not license.
#: ``sorryAx`` is a hard failure everywhere, at every tier.
ALLOWED_AXIOMS: frozenset[str] = frozenset()

#: Axioms that are never acceptable, whatever the tier.
FORBIDDEN_ANYWHERE = frozenset({"sorryAx"})

_NO_AXIOMS = re.compile(r"^'([^']+)' does not depend on any axioms")
_DEPENDS = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]")


class ToolchainError(RuntimeError):
    """Raised when the audit could not be performed at all."""


def audit_declarations(declarations: list[str]) -> dict[str, list[str]]:
    """Map each declaration to the axioms it depends on.

    An empty list means the declaration is axiom-free.  A declaration Lean
    cannot resolve is reported with the sentinel ``['<unresolved>']`` rather
    than omitted: silence about a name the catalogue claims exists would be the
    exact failure this gate exists to prevent.
    """
    if not declarations:
        raise ToolchainError("no declarations to audit")

    unique = sorted(set(declarations))
    body = "\n".join(f"#print axioms {name}" for name in unique)
    program = f"import Principia\n\nset_option maxHeartbeats 1000000\n\n{body}\n"

    with tempfile.TemporaryDirectory(prefix="pm-axiom-audit-") as directory:
        probe = Path(directory) / "AxiomAudit.lean"
        probe.write_text(program, encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    combined = result.stdout + "\n" + result.stderr
    if "unknown package" in combined or "no such file" in combined.lower():
        raise ToolchainError(
            "`lake env lean` could not resolve the Principia library; run "
            f"`lake build` first.\n{combined.strip()[:2000]}"
        )

    found: dict[str, list[str]] = {}
    for line in combined.splitlines():
        line = line.strip()
        clean = _NO_AXIOMS.match(line)
        if clean:
            found[clean.group(1)] = []
            continue
        depends = _DEPENDS.match(line)
        if depends:
            axioms = [
                axiom.strip()
                for axiom in depends.group(2).split(",")
                if axiom.strip()
            ]
            found[depends.group(1)] = axioms

    if not found:
        raise ToolchainError(
            "`#print axioms` produced no parsable output; the audit did not "
            f"run.\n{combined.strip()[:2000]}"
        )

    for name in unique:
        found.setdefault(name, ["<unresolved>"])
    return found


def catalogued_declarations(statuses: set[str]) -> dict[str, list[str]]:
    """Declarations to audit, mapped to the item ids that claim them."""
    claimed: dict[str, list[str]] = {}
    for path in sorted(ITEMS.glob("*.json")):
        batch = json.loads(path.read_text(encoding="utf-8"))
        for item in batch.get("items", []):
            if item.get("formal_status") not in statuses:
                continue
            declaration = item.get("declaration")
            if isinstance(declaration, str) and declaration:
                claimed.setdefault(declaration, []).append(item.get("id"))
    return claimed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--status",
        action="append",
        default=None,
        help="formal_status to audit (repeatable; default: kernel-checked)",
    )
    parser.add_argument(
        "--report", action="store_true", help="print every result, then exit 0"
    )
    arguments = parser.parse_args()
    statuses = set(arguments.status or ["kernel-checked"])

    claimed = catalogued_declarations(statuses)
    if not claimed:
        # Not a vacuous pass: if nothing claims the audited statuses the caller
        # asked the wrong question, and a silent success would hide that.
        print(
            f"no catalogue item carries formal_status in {sorted(statuses)}; "
            "nothing was audited",
            file=sys.stderr,
        )
        return 1

    try:
        results = audit_declarations(list(claimed))
    except ToolchainError as error:
        print(f"axiom audit could not run: {error}", file=sys.stderr)
        return 1

    failures: list[str] = []
    for declaration, axioms in sorted(results.items()):
        owners = ", ".join(claimed.get(declaration, []))
        if arguments.report:
            print(f"{declaration}: {axioms or 'axiom-free'}  [{owners}]")
        if axioms == ["<unresolved>"]:
            failures.append(
                f"{declaration} ({owners}) could not be resolved by Lean; the "
                "catalogue claims a declaration the build does not contain"
            )
            continue
        forbidden = [axiom for axiom in axioms if axiom in FORBIDDEN_ANYWHERE]
        disallowed = [axiom for axiom in axioms if axiom not in ALLOWED_AXIOMS]
        if forbidden:
            failures.append(f"{declaration} ({owners}) depends on {forbidden}")
        elif disallowed:
            failures.append(
                f"{declaration} ({owners}) depends on {disallowed}, outside the "
                f"allowed set {sorted(ALLOWED_AXIOMS) or '(empty)'}"
            )

    if arguments.report:
        return 0
    if failures:
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        print(
            f"\n{len(failures)} of {len(results)} audited declarations depend on "
            "axioms they may not use",
            file=sys.stderr,
        )
        return 1
    print(f"axiom audit passed ({len(results)} declarations, no axioms)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
