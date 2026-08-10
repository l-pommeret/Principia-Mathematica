#!/usr/bin/env python3
"""Static guardrails for the conservative pre-✱9 syntax layer."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
APPARENT = ROOT / "Principia/Syntax/Apparent.lean"


def main() -> None:
    source = APPARENT.read_text(encoding="utf-8")
    required = (
        "abbrev BoundContext", "inductive BoundVar", "inductive Apparent",
        "def ofElementary", "def toElementary?", "def rename",
        "def substitute", "def instantiate", "def Significant",
    )
    missing = [item for item in required if item not in source]
    if missing:
        raise SystemExit("missing apparent-syntax declarations: " + ", ".join(missing))

    forbidden = {
        "deduction import": r"^import\s+Principia\.Deduction",
        "premature deduction system": r"\b(ApparentDerivation|inductive\s+Derivation)\b",
        "semantic quantifier": r"[∀∃]",
        "classical machinery": r"\b(Classical|Quot|Choice)\b",
        "invented all-orders index": r"\b(negAt|disjAt|allOrders)\b",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, source, flags=re.MULTILINE)]
    if failures:
        raise SystemExit("apparent-syntax policy violation: " + ", ".join(failures))

    formula = (ROOT / "Principia/Syntax/Formula.lean").read_text(encoding="utf-8")
    system = (ROOT / "Principia/Deduction/System.lean").read_text(encoding="utf-8")
    if "Apparent" in formula or "Apparent" in system:
        raise SystemExit("the new layer leaked into Elementary or Derivation")
    print("Apparent-variable architecture checks passed")


if __name__ == "__main__":
    main()
