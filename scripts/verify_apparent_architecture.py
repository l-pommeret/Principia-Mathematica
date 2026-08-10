#!/usr/bin/env python3
"""Static guardrails for the conservative pre-✱9 syntax layer."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
APPARENT = ROOT / "Principia/Syntax/Apparent.lean"


def main() -> None:
    source = APPARENT.read_text(encoding="utf-8")
    code = code_without_comments_or_strings(source)
    required = (
        "abbrev BoundContext", "inductive BoundVar", "inductive Apparent",
        "def ofElementary", "def toElementary?", "def rename",
        "def substitute", "def instantiate", "def Significant",
        "inductive Quantified", "abbrev FirstOrder", "namespace FirstOrder",
        "abbrev always", "abbrev sometimes", "def neg",
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
        "derived existential encoding": r"def\s+(some|sometimes)[^\n]*:=\s*.*neg.*always",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, code, flags=re.MULTILINE)]
    if failures:
        raise SystemExit("apparent-syntax policy violation: " + ", ".join(failures))

    formula = (ROOT / "Principia/Syntax/Formula.lean").read_text(encoding="utf-8")
    system = (ROOT / "Principia/Deduction/System.lean").read_text(encoding="utf-8")
    if "Apparent" in formula or "Apparent" in system:
        raise SystemExit("the new layer leaked into Elementary or Derivation")
    if "| always" not in source or "| sometimes" not in source:
        raise SystemExit("the two primitive binding ideas are not distinct constructors")
    matrix_layer = source.split("inductive Quantified", maxsplit=1)[0]
    if re.search(r"^\s*\|\s+(all|sometimes)\b", matrix_layer, flags=re.MULTILINE):
        raise SystemExit("a quantified binder leaked into the elementary matrix layer")
    if "| .always body => .sometimes (matrixNeg body)" not in source:
        raise SystemExit("✱9·01 is not represented by a definitional reduction")
    if "| .sometimes body => .always (matrixNeg body)" not in source:
        raise SystemExit("✱9·02 is not represented by a definitional reduction")
    print("Apparent-variable architecture checks passed")


if __name__ == "__main__":
    main()
