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
        "def disjRightElementary", "def disjElementaryLeft",
        "theorem star_9_03_reduction", "theorem star_9_04_reduction",
        "theorem star_9_05_reduction", "theorem star_9_06_reduction",
        "def outerVariableRenaming", "def innerVariableRenaming",
        "abbrev SecondOrder", "def disjAlwaysSometimes",
        "def disjSometimesAlways", "theorem star_9_07_reduction",
        "theorem star_9_08_reduction",
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
    mixed_reductions = {
        "✱9·03": "disjRightElementary (always body) proposition",
        "✱9·04": "disjElementaryLeft proposition (always body)",
        "✱9·05": "disjRightElementary (sometimes body) proposition",
        "✱9·06": "disjElementaryLeft proposition (sometimes body)",
    }
    absent = [label for label, expression in mixed_reductions.items()
              if expression not in source]
    if absent:
        raise SystemExit("missing mixed-disjunction reductions: " + ", ".join(absent))
    assigned_order_contract = (
        "renameMatrix : {Δ Ξ : BoundContext}",
        "disjMatrix : {Δ : BoundContext}",
        "Apparent.outerVariableRenaming",
        "Apparent.innerVariableRenaming",
        "Quantified (Quantified Matrix)",
        "| .zero => .succ .zero",
        "| .zero => .zero",
        "theorem star_9_07_reduction",
        "theorem star_9_08_reduction",
    )
    missing_contract = [fragment for fragment in assigned_order_contract
                        if fragment not in source]
    if missing_contract:
        raise SystemExit("incomplete assigned-order ✱9·07/08 API: " +
                         ", ".join(missing_contract))
    print("Apparent-variable architecture checks passed")


if __name__ == "__main__":
    main()
