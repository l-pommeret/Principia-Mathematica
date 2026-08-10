#!/usr/bin/env python3
"""Guard the editorial separation of schema and syntactic substitution."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]


def require(pattern: str, source: str, label: str) -> None:
    if not re.search(pattern, source, flags=re.MULTILINE | re.DOTALL):
        raise SystemExit(f"substitution architecture violation: {label}")


def main() -> None:
    system_source = (ROOT / "Principia/Deduction/System.lean").read_text(encoding="utf-8")
    formula_source = (ROOT / "Principia/Syntax/Formula.lean").read_text(encoding="utf-8")
    apparent_source = (ROOT / "Principia/Syntax/Apparent.lean").read_text(encoding="utf-8")
    note = (ROOT / "docs/SUBSTITUTION.md").read_text(encoding="utf-8")

    system = code_without_comments_or_strings(system_source)
    formula = code_without_comments_or_strings(formula_source)
    apparent = code_without_comments_or_strings(apparent_source)

    require(
        r"\|\s+star_1_1\s+\{p q : Elementary \[\]\}\s*:\s*"
        r"Derivation p\s*→\s*Derivation \(p ⊃ₚ q\)\s*→\s*Derivation q",
        system,
        "✱1·1 is not the empty-context primitive constructor",
    )
    require(
        r"\|\s+star_1_11\s+\{Γ : RealContext\}\s+\{φ ψ : Elementary Γ\}"
        r"\s*\(hasRealVariable : Γ ≠ \[\]\)\s*:\s*Derivation φ\s*→"
        r"\s*Derivation \(φ ⊃ₚ ψ\)\s*→\s*Derivation ψ",
        system,
        "✱1·11 is not the nonempty-real-context primitive constructor",
    )
    for historical in ("PM.Derivation.star_1_1", "PM.Derivation.star_1_11"):
        if historical not in system_source:
            raise SystemExit(f"uniform detach no longer exposes {historical}")

    if re.search(r"\b(def|abbrev)\s+(substitute|instantiate|Substitution)\b", formula):
        raise SystemExit("generic syntactic substitution leaked into Elementary")

    for operation in (
        "def rename", "abbrev Substitution", "def liftSubstitution",
        "def substitute", "def instantiateSubstitution", "def instantiate",
    ):
        if operation not in apparent_source:
            raise SystemExit(f"missing explicit apparent-syntax operation: {operation}")
    require(
        r"Quantified\.always body =>\s*Quantified\.always\s*"
        r"\(Apparent\.substitute \(Apparent\.liftSubstitution σ\) body\)",
        apparent,
        "substitution is not lifted under always",
    )
    require(
        r"Quantified\.sometimes body =>\s*Quantified\.sometimes\s*"
        r"\(Apparent\.substitute \(Apparent\.liftSubstitution σ\) body\)",
        apparent,
        "substitution is not lifted under sometimes",
    )

    for phrase in (
        "Schematic instantiation in ✱1–✱5",
        "✱1·1 and ✱1·11 are primitive inference rules",
        "Object-syntactic substitution from ✱9 onward",
        "historical controversy",
    ):
        if phrase not in note:
            raise SystemExit(f"substitution editorial note lost required section: {phrase}")

    print("Substitution architecture checks passed")


if __name__ == "__main__":
    main()
