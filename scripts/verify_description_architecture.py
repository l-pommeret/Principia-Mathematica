#!/usr/bin/env python3
"""Static guardrails for canonical ✱14 contextual descriptions."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
CANONICAL = ROOT / "Principia/Syntax/Description.lean"
TOY = ROOT / "Principia/Experimental/DescriptionScopeToy.lean"


def main() -> None:
    source = CANONICAL.read_text(encoding="utf-8")
    code = code_without_comments_or_strings(source)
    required = (
        "namespace PM.DescriptionSyntax",
        "inductive Var",
        "inductive Term",
        "inductive CoreFormula",
        "inductive Formula",
        "| descriptionScope : DescriptionVocabulary",
        "(condition : Formula",
        "(continuation : Formula",
        "def conditionAtFreshSubstitution",
        "def uniquely",
        ".always vocabulary.universal (iff vocabulary conditionAtFresh equality)",
        "def expand : Formula",
        "theorem expand_descriptionScope",
        "def narrowDescriptionImplication",
        "def wideDescriptionImplication",
        "theorem narrowDescriptionImplication_shape",
        "theorem wideDescriptionImplication_shape",
        "consequent.weaken",
        "CoreFormula.uniquely vocabulary condition.expand",
        "continuation.expand",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise SystemExit("incomplete canonical description architecture: " + ", ".join(missing))

    forbidden = {
        "description promoted to a term": r"(?:inductive|structure|def|abbrev)\s+DescriptionTerm\b",
        "description term constructor": r"inductive\s+Term[\s\S]*?\|\s+description\b",
        "HOAS condition": r"condition\s*:\s*[^)\n]*→",
        "HOAS continuation": r"continuation\s*:\s*[^)\n]*→",
        "object formula as Lean Prop": r"(?:abbrev|def)\s+Formula[^:=]*:=\s*Prop\b",
        "global axiom": r"\baxiom\b",
        "experimental namespace": r"namespace\s+PM\.Experimental",
        "experimental dependency": r"import\s+Principia\.Experimental",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, code, flags=re.MULTILINE)]
    if failures:
        raise SystemExit("canonical description policy violation: " + ", ".join(failures))

    toy = TOY.read_text(encoding="utf-8")
    semantic_witnesses = (
        "def narrowDescriptionImplication",
        "def wideDescriptionImplication",
        "theorem implicationScopeReadings_haveDifferentTruthValues",
        "def nonDenoting",
    )
    absent = [fragment for fragment in semantic_witnesses if fragment not in toy]
    if absent:
        raise SystemExit("missing narrow/wide non-denoting witness: " + ", ".join(absent))

    print("Canonical ✱14 description architecture checks passed")


if __name__ == "__main__":
    main()
