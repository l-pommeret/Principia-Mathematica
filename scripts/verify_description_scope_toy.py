#!/usr/bin/env python3
"""Static guardrails for the incomplete-symbol/scope experiment."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
TOY = ROOT / "Principia/Experimental/DescriptionScopeToy.lean"


def main() -> None:
    source = TOY.read_text(encoding="utf-8")
    code = code_without_comments_or_strings(source)
    required = (
        "inductive Formula where",
        "| descriptionScope :",
        "(condition : Object → Formula)",
        "(continuation : Object → Formula)",
        "def expand : Formula → CoreFormula",
        "def negOutsideDescription",
        "def negInsideDescription",
        "theorem negOutsideDescription_isTrue",
        "theorem negInsideDescription_isFalse",
        "theorem scopeReadings_haveDifferentTruthValues",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise SystemExit("incomplete description-scope toy: " + ", ".join(missing))

    forbidden = {
        "description promoted to a term":
            r"(?:inductive|structure|def|abbrev)\s+DescriptionTerm\b",
        "description-valued formula constructor":
            r"\|\s+description\s*:[^\n]*→\s*(?:Object|Term)",
        "global axiom": r"\baxiom\b",
        "accepted edition namespace": r"namespace\s+PM\.FirstEdition",
        "syntax-only separation":
            r"scopeReadings_haveDifferentTruthValues[^:]*:\s*negOutsideDescription\s*≠",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, code, flags=re.MULTILINE)]
    if failures:
        raise SystemExit("description-scope policy violation: " + ", ".join(failures))

    print("Experimental description-scope architecture checks passed")


if __name__ == "__main__":
    main()
