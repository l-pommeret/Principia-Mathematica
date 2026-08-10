#!/usr/bin/env python3
"""Static guardrails for the isolated typical-ambiguity experiment."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
TOY = ROOT / "Principia/Experimental/TypicalAmbiguityToy.lean"


def main() -> None:
    source = TOY.read_text(encoding="utf-8")
    code = code_without_comments_or_strings(source)
    required = (
        "import Principia.Experimental.RamifiedToy",
        "inductive ClassSymbol : RamifiedSort → Type",
        "def classSchema (memberSort : RamifiedSort)",
        "def closedClassSchema (memberSort : RamifiedSort)",
        "def individualClassInstance",
        "closedClassSchema individualSort",
        "def predicativeFunctionClassInstance",
        "closedClassSchema predicateSort",
        "def instantiateClassSchema {memberSort : RamifiedSort}",
        "Term classSignature [] [] memberSort",
        "theorem noIndividualPredicateSortIdentification",
        "individualSort ≠ predicateSort",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise SystemExit("incomplete typical-ambiguity toy: " + ", ".join(missing))

    if len(re.findall(r"^def\s+classSchema\b", code, flags=re.MULTILINE)) != 1:
        raise SystemExit("the class proposition schema must be declared exactly once")

    forbidden = {
        "Lean-only type schema": r"classSchema\s*\{[^}]*:\s*Type",
        "unsafe cross-type cast": r"\b(unsafeCast|cast|Eq\.mp|Eq\.rec)\b",
        "global axiom": r"\baxiom\b",
        "accepted edition namespace": r"namespace\s+PM\.FirstEdition",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, code, flags=re.MULTILINE)]
    if failures:
        raise SystemExit("typical-ambiguity policy violation: " + ", ".join(failures))

    print("Experimental typical-ambiguity architecture checks passed")


if __name__ == "__main__":
    main()
