#!/usr/bin/env python3
"""Static conservative-contract checks for the assigned-order core."""

from pathlib import Path
import re
import sys

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
ORDERED = ROOT / "Principia/Syntax/Ordered.lean"
DERIVATION = ROOT / "Principia/Deduction/Ordered.lean"
Q259 = ROOT / "Principia/Architecture/FirstOrderQ259.lean"
APPARENT = ROOT / "Principia/Syntax/Apparent.lean"


def main() -> None:
    ordered = code_without_comments_or_strings(ORDERED.read_text(encoding="utf-8"))
    derivation = code_without_comments_or_strings(DERIVATION.read_text(encoding="utf-8"))
    targets = code_without_comments_or_strings(Q259.read_text(encoding="utf-8"))
    apparent = code_without_comments_or_strings(APPARENT.read_text(encoding="utf-8"))
    required = (
        "inductive OrderedFormula", "| elementary", "| firstOrder", "| neg", "| disj",
        "def eraseElementary?", "theorem erase_embedElementary",
        "structure OrderedRuleBook", "Primitive : OrderedFormula",
        "inductive OrderedDerivation", "| primitive", "| detach", "| elementary",
        "def embedElementary", "def impElementaryToFirst",
        "star_9_3_target", "star_9_31_target", "star_9_32_target", "star_9_33_target",
    )
    corpus = "\n".join((ordered, derivation, targets, apparent))
    missing = [entry for entry in required if entry not in corpus]
    if missing:
        raise SystemExit("incomplete ordered architecture: " + ", ".join(missing))
    forbidden = r"\b(sorry|admit|axiom|Classical|Exists|Forall)\b|[∀∃]"
    if re.search(forbidden, corpus):
        raise SystemExit("ordered architecture contains a forbidden proof or semantic escape")
    formula = (ROOT / "Principia/Syntax/Formula.lean").read_text(encoding="utf-8")
    system = (ROOT / "Principia/Deduction/System.lean").read_text(encoding="utf-8")
    if "OrderedFormula" in formula or "OrderedDerivation" in system:
        raise SystemExit("ordered core leaked into the elementary kernel")
    print("Ordered first-order architecture checks passed")


if __name__ == "__main__":
    try:
        main()
    except OSError as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
