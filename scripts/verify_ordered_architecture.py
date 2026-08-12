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
PREREQUISITES = ROOT / "Principia/Architecture/FirstOrderPrerequisites.lean"
CLOSED_RULEBOOK = ROOT / "Principia/Architecture/Q259ClosedRuleBook.lean"
APPARENT = ROOT / "Principia/Syntax/Apparent.lean"


def main() -> None:
    ordered = code_without_comments_or_strings(ORDERED.read_text(encoding="utf-8"))
    derivation = code_without_comments_or_strings(DERIVATION.read_text(encoding="utf-8"))
    targets = code_without_comments_or_strings(Q259.read_text(encoding="utf-8"))
    prerequisites = code_without_comments_or_strings(PREREQUISITES.read_text(encoding="utf-8"))
    closed_rulebook = code_without_comments_or_strings(CLOSED_RULEBOOK.read_text(encoding="utf-8"))
    apparent = code_without_comments_or_strings(APPARENT.read_text(encoding="utf-8"))
    required = (
        "inductive OrderedFormula", "| elementary", "| firstOrder",
        "| firstOrderMatrix", "| neg", "| disj",
        "inductive FirstOrderDisjunctionScope", "inductive OrderedDisjunctionScope",
        "def scopedDisj", "def scopedImp", "def scopedFirstOrderDisj", "def firstImp", "def secondImp",
        "def eraseElementary?", "theorem erase_embedElementary",
        "structure OrderedRuleBook", "Primitive : OrderedFormula",
        "inductive OrderedDerivation", "| primitive", "| detach",
        "def impElementaryToFirst",
        "inductive OrderedAssertion", "star_9_12_elementary_to_first", "star_9_12_second",
        "structure Q259ClosedRuleBook", "star_9_21", "star_9_25",
        "star_9_3_target", "star_9_31_target", "star_9_32_target", "star_9_33_target",
    )
    corpus = "\n".join((ordered, derivation, targets, prerequisites, closed_rulebook, apparent))
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
    if "scopedFirstOrderDisj .sameAssignedOrder" not in targets:
        raise SystemExit("Q259 order-one disjunction bypasses its scope certificate")
    if targets.count("FirstOrder.disjRightElementary") != 2:
        raise SystemExit("Q259 ✱9·32/33 must retain their printed final disjunction with q")
    if not re.search(
        r"star_9_32_target[\s\S]*?impElementaryToFirst q[\s\S]*?"
        r"disjRightElementary \(FirstOrder\.always φ\) q",
        targets,
    ):
        raise SystemExit("Q259 ✱9·32 target differs from the printed universal formula")
    if not re.search(
        r"star_9_33_target[\s\S]*?impElementaryToFirst q[\s\S]*?"
        r"disjRightElementary \(FirstOrder\.sometimes φ\) q",
        targets,
    ):
        raise SystemExit("Q259 ✱9·33 target differs from the printed existential formula")
    if "OrderedDisjunctionScope order" not in derivation:
        raise SystemExit("ordered detachment omits its disjunction scope certificate")
    if "| secondOrder : OrderedDisjunctionScope 2" not in ordered:
        raise SystemExit("order-two syntax lacks its explicit same-order scope certificate")
    if not re.search(
        r"def secondImp[\s\S]*?scopedImp \.secondOrder left right",
        ordered,
    ):
        raise SystemExit("order-two implication bypasses its scope certificate")
    if "| .disj .secondOrder _ _ => none" not in ordered:
        raise SystemExit("elementary erasure must reject order-two disjunctions")
    if "| .firstOrderMatrix _ => none" not in ordered:
        raise SystemExit("elementary erasure must reject first-order matrices")
    if not re.search(
        r"\|\s+star_9_12_second\s*\{p q : OrderedFormula Γ 2\}\s*:\s*"
        r"OrderedAssertion p\s*→\s*OrderedAssertion \(secondImp p q\)\s*→\s*"
        r"OrderedAssertion q",
        prerequisites,
    ):
        raise SystemExit("✱9·12 order-two specialization is absent or not scope-certified")
    if re.search(r"\|\s+star_9_12\w*\s*\{[^}]*order", prerequisites):
        raise SystemExit("✱9·12 must not become an order-polymorphic inference rule")
    if re.search(r"(?m)^\s+star_9_(?:3|31|32|33)\s*:", closed_rulebook):
        raise SystemExit("Q259 target appears as a closed-rulebook primitive")
    print("Ordered first-order architecture checks passed")


if __name__ == "__main__":
    try:
        main()
    except OSError as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
