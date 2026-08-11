#!/usr/bin/env python3
"""Static negative checks for the single assigned 1→2 ✱9 bridge."""

from pathlib import Path
import re
import sys

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
APPARENT = ROOT / "Principia/Syntax/Apparent.lean"
ORDERED = ROOT / "Principia/Syntax/Ordered.lean"
PREREQUISITES = ROOT / "Principia/Architecture/FirstOrderPrerequisites.lean"


def require(source: str, fragments: tuple[str, ...], label: str) -> None:
    absent = [fragment for fragment in fragments if fragment not in source]
    if absent:
        raise SystemExit(f"{label} is incomplete: {', '.join(absent)}")


def main() -> None:
    apparent = code_without_comments_or_strings(APPARENT.read_text(encoding="utf-8"))
    ordered = code_without_comments_or_strings(ORDERED.read_text(encoding="utf-8"))
    prerequisites = code_without_comments_or_strings(
        PREREQUISITES.read_text(encoding="utf-8")
    )

    require(apparent, (
        "def abstractRealHead", "def openRealHead",
        "theorem openRealHead_abstractRealHead",
        "namespace FirstOrder", "def renameReal",
    ), "capture-safe first-order scope bridge")
    require(ordered, (
        "| secondOrder : SecondOrder Γ [] → OrderedFormula Γ 2",
        "def alwaysFirstOrder", "| .secondOrder _ => none",
    ), "exact order-two formula constructor")
    require(prerequisites, (
        "private structure MatrixSyntaxAt", "private def firstOrderMatrixSyntaxAt : MatrixSyntaxAt 1",
        "def firstOrderToSecondAll", "theorem firstOrderToSecondAll_reduction",
        "closedFirstOrderAlphaRenaming", "theorem closedFirstOrder_alpha",
        "| star_9_13_first", "FirstOrder.openRealHead φ",
    ), "sealed assigned 1→2 generalization")

    forbidden = {
        "unsealed all-orders instance": r"(?m)^\s*(?:def|theorem|axiom)\s+\w*(?:allOrders|generalizeAt|matrixSyntaxAt)\b",
        "extra MatrixSyntaxAt instance": r"(?m)^\s*(?:private\s+)?def\s+\w+\s*:\s*MatrixSyntaxAt\s+(?!1\b)",
        "semantic/object escape": r"\b(?:Classical|axiom|sorry|admit|unsafe|Forall|Exists)\b|[∀∃]",
        "generic order-two assertion rule": r"\|\s+star_9_13\w*\s*\{[^}]*order",
    }
    corpus = "\n".join((apparent, ordered, prerequisites))
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, corpus)]
    if failures:
        raise SystemExit("forbidden second-order bridge feature: " + ", ".join(failures))
    if prerequisites.count("MatrixSyntaxAt 1") != 1:
        raise SystemExit("the sealed bridge must expose exactly one MatrixSyntaxAt 1 instance")
    if "OrderedAssertion (firstOrderToSecondAll φ)" not in prerequisites:
        raise SystemExit("✱9·13 first-order instance does not conclude the fixed 1→2 target")
    print("Assigned 1→2 Star 9 bridge checks passed")


if __name__ == "__main__":
    try:
        main()
    except OSError as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
