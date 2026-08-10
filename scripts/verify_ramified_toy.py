#!/usr/bin/env python3
"""Static guardrails for the isolated experimental ramified-type slice."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
TOY = ROOT / "Principia/Experimental/RamifiedToy.lean"


def main() -> None:
    source = TOY.read_text(encoding="utf-8")
    code = code_without_comments_or_strings(source)
    required = (
        "namespace PM.Experimental.RamifiedToy",
        "inductive RamifiedSort", "| individual", "| proposition", "| function",
        "def height", "def Predicative", "abbrev RealContext",
        "abbrev ApparentContext", "inductive Var", "inductive Term",
        "| real", "| apparent", "inductive Arguments", "inductive Formula",
        "| apply", "| always", "| sometimes", "NegationMeaning",
        "DisjunctionMeaning", "def instantiate", "inductive ToyDerivation",
        "inductive ElementaryMatrix", "structure ElementaryFunction",
        "def Term.abstractHead", "def Term.valueHead",
        "def valueHead", "def abstractHead", "theorem valueHead_abstractHead",
        "structure ScopedConnectives", "def disj00", "def disj01",
        "def disj10", "def disj11", "def imp00", "def imp01",
        "def imp10", "def imp11", "def normalImp01Sometimes",
        "def normalImp10Always", "structure ImplicationAt",
        "resultOrder : Nat", "def swapAbstractedWithBinder",
        "toy_star_9_1", "toy_star_9_11", "toy_star_9_12",
        "toy_star_9_13", "toy_star_10_1",
        "structure ReducibleAt", "def ramifiedFunctionOrder",
        "structure UnaryFormalEquivalence", "structure UnaryReducibility",
        "def reducedRepresentative", "def higherFunctionWitness",
        "def twoBinderFormulaWitness", "def higherToyStar10Witness",
        "def higherStar10WithReducibility", "def formalEquivalenceOrder",
        "def higherNonPredicativeEntry",
        "def higherNonPredicativeStar10Witness",
        "structure HigherStar10ReducibilityWitness",
        "theorem higherFunctionHeadRoundTrip",
        "def embedElementary", "def eraseElementary?",
        "theorem erase_embedElementary",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise SystemExit("incomplete ramified toy: " + ", ".join(missing))

    forbidden = {
        "accepted apparent dependency": r"^import\s+Principia\.Syntax\.Apparent",
        "accepted derivation dependency": r"^import\s+Principia\.Deduction",
        "global reducibility axiom": r"\baxiom\s+.*[Rr]educib",
        "global reducibility instance": r"\binstance\s+.*UnaryReducibility",
        "native semantic connective": r"\b(Classical|Exists|Forall)\b|[∀∃]",
        "all-orders connective": r"\b(negAt|disjAt|allOrders)\b",
        "generic implication helper": r"\bFormula\.imp\b|^\s*def\s+imp\s*\(",
        "canonical coverage namespace": r"namespace\s+PM\.FirstEdition",
        "invalid all-order eraser": r"\beraseElementaryAny\?\b",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, code, flags=re.MULTILINE)]
    if failures:
        raise SystemExit("ramified-toy policy violation: " + ", ".join(failures))

    accepted = (
        ROOT / "Principia/Syntax/Formula.lean",
        ROOT / "Principia/Syntax/Apparent.lean",
        ROOT / "Principia/Deduction/System.lean",
    )
    if any("RamifiedToy" in path.read_text(encoding="utf-8") for path in accepted):
        raise SystemExit("experimental ramified layer leaked into an accepted core module")
    if "formalEquivalence.formula entry.function (representative entry)" not in code:
        raise SystemExit("reducibility certificate is not tied to its representative")
    rules = code.split("inductive ToyDerivation", 1)[1].split(
        "def ramifiedFunctionOrder", 1)[0]
    if "Formula.disj" in rules or "signature.DisjunctionMeaning" in rules:
        raise SystemExit("toy rules bypass their certified scope-normal forms")
    if "{left right : Formula signature realContext [] operandOrder}" not in rules:
        raise SystemExit("toy detachment operands do not share one assigned order")
    if "ImplicationAt signature operandOrder" not in rules:
        raise SystemExit("toy detachment does not expose its assigned operand order")
    if "operation.normalize left right" not in rules:
        raise SystemExit("toy detachment bypasses its scope normalizer")
    if "ElementaryFunction" not in rules:
        raise SystemExit("toy primitive shapes are not restricted to elementary functions")
    if "(reducibility : UnaryReducibility" not in code:
        raise SystemExit("reducibility can be consumed without an explicit hypothesis")
    if "formalEquivalenceOrder argument resultOrder leftExcess rightExcess" not in code:
        raise SystemExit("formal equivalence order ignores a function excess")
    if "Sigma fun representative" not in code:
        raise SystemExit("the higher-order witness does not depend on its representative")
    if "reducibility.certificate higherNonPredicativeEntry" not in code:
        raise SystemExit("the higher-order witness ignores the reduction certificate")
    eraser = code.split("def eraseElementary?", 1)[1].split(
        "theorem erase_embedElementary", 1)[0]
    if "| .always _ => none" not in eraser or "| .sometimes _ => none" not in eraser:
        raise SystemExit("elementary erasure has uncovered quantified branches")
    print("Experimental ramified-type architecture checks passed")


if __name__ == "__main__":
    main()
