#!/usr/bin/env python3
"""Static checks for the ramified 1→2 instance of the ✱9 bridge."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
RAMIFIED = ROOT / "Principia/Syntax/Ramified.lean"
STAR9 = ROOT / "Principia/Deduction/Star9Derived.lean"


def load_code(path: Path, label: str) -> str:
    """Read one required bridge component with a policy-level diagnostic."""
    relative = path.relative_to(ROOT)
    if not path.is_file():
        raise SystemExit(f"missing {label}: {relative}")
    try:
        source = path.read_text(encoding="utf-8")
    except OSError as error:
        raise SystemExit(f"cannot read {label} {relative}: {error}") from None
    return code_without_comments_or_strings(source)


def section(source: str, start: str, end: str, label: str) -> str:
    """Select a declaration range, naming the absent boundary if it moved."""
    if start not in source:
        raise SystemExit(f"{label} is missing its opening declaration: {start}")
    tail = source[source.index(start):]
    if end not in tail:
        raise SystemExit(f"{label} is missing its closing declaration: {end}")
    return tail[:tail.index(end)]


def require(source: str, fragments: tuple[str, ...], label: str) -> None:
    absent = [fragment for fragment in fragments if fragment not in source]
    if absent:
        raise SystemExit(f"{label} is incomplete: {', '.join(absent)}")


def main() -> None:
    ramified = load_code(RAMIFIED, "ramified formula and deduction calculus")
    star9 = load_code(STAR9, "ramified ✱9 interface")

    formula = section(
        ramified, "inductive Formula", "abbrev Renaming",
        "intrinsically ordered formula syntax",
    )
    primitive_bridge = section(
        ramified, "  | star_9_1", "  | star_10_1",
        "ramified primitive ✱9 bridge",
    )
    public_bridge = section(
        star9, "abbrev Star9Assertion", "def star_9_14_reading",
        "public ramified ✱9 bridge",
    )

    require(ramified, (
        "| .proposition order => order",
        "def bindOrder (matrixOrder : Nat) (sort : RSort) : Nat :=",
        "max matrixOrder (Nat.succ sort.height)",
        "def Formula.substitute",
        "body.substitute (liftSubstitution sigma)",
        "def Formula.instantiate",
        "body.substitute (instantiateSubstitution argument)",
        "def Formula.weakenReal",
    ), "capture-safe ramified scope operations")
    require(formula, (
        "Formula signature real apparent (bindOrder matrixOrder sort)",
        "| always : signature.Universal sort matrixOrder",
        "Formula signature real (sort :: apparent) matrixOrder",
    ), "intrinsically computed quantifier order")
    require(primitive_bridge, (
        "| star_9_12 {leftOrder rightOrder implicationOrder : Nat}",
        "{p : Formula signature real [] leftOrder}",
        "{q : Formula signature real [] rightOrder}",
        "[ImplicationReading negation disjunction p implicationFormula q]",
        "Derivation (.assertion q)",
        "| star_9_13 {argument : RSort} {matrixOrder : Nat}",
        "(body : Formula signature real [argument] matrixOrder)",
        "body.weakenReal.instantiate",
        "(.real (.zero : Var (argument :: real) argument))",
        "Derivation (.assertion (.always universal body))",
    ), "typed ramified generalization and detachment")
    require(public_bridge, (
        "abbrev Star9Assertion",
        "theorem star_9_12",
        "have line3 := Derivation.star_9_12 negation disjunction line1 line2",
        "theorem star_9_13",
        "have line2 := Derivation.star_9_13 universal body line1",
    ), "public ✱9·12/✱9·13 bridge")

    forbidden = {
        "retired Architecture bridge scaffold":
            r"\b(?:MatrixSyntaxAt|firstOrderToSecondAll|OrderedAssertion|"
            r"star_9_12_second|star_9_13_first)\b",
        "semantic/object escape":
            r"\b(?:Classical|axiom|sorry|admit|unsafe|Forall|Exists)\b|[∀∃]",
        "arbitrary order promotion":
            r"\b(?:castOrder|generalizeAt|liftOrder|promoteOrder)\b",
    }
    corpus = "\n".join((formula, primitive_bridge, public_bridge))
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, corpus)]
    if failures:
        raise SystemExit("forbidden ramified second-order bridge feature: " +
                         ", ".join(failures))
    if primitive_bridge.count("| star_9_12 ") != 1:
        raise SystemExit("the ramified calculus must expose exactly one ✱9·12 primitive")
    if primitive_bridge.count("| star_9_13 ") != 1:
        raise SystemExit("the ramified calculus must expose exactly one ✱9·13 primitive")

    print("Ramified 1→2 Star 9 bridge checks passed")


if __name__ == "__main__":
    main()
