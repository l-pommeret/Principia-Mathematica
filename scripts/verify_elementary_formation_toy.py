#!/usr/bin/env python3
"""Static guardrails for the explicit ✱1·7·71·72 formation experiment."""

from pathlib import Path
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
TOY = ROOT / "Principia/Experimental/ElementaryFormationToy.lean"
CORE = ROOT / "Principia/Deduction/Formation.lean"
FORMED = ROOT / "Principia/Deduction/Formed.lean"
SYSTEM = ROOT / "Principia/Deduction/System.lean"


def repository_source() -> str:
    return (CORE.read_text(encoding="utf-8") + "\n" +
            FORMED.read_text(encoding="utf-8") + "\n" +
            SYSTEM.read_text(encoding="utf-8") + "\n" +
            TOY.read_text(encoding="utf-8"))


def audit(source: str) -> None:
    code = code_without_comments_or_strings(source)
    required = (
        "inductive Formation",
        "| star_1_7 (hp : Formation p)",
        "| star_1_71 (hp : Formation (Γ := []) p)",
        "| star_1_72 (hasRealVariable : Γ ≠ [])",
        "def ofElementary",
        "| [], .disj p q => .star_1_71",
        "| (_ :: _), .disj p q =>",
        ".star_1_72 (List.cons_ne_nil _ _)",
        "structure FormedDerivation",
        "formation : Formation p",
        "derivation : Derivation p",
        "theorem star_3_03",
        "(hasRealVariable : Γ ≠ [])",
        "Formation.star_1_72 hasRealVariable notφ notψ",
        "formation := Formation.star_1_7 joined",
        "PM.Derivation.detach hφ.derivation implication",
        "PM.Derivation.detach hψ.derivation afterφ",
        "theorem star_3_03_derivation",
        "(star_3_03 hasRealVariable",
        "{ formation := Formation.ofElementary φ, derivation := hφ }",
        "{ formation := Formation.ofElementary ψ, derivation := hψ }).derivation",
        "def closedConjunctionFormation",
        "Formation.star_1_71",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise ValueError("incomplete elementary-formation toy: " + ", ".join(missing))

    constructors = re.findall(r"^\s*\|\s+(\w+)", _formation_block(code), re.MULTILINE)
    if constructors != ["constant", "realVar", "star_1_7", "star_1_71", "star_1_72"]:
        raise ValueError(f"unexpected Formation constructors: {constructors}")

    forbidden = {
        "generic disjunction formation": r"\|\s+(?:disj|or|sum)\b",
        "new assertion axiom": r"\baxiom\b",
        "semantic shortcut": r"\b(Classical|by_cases|decide)\b",
        "native conjunction": r"\bAnd\b",
        "placeholder": r"\b(sorry|admit)\b",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, code, re.MULTILINE)]
    if failures:
        raise ValueError("elementary-formation policy violation: " + ", ".join(failures))
    # The accepted calculus must remain a single inductive.  It is now named
    # `DerivationEvidence` and inhabited through `Derivation p := Nonempty …`;
    # the invariant this guards — no proliferation of accepted derivation
    # relations — is unchanged.
    accepted = re.findall(r"inductive\s+(?:PM\.)?Derivation(?:Evidence)?\b", code)
    if len(accepted) != 1:
        raise ValueError(
            f"the accepted Derivation inductive must remain unique, found {len(accepted)}"
        )


def _formation_block(code: str) -> str:
    match = re.search(
        r"inductive\s+Formation\b(?P<body>.*?)(?=\nnamespace\s+Formation)",
        code,
        re.DOTALL,
    )
    if not match:
        raise ValueError("Formation inductive block not found")
    return match.group("body")


def main() -> None:
    audit(repository_source())
    print("Experimental elementary-formation architecture checks passed")


if __name__ == "__main__":
    main()
