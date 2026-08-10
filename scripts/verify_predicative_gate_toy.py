#!/usr/bin/env python3
"""Guard the isolated φ!/reducibility architecture experiment."""

from pathlib import Path
import json
import re

from verify_lean_policy import code_without_comments_or_strings

ROOT = Path(__file__).resolve().parents[1]
TOY = ROOT / "Principia/Experimental/PredicativeGateToy.lean"
SOURCE_RECORD = ROOT / "metadata/experimental/pm1-star12-star13-predicative-gate.json"


def main() -> None:
    source = TOY.read_text(encoding="utf-8")
    source_record = json.loads(SOURCE_RECORD.read_text(encoding="utf-8"))
    code = code_without_comments_or_strings(source)
    required = (
        "inductive DeepFormula", "applyGeneral", "applyPredicative",
        "alwaysFunction", "sometimesFunction",
        ".function arguments resultOrder 0", "def DeepFormula.renameApparent",
        "def DeepFormula.renameReal", "def DeepFormula.substitute",
        "def DeepFormula.abstractHead", "def DeepFormula.valueHead",
        "theorem generalApply_ne_predicativeApply",
        "inductive DeepDerivation", "def unaryReducibilityFormula",
        ".sometimesFunction", ".alwaysFunction",
        ".applyGeneral (weakenApparent (weakenApparent function))",
        ".applyPredicative (.apparent (.succ .zero))",
        "structure UnaryReducibility12_1",
        "def binaryReducibilityFormula",
        "(weakenApparent (weakenApparent (weakenApparent function)))",
        ".applyPredicative (.apparent (.succ (.succ .zero)))",
        "structure BinaryReducibility12_11", "def star13_01Df",
        ".alwaysFunction", ".applyPredicative (.apparent .zero)",
        ".cons (weakenApparent x) .nil",
        ".cons (weakenApparent y) .nil",
        "def star13_101ReducibilityPremise",
        "reducibility.certificate",
        "56e8d8644f7db3d93d3a29d208fd75a5fc346a11c11fff337211ec9194f4cb79",
        "190549556ab8e2ca2c757baa0ed705181ade995cdc21742d5478a72ba25fb0ed",
        "4b4f4e557eba3e16e231f3e437af150fb6f347ea20b6602948f363432048227a",
        "377a277639f9d194f712cf5d0a88d5979b7243b26088b04133d0be91464b4960",
    )
    missing = [fragment for fragment in required if fragment not in source]
    if missing:
        raise SystemExit("incomplete predicative gate toy: " + ", ".join(missing))
    forbidden = {
        "global reducibility axiom": r"\baxiom\s+.*[Rr]educib",
        "global reducibility instance": r"\binstance\s+.*Reducibility",
        "variadic reducibility": r"structure\s+(Nary|Variadic|Ternary)Reducibility",
        "mark-erasing projection": r"\b(toFormula|eraseMark|forgetMark)\b",
        "markless certificate": r"\bToyDerivation\b",
        "accepted namespace claim": r"namespace\s+PM\.FirstEdition",
        "predicative positive excess":
            r"applyPredicative[\s\S]{0,160}\.function[^\n]*resultOrder\s+\([1-9]",
    }
    failures = [label for label, pattern in forbidden.items()
                if re.search(pattern, code, flags=re.MULTILINE)]
    if failures:
        raise SystemExit("predicative gate violation: " + ", ".join(failures))
    premise = code.split("def star13_101ReducibilityPremise", 1)[1]
    if "(reducibility : UnaryReducibility12_1" not in premise:
        raise SystemExit("✱13·101 premise lost its explicit ✱12·1 package")
    reducibility_blocks = re.findall(
        r"structure\s+\w*Reducibility\w*[\s\S]*?(?=\n(?:structure|def|theorem|end)\b)",
        code,
    )
    if len(reducibility_blocks) != 2:
        raise SystemExit("reducibility gate must expose exactly unary and binary packages")
    if any("List RamifiedSort" in block or ".function arguments" in block
           for block in reducibility_blocks):
        raise SystemExit("generic-list reducibility bypasses the ✱12·1/·11 arity gate")
    if re.search(r"structure\s+(Unary|Binary)Reducibility[\s\S]*?\brepresentative\s*:", code):
        raise SystemExit("✱12 was collapsed to a meta-level representative")
    if "DeepDerivation signature (unaryReducibilityFormula function)" not in premise:
        raise SystemExit("✱13·101 premise is not the printed existential formula")
    identity_df = code.split("def star13_01Df", 1)[1].split(
        "def star13_101ReducibilityPremise", 1)[0]
    if re.search(r"\(phi\s*:\s*Term", identity_df):
        raise SystemExit("✱13·01 leaves phi as a Lean parameter instead of binding it")
    if identity_df.count(".applyPredicative (.apparent .zero)") != 2:
        raise SystemExit("✱13·01 does not reuse one bound predicative function")
    if source_record.get("canonical_item_metadata") is not False:
        raise SystemExit("experimental source evidence was promoted to canonical metadata")
    if source_record["source_witnesses"]["project_gutenberg"].get("ebook") != 78050:
        raise SystemExit("Project Gutenberg witness is missing")
    for witness in ("canonical_scan", "project_gutenberg"):
        record = source_record["source_witnesses"][witness]
        if not record.get("uri", "").startswith("https://") or len(record.get("sha256", "")) != 64:
            raise SystemExit(f"{witness} URL/hash provenance is incomplete")
    if source_record["source_witnesses"]["wikisource"].get("page_transcription") != "absent":
        raise SystemExit("Wikisource absence is not recorded")
    evidence = source_record.get("architecture_ci", {})
    if evidence != {"commit": "pending", "run": "pending", "conclusion": "pending"}:
        if evidence.get("conclusion") != "success" or len(evidence.get("commit", "")) != 40:
            raise SystemExit("predicative gate CI evidence is missing or inconsistent")
    print("Experimental predicative/reducibility gate checks passed")


if __name__ == "__main__":
    main()
