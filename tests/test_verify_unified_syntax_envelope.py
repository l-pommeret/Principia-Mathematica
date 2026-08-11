#!/usr/bin/env python3
"""Static guard for the syntax-only unified-envelope experiment.

This test deliberately does not invoke Lean.  It verifies the architectural
boundary required before a future consolidated CI compiles the experiment.
"""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Principia/Experimental/UnifiedSyntaxEnvelope.lean"


def test_unified_envelope_is_indexed_and_syntax_only() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    for required in (
        "inductive FamilyTag",
        "inductive Envelope",
        "| elementary",
        "| ordered",
        "| description",
        "retract_injectElementary",
        "retract_injectOrdered",
        "retractOrderedElementary?",
        "retract_injectOrderedElementary",
        "retract_injectDescription",
        "injectDescription_substitute",
        "injectDescription_weaken",
    ):
        assert required in text

    forbidden = (
        "inductive Judgement",
        "inductive Derivation",
        "axiom ",
        "opaque ",
        "Classical",
        "DescriptionTerm",
        "Primitive",
        "RuleBook",
    )
    for marker in forbidden:
        assert marker not in text


def test_no_common_carrier_coercion_is_claimed() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    assert "not a coercion" in text
    assert "no rename/substitute operation for `Elementary` or\n`OrderedFormula`" in text
