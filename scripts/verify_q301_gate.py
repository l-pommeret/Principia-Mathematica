#!/usr/bin/env python3
"""Audit the non-executable sequential remap gate for ✱9·23 and ✱9·25."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "aristotle/manifests/Q301.json"
PROMPT = ROOT / "aristotle/Q301.md"
REVIEW = ROOT / "reviews/Q301-review.md"
STAR9 = ROOT / "Principia/FirstEdition/Volume1/Star9.lean"


def fail(message: str) -> None:
    raise SystemExit(f"Q301 gate error: {message}")


def main() -> None:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("kind") != "pm-sequential-remap-gate":
        fail("wrong manifest kind")
    if manifest.get("audit_status") != "A-interface-only":
        fail("audit is not interface-only")
    if manifest.get("submission_prohibited") is not True:
        fail("submission must remain prohibited")
    if manifest.get("promotion_prohibited") is not True:
        fail("promotion must remain prohibited")
    source = manifest.get("canonical_source", {})
    if source.get("scan_sha256") != "bd0e3af38b946e64c1f6d9a59d95d427ff9dac0fef26f9f7f7898896ea1ddcab":
        fail("wrong leaf-162 witness hash")
    targets = manifest.get("targets_in_order")
    if not isinstance(targets, list) or [target.get("id") for target in targets] != [
        "PM1:✱9·23", "PM1:✱9·25"
    ]:
        fail("target order is not ✱9·23 then ✱9·25")
    expected = {
        "PM1:✱9·23": {"PM1:✱2·08", "PM1:✱9·13", "PM1:✱9·21"},
        "PM1:✱9·25": {"PM1:✱9·23", "PM1:✱9·04"},
    }
    for target in targets:
        identifier = target["id"]
        if set(target.get("exact_dependencies", [])) != expected[identifier]:
            fail(f"wrong dependencies for {identifier}")
        if "theorem " not in target.get("signature", ""):
            fail(f"target {identifier} has no theorem signature")
    contract = manifest.get("q300_remap_contract", {})
    if contract.get("expected_declaration") != (
        "PM.Architecture.FirstOrderPrerequisites.star_9_21"
    ):
        fail("Q300 declaration remap changed")
    if "no executable opaque declaration" not in contract.get("opaque_interface_policy", ""):
        fail("Q300 contract permits an executable opaque theorem")
    if (ROOT / "aristotle/contexts/Q301.lean").exists():
        fail("Q301 must not materialize an axiom-backed context before Q300 remap")
    verbatim = STAR9.read_text(encoding="utf-8")
    for marker in ("PM-VERBATIM-BEGIN PM1:✱9·23", "PM-VERBATIM-BEGIN PM1:✱9·25"):
        if marker not in verbatim:
            fail(f"missing canonical source marker {marker}")
    prompt = PROMPT.read_text(encoding="utf-8")
    review = REVIEW.read_text(encoding="utf-8")
    for fragment in (
        "PM.FirstEdition.Volume1.Star2.star_2_08",
        "star_9_21 φ φ",
        "Apparent.ofElementary p ∨ₐ φ",
        "A-interface-only",
        "submission prohibited",
    ):
        if fragment not in (prompt + review):
            fail(f"missing audit fragment {fragment!r}")
    print("Q301 sequential remap gate checks passed")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
