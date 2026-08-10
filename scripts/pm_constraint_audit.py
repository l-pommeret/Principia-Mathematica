#!/usr/bin/env python3
"""Classify a reconstructed proof against a strict PM prover manifest."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


class ReconstructionAuditError(ValueError):
    pass


def classify_reconstruction(manifest: dict, used_pm_items: list[str]) -> dict:
    if manifest.get("kind") != "pm-constrained-prover-manifest":
        raise ReconstructionAuditError("not a PM constrained-prover manifest")
    if len(used_pm_items) != len(set(used_pm_items)):
        raise ReconstructionAuditError("used PM items must be unique")

    used = set(used_pm_items)
    allowed = set(manifest["allowed_pm_items"])
    extra = sorted(used - allowed)
    unused_allowed = sorted(allowed - used)
    event_coverage = []
    uncovered = []
    for permission in manifest["proof_permissions"]:
        candidates = set(permission["candidates"])
        witnesses = sorted(used & candidates)
        record = {
            "step": permission["step"],
            "event": permission["event"],
            "printed": permission["printed"],
            "used_candidates": witnesses,
            "covered": bool(witnesses),
        }
        event_coverage.append(record)
        if not witnesses:
            uncovered.append(record)

    if extra:
        classification = "relaxed-closure"
    elif uncovered:
        classification = "strict-subset-with-unused-printed-citations"
    else:
        classification = "strict-closure"
    return {
        "kind": "pm-constrained-reconstruction-audit",
        "current_item": manifest.get("current_item"),
        "classification": classification,
        "faithful_by_printed_dependency_constraint": classification == "strict-closure",
        "used_pm_items": sorted(used),
        "added_beyond_print": extra,
        "allowed_but_unused": unused_allowed,
        "global_conventions": list(manifest.get("global_conventions", [])),
        "printed_event_coverage": event_coverage,
        "uncovered_printed_events": uncovered,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("used_items", type=Path,
                        help="JSON array of PM item IDs extracted from the Lean term")
    options = parser.parse_args()
    manifest = json.loads(options.manifest.read_text(encoding="utf-8"))
    used = json.loads(options.used_items.read_text(encoding="utf-8"))
    if not isinstance(used, list) or any(not isinstance(item, str) for item in used):
        raise ReconstructionAuditError("used-items file must contain a JSON string array")
    print(json.dumps(classify_reconstruction(manifest, used),
                     ensure_ascii=False, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
