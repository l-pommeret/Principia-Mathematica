#!/usr/bin/env python3
"""Lift only the source-backfill gate for audited PM statement interfaces.

This does not promote a proof or clear the integration block.  It records that
the prompt-derived task now has a matching PM-VERBATIM block, item metadata,
and parsable diplomatic citation skeleton.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

from pm_constraint_manifest import load_item_registry
from pm_proof_skeleton import parse_demonstration
from verify_editorial import collect_verbatim

ROOT = Path(__file__).resolve().parents[1]


def canonical_json(value: dict) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def promote(batch: str) -> None:
    manifest_path = ROOT / "aristotle" / "manifests" / f"{batch}-interface.json"
    bundle_path = ROOT / "metadata" / "interface_bundles" / f"{batch}.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    bundle = json.loads(bundle_path.read_text(encoding="utf-8"))
    registry = load_item_registry(ROOT / "metadata" / "items")
    blocks = collect_verbatim()
    for item_id in manifest["canonical_ids"]:
        if item_id not in registry or registry[item_id].get("formal_status") != "prepared":
            raise ValueError(f"{batch}: no prepared metadata for {item_id}")
        if item_id not in blocks:
            raise ValueError(f"{batch}: no PM-VERBATIM block for {item_id}")
        suffix = item_id.rsplit("·", 1)[1]
        demo = ROOT / "aristotle" / "demonstrations" / f"PM1-star-5-{suffix}.txt"
        if not demo.is_file():
            raise ValueError(f"{batch}: no demonstration transcript for {item_id}")
        parse_demonstration(demo.read_text(encoding="utf-8"), 1, item_id)
    manifest["source_backfill_required"] = False
    manifest["audit_basis"] = (
        "canonical PM-VERBATIM backfill on scan leaves 152–153; "
        "diplomatic citation skeletons parsed per target"
    )
    manifest["canonical_backfill_audit"] = {
        "verbatim": True,
        "item_metadata": True,
        "parsed_demonstrations": True,
        "integration_still_blocked": True,
    }
    manifest["promotion_prohibited"] = "formal dependency/remote-kernel audit still required"
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    bundle["source_backfill_required"] = False
    bundle["manifest_sha256"] = hashlib.sha256(canonical_json(manifest).encode("utf-8")).hexdigest()
    bundle_path.write_text(json.dumps(bundle, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    for name in sys.argv[1:]:
        promote(name)
