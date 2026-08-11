#!/usr/bin/env python3
"""Audit provisional prompt-derived Aristotle interfaces.

These are intentionally weaker than reconstructed PM batches.  The verifier
ensures they stay linked to their reviewed prompt and scan evidence, and that
their explicit promotion block cannot silently disappear.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

from generate_statement_only_interfaces import FENCE, ROOT, SCAN, sha256_text
from pm_constraint_manifest import load_item_registry
from pm_proof_skeleton import parse_demonstration
from verify_editorial import collect_verbatim


def demonstration_path(item_id: str) -> Path:
    """Locate the diplomatic transcript from the canonical PM item identity."""
    match = re.fullmatch(r"PM(\d+):✱(\d+)·(\d+)", item_id)
    if match is None:
        raise ValueError(f"invalid PM item identity: {item_id}")
    volume, star, suffix = match.groups()
    return ROOT / "aristotle" / "demonstrations" / f"PM{volume}-star-{star}-{suffix}.txt"


def verify() -> int:
    pipeline = json.loads((ROOT / "pipeline.json").read_text(encoding="utf-8"))
    registry = load_item_registry(ROOT / "metadata" / "items")
    verbatim = collect_verbatim()
    checked = 0
    for path in sorted((ROOT / "metadata/interface_bundles").glob("Q*.json")):
        bundle = json.loads(path.read_text(encoding="utf-8"))
        batch = bundle["batch"]
        manifest_path = ROOT / bundle["manifest_path"]
        context_path = ROOT / bundle["context_path"]
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        question = pipeline["questions"][batch]
        prompt = (ROOT / question["prompt_path"]).read_text(encoding="utf-8")
        review = (ROOT / question["audit_path"]).read_text(encoding="utf-8")
        if (manifest.get("kind") != "pm-statement-only-interface-manifest" or
                not isinstance(manifest.get("source_backfill_required"), bool) or
                manifest.get("integration_blocked") is not True):
            raise ValueError(f"{batch}: missing statement-only promotion block")
        if manifest.get("audit_status") != "A-interface-only":
            raise ValueError(f"{batch}: missing interface audit classification")
        if manifest.get("canonical_ids") != question["canonical_ids"]:
            raise ValueError(f"{batch}: canonical ID drift")
        if manifest.get("exact_lean_targets") != FENCE.findall(prompt):
            raise ValueError(f"{batch}: Lean target drift")
        if manifest.get("opaque_dependency_stubs") != question.get("depends_on", []):
            raise ValueError(f"{batch}: stub map drift")
        if manifest.get("scan_hashes") != sorted(set(SCAN.findall(prompt + "\n" + review))):
            raise ValueError(f"{batch}: scan hash drift")
        if manifest.get("prompt_sha256") != sha256_text(prompt) or manifest.get("review_sha256") != sha256_text(review):
            raise ValueError(f"{batch}: prompt/review link drift")
        if manifest.get("exact_lean_target_sha256") != [sha256_text(t) for t in FENCE.findall(prompt)]:
            raise ValueError(f"{batch}: target hash drift")
        expected_context = (
            "/- Non-repository opaque interface. Do not promote or import into the repository.\n"
            "   Exact target declarations are in the paired manifest/prompt; dependencies below are stubs only. -/\n\n"
            + "\n".join(f"-- OPAQUE-PM-DEPENDENCY {item}" for item in question.get("depends_on", []))
            + "\n"
        )
        if context_path.read_text(encoding="utf-8") != expected_context:
            raise ValueError(f"{batch}: context link drift")
        if bundle.get("source_backfill_required") != manifest["source_backfill_required"] or bundle.get("integration_blocked") is not True:
            raise ValueError(f"{batch}: bundle promotion block missing")
        if not manifest["source_backfill_required"]:
            # Earlier source backfills predate the structured audit field.
            # Keep them readable while enforcing the stronger contract for
            # every newly promoted record which carries that field.
            if not manifest.get("canonical_backfill_audit"):
                checked += 1
                continue
            for item_id in manifest["canonical_ids"]:
                item = registry.get(item_id)
                if item is None or item.get("formal_status") != "prepared":
                    raise ValueError(f"{batch}: {item_id} lacks prepared canonical metadata")
                if item_id not in verbatim:
                    raise ValueError(f"{batch}: {item_id} lacks PM-VERBATIM")
                demo = demonstration_path(item_id)
                if not demo.is_file():
                    raise ValueError(f"{batch}: {item_id} lacks demonstration transcript")
                parse_demonstration(demo.read_text(encoding="utf-8"), 1, item_id)
        checked += 1
    return checked


if __name__ == "__main__":
    try:
        print(f"statement-only interface checks passed ({verify()} bundle(s))")
    except (KeyError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"statement-only interface error: {error}", file=sys.stderr)
        raise SystemExit(1)
