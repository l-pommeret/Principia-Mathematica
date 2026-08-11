#!/usr/bin/env python3
"""Generate non-repository Aristotle interfaces from audited statement prompts.

These artifacts are deliberately not constrained PM reconstructions: they retain
the exact Lean target blocks and citation comments already reviewed in a prompt,
while every dependency is an opaque external interface.  They must never be
used for a repository promotion before a PM-VERBATIM demonstration backfill.
"""

from __future__ import annotations

import json
import hashlib
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FENCE = re.compile(r"```lean\n(.*?)```", re.S)
SCAN = re.compile(r"\b[0-9a-f]{64}\b")


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def generate(batch: str) -> None:
    pipeline = json.loads((ROOT / "pipeline.json").read_text(encoding="utf-8"))
    question = pipeline["questions"][batch]
    prompt_path = ROOT / question["prompt_path"]
    review_path = ROOT / question["audit_path"]
    prompt = prompt_path.read_text(encoding="utf-8")
    review = review_path.read_text(encoding="utf-8")
    targets = FENCE.findall(prompt)
    if not targets:
        raise ValueError(f"{batch}: prompt has no exact Lean target block")
    citations = re.findall(r"--\s*\[([^\]]+)\]", "\n".join(targets))
    scan_hashes = SCAN.findall(prompt + "\n" + review)
    payload = {
        "kind": "pm-statement-only-interface-manifest",
        "batch": batch,
        "source_backfill_required": True,
        "integration_blocked": True,
        "audit_status": "A-interface-only",
        "audit_basis": "reviewed exact prompt targets, citations, and scan hashes; no PM-VERBATIM proof skeleton",
        "promotion_prohibited": "PM-VERBATIM plus parsed demonstration audit required",
        "canonical_ids": question["canonical_ids"],
        "prompt_path": question["prompt_path"],
        "review_path": question["audit_path"],
        "scan_hashes": sorted(set(scan_hashes)),
        "opaque_dependency_stubs": question.get("depends_on", []),
        "citation_comments": citations,
        "exact_lean_targets": targets,
        "prompt_sha256": sha256_text(prompt),
        "review_sha256": sha256_text(review),
        "exact_lean_target_sha256": [sha256_text(target) for target in targets],
    }
    manifest_dir = ROOT / "aristotle/manifests"
    context_dir = ROOT / "aristotle/contexts"
    bundle_dir = ROOT / "metadata/interface_bundles"
    bundle_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = manifest_dir / f"{batch}-interface.json"
    context_path = context_dir / f"{batch}-interface.lean"
    manifest_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    context_path.write_text(
        "/- Non-repository opaque interface. Do not promote or import into the repository.\n"
        "   Exact target declarations are in the paired manifest/prompt; dependencies below are stubs only. -/\n\n"
        + "\n".join(f"-- OPAQUE-PM-DEPENDENCY {item}" for item in payload["opaque_dependency_stubs"])
        + "\n",
        encoding="utf-8",
    )
    (bundle_dir / f"{batch}.json").write_text(json.dumps({
        "kind": "pm-statement-only-interface-bundle",
        "batch": batch,
        "manifest_path": str(manifest_path.relative_to(ROOT)),
        "context_path": str(context_path.relative_to(ROOT)),
        "source_backfill_required": True,
        "integration_blocked": True,
        "opaque_dependency_stubs": payload["opaque_dependency_stubs"],
        "manifest_sha256": sha256_text(
            json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        ),
    }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    for name in sys.argv[1:]:
        generate(name)
