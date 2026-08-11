#!/usr/bin/env python3
"""Generate non-canonical interfaces for exact architecture experiments.

These artifacts retain every reviewed Lean fence byte-for-byte, but deliberately
do not claim a PM reconstruction or a repository-integration result.  Each
dependency is an opaque declaration whose signature is sliced from the current
item metadata/source; its body is never copied into the experiment.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

from pm_constraint_manifest import load_item_registry
from pm_context_bundle import clean_foundation, declaration_namespace, interface_stub


ROOT = Path(__file__).resolve().parents[1]
FENCE = re.compile(r"```lean\n(.*?)```", re.S)
SCAN = re.compile(r"\b[0-9a-f]{64}\b")

# Q253/254 contain declaration slices whose opaque signatures use the ✱9
# syntax foundation. Isolated contexts are compiled before repository modules,
# so imports would look for unavailable `.olean` files; embed these exact
# foundation sources instead. Q252 declares the same foundation itself.
FOUNDATION_SOURCES = {
    "Q253": ("Principia/Syntax/Formula.lean", "Principia/Syntax/Apparent.lean"),
    "Q254": ("Principia/Syntax/Formula.lean", "Principia/Syntax/Apparent.lean"),
}


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def canonical_json(value: dict) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def dependency_stubs(question: dict, registry: dict[str, dict]) -> list[dict]:
    stubs = []
    for identifier in question.get("depends_on", []):
        item = registry.get(identifier)
        if item is None:
            raise ValueError(f"missing item metadata for architecture stub {identifier}")
        opaque, signature = interface_stub(item, ROOT)
        stubs.append({
            "id": identifier,
            "declaration": item["declaration"],
            "metadata_path": str(Path(item["_metadata_path"]).relative_to(ROOT)),
            "signature": signature,
            "signature_sha256": sha256_text(signature),
            "opaque_declaration": opaque,
            "opaque_declaration_sha256": sha256_text(opaque),
        })
    return stubs


def foundation_sources(paths: tuple[str, ...]) -> tuple[list[str], list[dict]]:
    chunks: list[str] = []
    provenance: list[dict] = []
    for relative in paths:
        path = ROOT / relative
        raw = path.read_text(encoding="utf-8")
        clean = clean_foundation(raw)
        chunks.append(f"-- PM-CONTEXT-FOUNDATION {relative}\n{clean}")
        provenance.append({
            "path": relative,
            "source_sha256": sha256_text(raw),
            "slice_sha256": sha256_text(clean),
        })
    return chunks, provenance


def render_context(stubs: list[dict], foundations: list[str]) -> str:
    chunks = [
        "/- Architecture-experimental opaque interface. This file is not a repository import,",
        "   does not establish canonical PM coverage, and cannot be promoted. -/",
        "",
    ]
    chunks.extend(foundations)
    if foundations:
        chunks.append("")
    for stub in stubs:
        chunks.extend([
            f"-- OPAQUE-PM-DEPENDENCY {stub['id']} {stub['signature_sha256']}",
            f"namespace {declaration_namespace(stub['declaration'])}",
            "",
            stub["opaque_declaration"].rstrip(),
            "",
            f"end {declaration_namespace(stub['declaration'])}",
            "",
        ])
    return "\n".join(chunks).rstrip() + "\n"


def generate(batch: str) -> None:
    pipeline = json.loads((ROOT / "pipeline.json").read_text(encoding="utf-8"))
    question = pipeline["questions"][batch]
    prompt = (ROOT / question["prompt_path"]).read_text(encoding="utf-8")
    review = (ROOT / question["audit_path"]).read_text(encoding="utf-8")
    targets = FENCE.findall(prompt)
    if not targets:
        raise ValueError(f"{batch}: no exact Lean target block; architecture task stays blocked")
    if question.get("audit_status") != "A":
        raise ValueError(f"{batch}: audit is not A; architecture task stays blocked")
    stubs = dependency_stubs(question, load_item_registry(ROOT / "metadata" / "items"))
    foundation_paths = FOUNDATION_SOURCES.get(batch, ())
    foundations, foundation_provenance = foundation_sources(foundation_paths)
    payload = {
        "kind": "pm-architecture-experimental-interface-manifest",
        "batch": batch,
        "architecture_experimental": True,
        "canonical_source_claim": False,
        "canonical_integration_forbidden": True,
        "requires_one_to_one_kernel_remap": True,
        "integration_blocked": True,
        "audit_status": "A-architecture-experimental",
        "audit_basis": "reviewed exact Lean target blocks and source hashes; isolated architecture experiment only",
        "promotion_prohibited": "not canonical; requires separate canonical source/dependency audit",
        "canonical_ids": question["canonical_ids"],
        "prompt_path": question["prompt_path"],
        "review_path": question["audit_path"],
        # The prompt, unlike an audit review, contains only the cited scan
        # witnesses (reviews also record archive and source-file hashes).
        "scan_hashes": sorted(set(SCAN.findall(prompt))),
        "exact_lean_targets": targets,
        "exact_lean_target_sha256": [sha256_text(target) for target in targets],
        "prompt_sha256": sha256_text(prompt),
        "review_sha256": sha256_text(review),
        "opaque_dependency_stubs": stubs,
        **({"foundation_sources": foundation_provenance} if foundation_provenance else {}),
    }
    context = render_context(stubs, foundations)
    manifest_path = ROOT / "aristotle" / "manifests" / f"{batch}-architecture-interface.json"
    context_path = ROOT / "aristotle" / "contexts" / f"{batch}-architecture-interface.lean"
    bundle_path = ROOT / "metadata" / "architecture_interface_bundles" / f"{batch}.json"
    bundle_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    context_path.write_text(context, encoding="utf-8")
    bundle_path.write_text(json.dumps({
        "kind": "pm-architecture-experimental-interface-bundle",
        "batch": batch,
        "manifest_path": str(manifest_path.relative_to(ROOT)),
        "context_path": str(context_path.relative_to(ROOT)),
        "architecture_experimental": True,
        "canonical_source_claim": False,
        "canonical_integration_forbidden": True,
        "integration_blocked": True,
        "opaque_dependency_stubs": [stub["id"] for stub in stubs],
        "manifest_sha256": sha256_text(canonical_json(payload)),
    }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    for name in sys.argv[1:]:
        generate(name)
