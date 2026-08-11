#!/usr/bin/env python3
"""Generate a reviewed constrained batch's manifest, context, metadata and prompt."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from pm_aristotle_prompt import render_batch_prompt
from pm_constraint_manifest import compile_batch_manifest, load_item_registry
from pm_context_bundle import ROOT, build_bundle
from pm_proof_skeleton import apply_reference_overrides, parse_demonstration


def generate(batch: str, root: Path = ROOT) -> None:
    spec_path = root / "metadata/constrained_batches" / f"{batch}.json"
    spec = json.loads(spec_path.read_text(encoding="utf-8"))
    if spec.get("generation_status", "ready") != "ready":
        raise ValueError(f"{batch} is not ready for generation")
    registry = load_item_registry(root / "metadata/items")
    skeletons = []
    targets: dict[str, str] = {}
    printed: dict[str, str] = {}
    lean: dict[str, str] = {}
    conventions: dict[str, list[str]] = {}
    for entry in spec["items"]:
        identifier = entry["id"]
        source = (root / entry["demonstration_path"]).read_text(encoding="utf-8")
        skeleton = parse_demonstration(source, spec.get("volume", 1), identifier)
        skeletons.append(apply_reference_overrides(
            skeleton, entry.get("reference_overrides", [])
        ))
        targets[identifier] = entry["declaration"]
        printed[identifier] = source
        lean[identifier] = entry["lean_target"]
        conventions[identifier] = entry.get("global_conventions", [])
    manifest = compile_batch_manifest(
        skeletons, registry, targets, global_conventions=conventions
    )
    if "foundation_profile" in spec:
        manifest["foundation_profile"] = spec["foundation_profile"]
    manifest_path = root / "aristotle/manifests" / f"{batch}.json"
    manifest_path.write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    bundle = build_bundle(manifest, registry, root)
    source = bundle.pop("lean_source")
    (root / "aristotle/contexts" / f"{batch}.lean").write_text(source, encoding="utf-8")
    bundle["ci_evidence"] = {"commit": "pending", "run": "pending", "conclusion": "pending"}
    (root / "metadata/context_bundles" / f"{batch}.json").write_text(
        json.dumps(bundle, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    prompt = render_batch_prompt(
        manifest, printed_targets=printed, lean_targets=lean, context=source
    )
    (root / spec["prompt_path"]).write_text(prompt, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("batch")
    options = parser.parse_args()
    generate(options.batch)


if __name__ == "__main__":
    main()
