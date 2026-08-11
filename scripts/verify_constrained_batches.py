#!/usr/bin/env python3
"""Reproduce ordered constrained-prover batches from their reviewed specs."""

from __future__ import annotations

import json
from pathlib import Path
import sys

from pm_aristotle_prompt import render_batch_prompt
from pm_constraint_manifest import compile_batch_manifest, load_item_registry
from pm_context_bundle import ROOT, build_bundle, preserve_historical_container_hashes
from pm_lean_target import render_elementary_assertion
from pm_proof_skeleton import apply_reference_overrides, parse_demonstration


class BatchVerificationError(ValueError):
    pass


def verify(root: Path = ROOT) -> int:
    registry = load_item_registry(root / "metadata/items")
    checked = 0
    for spec_path in sorted((root / "metadata/constrained_batches").glob("*.json")):
        spec = json.loads(spec_path.read_text(encoding="utf-8"))
        if spec.get("kind") != "pm-constrained-batch-spec":
            raise BatchVerificationError(f"invalid batch spec {spec_path}")
        generation_status = spec.get("generation_status", "ready")
        if generation_status != "ready":
            if not isinstance(generation_status, str) or not generation_status.startswith("blocked-on-"):
                raise BatchVerificationError(f"invalid generation status in {spec_path}")
            continue
        stem = spec_path.stem
        skeletons = []
        targets = {}
        printed = {}
        lean = {}
        conventions = {}
        for entry in spec["items"]:
            identifier = entry["id"]
            source = (root / entry["demonstration_path"]).read_text(encoding="utf-8")
            skeleton = parse_demonstration(source, spec.get("volume", 1), identifier)
            skeletons.append(apply_reference_overrides(
                skeleton, entry.get("reference_overrides", [])
            ))
            targets[identifier] = entry["declaration"]
            printed[identifier] = source
            if entry.get("lean_target_profile") == "elementary-assertion":
                lean[identifier] = render_elementary_assertion(source, entry["declaration"])
            else:
                lean[identifier] = entry["lean_target"]
            conventions[identifier] = entry.get("global_conventions", [])
        manifest = compile_batch_manifest(
            skeletons, registry, targets, global_conventions=conventions
        )
        if "foundation_profile" in spec:
            manifest["foundation_profile"] = spec["foundation_profile"]
        manifest_path = root / "aristotle/manifests" / f"{stem}.json"
        actual_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if actual_manifest != manifest:
            raise BatchVerificationError(f"manifest drift for {stem}")
        bundle = build_bundle(manifest, registry, root)
        source = bundle.pop("lean_source")
        context_path = root / "aristotle/contexts" / f"{stem}.lean"
        if context_path.read_text(encoding="utf-8") != source:
            raise BatchVerificationError(f"context drift for {stem}")
        metadata_path = root / "metadata/context_bundles" / f"{stem}.json"
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        metadata.pop("ci_evidence", None)
        # A context bundle embeds declaration slices, not the whole container
        # file. Later propositions may therefore change `source_sha256` while
        # every included byte and `slice_sha256` remains identical. Preserve
        # the historical whole-file digest as provenance, but do not treat
        # such an append-only container change as context drift.
        preserve_historical_container_hashes(metadata, bundle)
        if metadata != bundle:
            raise BatchVerificationError(f"context metadata drift for {stem}")
        prompt = render_batch_prompt(
            manifest, printed_targets=printed, lean_targets=lean, context=source
        )
        if (root / spec["prompt_path"]).read_text(encoding="utf-8") != prompt:
            raise BatchVerificationError(f"prompt drift for {stem}")
        checked += 1
    if checked == 0:
        raise BatchVerificationError("no constrained batch specs found")
    return checked


def main() -> None:
    try:
        checked = verify()
    except (BatchVerificationError, ValueError, OSError, json.JSONDecodeError) as error:
        print(f"constrained batch error: {error}", file=sys.stderr)
        raise SystemExit(1)
    print(f"constrained batch checks passed ({checked} batch(es))")


if __name__ == "__main__":
    main()
