#!/usr/bin/env python3
"""Verify generated isolated Aristotle contexts against current sources."""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys

from pm_constraint_manifest import load_item_registry
from pm_context_bundle import ROOT, build_bundle


class ContextBundleVerificationError(ValueError):
    pass


def verify(root: Path = ROOT) -> int:
    metadata_dir = root / "metadata/context_bundles"
    registry = load_item_registry(root / "metadata/items")
    checked = 0
    for metadata_path in sorted(metadata_dir.glob("*.json")):
        stem = metadata_path.stem
        manifest_path = root / "aristotle/manifests" / f"{stem}.json"
        source_path = root / "aristotle/contexts" / f"{stem}.lean"
        if not manifest_path.is_file() or not source_path.is_file():
            raise ContextBundleVerificationError(f"missing manifest/source for {stem}")
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        expected = build_bundle(manifest, registry, root)
        actual_metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        actual_source = source_path.read_text(encoding="utf-8")
        forbidden = re.search(
            r"(?m)(?:\bsorry\b|\badmit\b|^\s*axiom\b|^\s*unsafe\b|\bClassical\b)",
            actual_source,
        )
        if forbidden:
            raise ContextBundleVerificationError(
                f"forbidden construct {forbidden.group(0)!r} in {stem}"
            )
        expected_source = expected.pop("lean_source")
        if actual_source != expected_source:
            raise ContextBundleVerificationError(f"generated Lean context drift for {stem}")
        if actual_metadata != expected:
            raise ContextBundleVerificationError(f"context metadata drift for {stem}")
        if not actual_metadata["policy"]["grants_no_additional_proof_permission"]:
            raise ContextBundleVerificationError(f"unsafe permission policy for {stem}")
        checked += 1
    if checked == 0:
        raise ContextBundleVerificationError("no isolated context bundles found")
    return checked


def main() -> None:
    try:
        checked = verify()
    except (ContextBundleVerificationError, ValueError, OSError, json.JSONDecodeError) as error:
        print(f"context bundle error: {error}", file=sys.stderr)
        raise SystemExit(1)
    print(f"isolated context bundle checks passed ({checked} bundle(s))")


if __name__ == "__main__":
    main()
