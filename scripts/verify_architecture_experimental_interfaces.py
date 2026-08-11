#!/usr/bin/env python3
"""Verify that experimental architecture interfaces remain non-canonical."""

from __future__ import annotations

import json
import sys

from generate_architecture_experimental_interfaces import ROOT, canonical_json, generate, sha256_text


def verify() -> int:
    checked = 0
    # Regenerate from the reviewed sources, compare byte-for-byte, then restore
    # nothing: generation is deterministic and only addresses these artifacts.
    for bundle_path in sorted((ROOT / "metadata" / "architecture_interface_bundles").glob("Q*.json")):
        before = {
            path: path.read_text(encoding="utf-8")
            for path in (
                bundle_path,
                ROOT / "aristotle" / "manifests" / f"{bundle_path.stem}-architecture-interface.json",
                ROOT / "aristotle" / "contexts" / f"{bundle_path.stem}-architecture-interface.lean",
            )
        }
        generate(bundle_path.stem)
        for path, expected in before.items():
            if path.read_text(encoding="utf-8") != expected:
                raise ValueError(f"{bundle_path.stem}: generated interface drift")
        bundle = json.loads(before[bundle_path])
        manifest = json.loads(before[ROOT / "aristotle" / "manifests" / f"{bundle_path.stem}-architecture-interface.json"])
        if not (bundle.get("architecture_experimental") is True and
                bundle.get("canonical_source_claim") is False and
                bundle.get("canonical_integration_forbidden") is True and
                bundle.get("integration_blocked") is True):
            raise ValueError(f"{bundle_path.stem}: canonical-promotion block missing")
        if manifest.get("audit_status") != "A-architecture-experimental":
            raise ValueError(f"{bundle_path.stem}: experimental audit classification missing")
        if bundle.get("manifest_sha256") != sha256_text(canonical_json(manifest)):
            raise ValueError(f"{bundle_path.stem}: manifest hash drift")
        checked += 1
    return checked


if __name__ == "__main__":
    try:
        print(f"architecture experimental checks passed ({verify()} bundle(s))")
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"architecture experimental error: {error}", file=sys.stderr)
        raise SystemExit(1)
