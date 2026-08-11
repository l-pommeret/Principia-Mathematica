#!/usr/bin/env python3
"""Build a minimal, provenance-hashed Lean context from a PM manifest.

The elementary profile contains the complete trusted syntax/deduction kernel
(`Formula.lean` and `System.lean`) with comments/imports removed, followed by
only the reviewed item declarations in the manifest's implementation closure.
It is intended for an isolated Aristotle sandbox, not for import into the main
edition where those declarations already exist.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

from pm_constraint_manifest import load_item_registry
from verify_dependencies import declaration_body, pm_order, strip_lean_comments


ROOT = Path(__file__).resolve().parents[1]
FOUNDATION_PROFILES = {
    "elementary-pm1": (
        "Principia/Syntax/Formula.lean",
        "Principia/Deduction/System.lean",
    ),
    "elementary-formation-pm1": (
        "Principia/Syntax/Formula.lean",
        "Principia/Deduction/System.lean",
        "Principia/Deduction/Formation.lean",
        "Principia/Deduction/Formed.lean",
    ),
}


class BundleError(ValueError):
    pass


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def preserve_historical_container_hashes(recorded: dict, rebuilt: dict) -> None:
    """Ignore append-only container drift when exact declaration slices agree."""
    for old, new in zip(recorded.get("sources", []), rebuilt.get("sources", []),
                        strict=True):
        if (old.get("kind") == new.get("kind") == "item-declaration"
                and old.get("slice_sha256") == new.get("slice_sha256")):
            new["source_sha256"] = old.get("source_sha256")


def clean_foundation(source: str, *, strip_trailing_whitespace: bool = False) -> str:
    clean = strip_lean_comments(source)
    clean = re.sub(r"(?m)^import\s+[^\n]+\n", "", clean)
    if strip_trailing_whitespace:
        # Removing an indented doc comment can leave its indentation behind on
        # an otherwise blank line.  A manifest may opt into this canonical
        # representation without rewriting historical context bundles.
        clean = "\n".join(line.rstrip() for line in clean.splitlines())
    return re.sub(r"\n{3,}", "\n\n", clean).strip() + "\n"


def declaration_namespace(qualified: str) -> str:
    if "." not in qualified:
        raise BundleError(f"unqualified Lean declaration {qualified}")
    return qualified.rsplit(".", 1)[0]


def clean_declaration(item: dict, root: Path) -> str:
    body = declaration_body(root / item["lean_path"], item["declaration"])
    return re.sub(r"\n{3,}", "\n\n", strip_lean_comments(body)).strip()


def build_bundle(manifest: dict, registry: dict[str, dict], root: Path = ROOT) -> dict:
    if manifest.get("kind") not in {
        "pm-constrained-prover-manifest", "pm-constrained-prover-batch-manifest"
    }:
        raise BundleError("not a PM constrained-prover manifest")
    closure = list(manifest.get("context_closure", []))
    unknown = sorted(set(closure) - registry.keys())
    if unknown:
        raise BundleError(f"unknown context items {unknown}")

    chunks: list[str] = []
    sources: list[dict] = []
    profile = manifest.get("foundation_profile", "elementary-pm1")
    if profile not in FOUNDATION_PROFILES:
        raise BundleError(f"unknown foundation profile {profile}")
    foundation = FOUNDATION_PROFILES[profile]
    whitespace_policy = manifest.get("context_whitespace_policy", "preserve")
    if whitespace_policy not in {"preserve", "strip-trailing"}:
        raise BundleError(f"unknown context whitespace policy {whitespace_policy!r}")
    foundation_paths = set(foundation)
    for relative in foundation:
        path = root / relative
        raw = path.read_text(encoding="utf-8")
        clean = clean_foundation(
            raw, strip_trailing_whitespace=whitespace_policy == "strip-trailing"
        )
        chunks.append(f"-- PM-CONTEXT-FOUNDATION {relative}\n{clean}")
        sources.append({
            "kind": "foundation",
            "path": relative,
            "source_sha256": sha256_text(raw),
            "slice_sha256": sha256_text(clean),
            "bytes": len(clean.encode("utf-8")),
        })

    # Constructors and `detach` live inside the complete System foundation;
    # ✱1·01 lives inside Formula. Do not duplicate those declarations.
    sliced = [registry[identifier] for identifier in closure
              if registry[identifier]["lean_path"] not in foundation_paths]
    sliced.sort(key=lambda item: pm_order(item["id"]))
    for item in sliced:
        clean = clean_declaration(item, root)
        namespace = declaration_namespace(item["declaration"])
        wrapped = f"namespace {namespace}\n\n{clean}\n\nend {namespace}\n"
        chunks.append(
            f"-- PM-CONTEXT-ITEM {item['id']} {item['declaration']}\n{wrapped}"
        )
        sources.append({
            "kind": "item-declaration",
            "id": item["id"],
            "path": item["lean_path"],
            "declaration": item["declaration"],
            "source_sha256": sha256_text(
                (root / item["lean_path"]).read_text(encoding="utf-8")
            ),
            "slice_sha256": sha256_text(clean),
            "bytes": len(clean.encode("utf-8")),
        })

    source = "\n".join(chunks).rstrip() + "\n"
    canonical_manifest = json.dumps(
        manifest, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    )
    result = {
        "kind": "pm-isolated-context-bundle",
        "profile": profile,
        "current_item": manifest.get("current_item"),
        "manifest_sha256": sha256_text(canonical_manifest),
        "source_sha256": sha256_text(source),
        "source_bytes": len(source.encode("utf-8")),
        "proof_permissions": list(
            manifest.get("allowed_pm_items", manifest.get("proof_permissions", []))
        ),
        "context_closure": closure,
        "sources": sources,
        "lean_source": source,
        "policy": {
            "standalone_context_only": True,
            "grants_no_additional_proof_permission": True,
            "requires_remote_kernel_check": True,
        },
    }
    if "target_order" in manifest:
        result["target_order"] = list(manifest["target_order"])
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--metadata-dir", type=Path, default=Path("metadata/items"))
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--source-output", type=Path)
    parser.add_argument("--metadata-output", type=Path)
    options = parser.parse_args()
    manifest = json.loads(options.manifest.read_text(encoding="utf-8"))
    registry = load_item_registry(options.metadata_dir)
    bundle = build_bundle(manifest, registry, options.root)
    if options.source_output:
        options.source_output.write_text(bundle.pop("lean_source"), encoding="utf-8")
    rendered = json.dumps(bundle, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if options.metadata_output:
        options.metadata_output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
