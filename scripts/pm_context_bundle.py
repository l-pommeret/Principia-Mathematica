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
from pm_lean_target import LeanTargetError, render_elementary_assertion
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
    "ordered-first-order-pm1": (
        "Principia/Syntax/Formula.lean",
        "Principia/Syntax/Apparent.lean",
        "Principia/Syntax/Ordered.lean",
        "Principia/Deduction/System.lean",
        "Principia/Deduction/Ordered.lean",
    ),
    "description-scope-pm1": (
        "Principia/Syntax/Description.lean",
    ),
    "description-definitions-pm1": (
        "Principia/Syntax/Description.lean",
        "Principia/Syntax/DescriptionDefinitions.lean",
    ),
}


class BundleError(ValueError):
    pass


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def preserve_historical_container_hashes(recorded: dict, rebuilt: dict) -> None:
    """Ignore append-only container drift when exact declaration slices agree."""
    def source_key(source: dict) -> tuple[str | None, str | None, str | None]:
        return (source.get("kind"), source.get("id"), source.get("path"))

    # A reviewed relaxation may add a declaration to a bundle.  Such an
    # expansion is not historical container drift, so retain provenance only
    # for source slices which occur in both versions.
    previous = {source_key(source): source for source in recorded.get("sources", [])}
    for new in rebuilt.get("sources", []):
        old = previous.get(source_key(new))
        if old is None:
            continue
        if (old.get("kind") == new.get("kind")
                and new.get("kind") in {"item-declaration", "opaque-interface-stub"}
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


def interface_stub(item: dict, root: Path) -> tuple[str, str]:
    """Return a signature-only interface axiom for a non-kernel item.

    This deliberately derives the type binder/header from the declared Lean
    source and emits no reconstructed proof body.  Lean's bodyless `opaque`
    declarations require a `Nonempty` target, which proof and syntax targets
    intentionally lack.  The generated context therefore uses an `axiom`;
    it is permitted only in a manifest-recorded, integration-blocked context
    and is rejected from canonical Lean sources.
    """
    try:
        body = clean_declaration(item, root)
    except ValueError:
        # Prepared items often have an audited demonstration but deliberately
        # no Lean body in the edition yet.  For elementary assertions the
        # audited PM AST is the authoritative source of the exact signature.
        match = re.fullmatch(r"PM(\d+):✱(\d+)·(\d+)", item["id"])
        if match is None:
            raise BundleError(f"no declaration or elementary AST route for {item['id']}")
        volume, section, number = match.groups()
        # First prefer a previously audited exact Lean target.  This is needed
        # for object-language abbreviations such as ✱4 equivalence, which are
        # not reducible to the elementary AST renderer.
        rendered = None
        for manifest_path in sorted((root / "aristotle" / "manifests").glob("*.json")):
            payload = json.loads(manifest_path.read_text(encoding="utf-8"))
            candidate = payload.get("interface_signature_targets", {}).get(item["id"])
            if isinstance(candidate, str):
                rendered = candidate
                break
        demo = root / "aristotle" / "demonstrations" / (
            f"PM{volume}-star-{section}-{number}.txt"
        )
        if rendered is None and not demo.is_file():
            raise BundleError(f"no audited AST or Lean target for {item['id']}")
        try:
            if rendered is None:
                rendered = render_elementary_assertion(
                    demo.read_text(encoding="utf-8"), item["declaration"]
                )
            lines = rendered.splitlines()
            if len(lines) < 5 or not lines[0].startswith("namespace ") or not lines[-1].startswith("end "):
                raise BundleError(f"malformed generated AST signature for {item['id']}")
            body = "\n".join(lines[2:-2]).strip()
        except LeanTargetError as error:
            raise BundleError(
                f"no exact interface signature route for {item['id']}: {error}"
            ) from error
    if ":=" not in body:
        raise BundleError(f"cannot derive interface signature for {item['id']}")
    header = body.split(":=", 1)[0].rstrip()
    interface, replacements = re.subn(
        r"(?m)^(\s*)(?:theorem|def|abbrev)\b", r"\1axiom", header, count=1
    )
    if replacements != 1:
        raise BundleError(f"unsupported declaration header for {item['id']}")
    return interface + "\n", header + "\n"


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

    # An assigned-order experiment may need a small, audited architecture
    # adapter which is not yet an edition item.  Keep this separate from both
    # PM declaration slices and opaque interfaces: its whole source is copied
    # into the isolated context with a hash, and it grants no proof
    # permission.  This route is deliberately manifest-explicit so a context
    # cannot acquire an unrecorded local import.
    local_context_paths = manifest.get("local_context_paths", [])
    if (not isinstance(local_context_paths, list) or
            not all(isinstance(relative, str) for relative in local_context_paths)):
        raise BundleError("local_context_paths must be a list of relative paths")
    if len(local_context_paths) != len(set(local_context_paths)):
        raise BundleError("local_context_paths must be unique")
    interface_gated = bool(manifest.get("policy", {}).get("interface_gated", False))
    source_backfill_required = manifest.get("source_backfill_required", interface_gated)
    if not isinstance(source_backfill_required, bool):
        raise BundleError("source_backfill_required must be boolean when supplied")
    source_backfill_audit = manifest.get("source_backfill_audit")
    if interface_gated and not source_backfill_required:
        if not isinstance(source_backfill_audit, dict):
            raise BundleError(
                "completed source backfill requires an explicit source_backfill_audit"
            )

    # Some local architecture adapters depend on a small kernel-checked
    # declaration slice.  Emit those slices before the local source (rather
    # than after it with the ordinary closure) so the isolated context has the
    # same declaration order as the canonical import graph.
    predeclare_ids = manifest.get("context_predeclarations", [])
    if (not isinstance(predeclare_ids, list) or
            not all(isinstance(identifier, str) for identifier in predeclare_ids) or
            len(predeclare_ids) != len(set(predeclare_ids))):
        raise BundleError("context_predeclarations must be a unique string list")
    if not set(predeclare_ids) <= set(closure):
        raise BundleError("context_predeclarations must belong to context_closure")
    for identifier in sorted(predeclare_ids, key=pm_order):
        item = registry[identifier]
        if item.get("formal_status") != "kernel-checked":
            raise BundleError("context_predeclaration must be kernel-checked: " + identifier)
        clean = clean_declaration(item, root)
        namespace = declaration_namespace(item["declaration"])
        wrapped = f"namespace {namespace}\n\n{clean}\n\nend {namespace}\n"
        chunks.append(
            f"-- PM-CONTEXT-PREDECLARATION {item['id']} {item['declaration']}\n{wrapped}"
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
    if local_context_paths and not interface_gated:
        raise BundleError("local architecture context requires interface-gated policy")
    for relative in local_context_paths:
        local_path = Path(relative)
        if local_path.is_absolute() or ".." in local_path.parts:
            raise BundleError(f"invalid local context path {relative!r}")
        if relative in foundation_paths:
            raise BundleError(f"local context duplicates foundation {relative}")
        path = root / local_path
        if not path.is_file():
            raise BundleError(f"local context path is not a file: {relative}")
        raw = path.read_text(encoding="utf-8")
        clean = clean_foundation(
            raw, strip_trailing_whitespace=whitespace_policy == "strip-trailing"
        )
        chunks.append(f"-- PM-CONTEXT-LOCAL {relative}\n{clean}")
        sources.append({
            "kind": "local-architecture-context",
            "path": relative,
            "source_sha256": sha256_text(raw),
            "slice_sha256": sha256_text(clean),
            "bytes": len(clean.encode("utf-8")),
            "grants_proof_permission": False,
        })

    # Constructors and `detach` live inside the complete System foundation;
    # ✱1·01 lives inside Formula. Do not duplicate those declarations.
    non_kernel = sorted(
        identifier for identifier in closure
        if registry[identifier].get("formal_status") != "kernel-checked"
    )
    if non_kernel and not interface_gated:
        raise BundleError(
            "non-kernel context requires explicit interface-gated policy: "
            + ", ".join(non_kernel)
        )
    syntax = manifest.get("interface_syntax", [])
    if syntax:
        if not interface_gated or not isinstance(syntax, list) or not all(
            isinstance(entry, dict) and set(entry) == {"id", "lean"}
            and isinstance(entry["id"], str) and isinstance(entry["lean"], str)
            for entry in syntax
        ):
            raise BundleError("invalid interface syntax declaration")
        syntax_by_id = {entry["id"]: entry for entry in syntax}
        if len(syntax_by_id) != len(syntax):
            raise BundleError("duplicate interface syntax declaration")
        for identifier in syntax_by_id:
            if identifier not in non_kernel:
                raise BundleError(f"interface syntax must belong to a stub: {identifier}")
    else:
        syntax_by_id = {}

    sliced = [registry[identifier] for identifier in closure
              if (identifier not in predeclare_ids and
                  registry[identifier]["lean_path"] not in foundation_paths)]
    sliced.sort(key=lambda item: pm_order(item["id"]))
    for item in sliced:
        is_interface = item["id"] in non_kernel
        if is_interface:
            clean, signature = interface_stub(item, root)
        else:
            clean = clean_declaration(item, root)
            signature = None
        namespace = declaration_namespace(item["declaration"])
        wrapped = f"namespace {namespace}\n\n{clean}\n\nend {namespace}\n"
        chunks.append(
            f"-- PM-CONTEXT-ITEM {item['id']} {item['declaration']}\n{wrapped}"
        )
        sources.append({
            "kind": "opaque-interface-stub" if is_interface else "item-declaration",
            "id": item["id"],
            "path": item["lean_path"],
            "declaration": item["declaration"],
            "source_sha256": sha256_text(
                (root / item["lean_path"]).read_text(encoding="utf-8")
            ),
            "slice_sha256": sha256_text(clean),
            "bytes": len(clean.encode("utf-8")),
            **({
                "signature_sha256": sha256_text(signature),
                "signature": signature,
                "remap_required": True,
            } if is_interface else {}),
        })
        # Syntax which names an interface declaration must immediately follow
        # that declaration: later interface headers may use the notation.
        entry = syntax_by_id.get(item["id"])
        if entry is not None:
            clean = entry["lean"].strip() + "\n"
            chunks.append(f"-- PM-CONTEXT-INTERFACE-SYNTAX {entry['id']}\n{clean}")
            sources.append({
                "kind": "interface-syntax",
                "id": entry["id"],
                "lean": clean,
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
            "interface_gated": interface_gated,
            "canonical_integration_forbidden": interface_gated,
            "requires_one_to_one_kernel_remap": interface_gated,
        },
        "interface_dependencies": non_kernel,
        "source_backfill_required": source_backfill_required,
        "integration_blocked": interface_gated,
    }
    if source_backfill_audit is not None:
        result["source_backfill_audit"] = source_backfill_audit
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
