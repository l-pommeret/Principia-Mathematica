#!/usr/bin/env python3
"""Compile a PM demonstration skeleton into a strict prover manifest.

The manifest deliberately separates two notions which must never be blurred:

* ``proof_permissions`` are exactly the propositions licensed by the printed
  demonstration (including a historically scoped alias family);
* ``context_closure`` is the transitive implementation context required to
  typecheck those licensed declarations in an isolated prover sandbox.

The latter is not permission to cite an item in the reconstructed proof.  A
constrained prover must enforce ``proof_permissions`` at the proof term level.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from pm_proof_skeleton import parse_demonstration


class ConstraintError(ValueError):
    pass


def load_item_registry(metadata_dir: Path) -> dict[str, dict]:
    registry: dict[str, dict] = {}
    for path in sorted(metadata_dir.glob("*.json")):
        payload = json.loads(path.read_text(encoding="utf-8"))
        for raw in payload.get("items", []):
            item = dict(raw)
            identifier = item.get("id")
            if not isinstance(identifier, str):
                raise ConstraintError(f"item without ID in {path}")
            if identifier in registry:
                raise ConstraintError(f"duplicate PM item {identifier}")
            item["_metadata_path"] = str(path)
            registry[identifier] = item
    return registry


def event_permissions(skeleton: dict) -> list[dict]:
    result: list[dict] = []
    for step_index, step in enumerate(skeleton["steps"], start=1):
        for event_index, event in enumerate(step["events"], start=1):
            if event["kind"] not in {"printed-reference", "printed-alias"}:
                continue
            result.append({
                "step": step_index,
                "event": event_index,
                "printed": event["printed"],
                "kind": event["kind"],
                "resolution_status": event.get("resolution_status", "exact"),
                "candidates": list(event["normalized_candidates"]),
            })
    return result


def context_closure(roots: set[str], registry: dict[str, dict]) -> list[str]:
    visited: set[str] = set()
    visiting: set[str] = set()

    def visit(identifier: str) -> None:
        if identifier in visited:
            return
        if identifier in visiting:
            raise ConstraintError(f"dependency cycle at {identifier}")
        if identifier not in registry:
            raise ConstraintError(f"missing metadata for {identifier}")
        visiting.add(identifier)
        for dependency in registry[identifier].get("normalized_dependencies", []):
            visit(dependency)
        visiting.remove(identifier)
        visited.add(identifier)

    for root in sorted(roots):
        visit(root)
    return sorted(visited)


def compile_manifest(skeleton: dict, registry: dict[str, dict], *, strict: bool = True,
                     global_conventions: list[str] | None = None) -> dict:
    permissions = event_permissions(skeleton)
    conventions = list(global_conventions or [])
    if len(conventions) != len(set(conventions)):
        raise ConstraintError("global conventions must be unique")
    printed_candidates = {
        candidate for permission in permissions for candidate in permission["candidates"]
    }
    all_candidates = printed_candidates | set(conventions)
    missing = sorted(candidate for candidate in all_candidates if candidate not in registry)
    non_kernel = sorted(
        candidate for candidate in all_candidates
        if candidate in registry and registry[candidate].get("formal_status") != "kernel-checked"
    )
    unresolved = [
        permission for permission in permissions
        if permission["resolution_status"] == "locus-required"
    ]
    if strict and (missing or non_kernel or unresolved):
        details = []
        if missing:
            details.append(f"missing metadata: {missing}")
        if non_kernel:
            details.append(f"not kernel-checked: {non_kernel}")
        if unresolved:
            details.append("aliases require a current PM locus")
        raise ConstraintError("; ".join(details))

    available = all_candidates - set(missing) - set(non_kernel)
    closure = context_closure(available, registry)
    declarations = {
        identifier: registry[identifier]["declaration"]
        for identifier in closure
    }
    lean_paths = sorted({registry[identifier]["lean_path"] for identifier in closure})
    return {
        "kind": "pm-constrained-prover-manifest",
        "policy": {
            "proof_permissions_are_exact": True,
            "context_closure_grants_proof_permission": False,
            "strict": strict,
        },
        "current_item": skeleton.get("current_item"),
        "proof_permissions": permissions,
        "global_conventions": conventions,
        "allowed_pm_items": sorted(available),
        "allowed_lean_declarations": {
            identifier: declarations[identifier] for identifier in sorted(available)
        },
        "context_closure": closure,
        "context_declarations": declarations,
        "context_lean_paths": lean_paths,
        "diagnostics": {
            "missing_items": missing,
            "non_kernel_checked_items": non_kernel,
            "unresolved_aliases": unresolved,
        },
        "substitutions": [
            {"step": index, "printed": substitution}
            for index, step in enumerate(skeleton["steps"], start=1)
            for substitution in step["substitutions"]
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path, help="PM demonstration text")
    parser.add_argument("--item", required=True, help="current PM item, e.g. PM1:✱3·37")
    parser.add_argument("--volume", type=int, default=1)
    parser.add_argument("--metadata-dir", type=Path, default=Path("metadata/items"))
    parser.add_argument("--diagnostic", action="store_true", help="emit incomplete manifests")
    parser.add_argument("--global-convention", action="append", default=[],
                        help="reviewed implicit PM rule licensed at this locus")
    options = parser.parse_args()
    skeleton = parse_demonstration(
        options.source.read_text(encoding="utf-8"), options.volume, options.item
    )
    manifest = compile_manifest(
        skeleton, load_item_registry(options.metadata_dir), strict=not options.diagnostic,
        global_conventions=options.global_convention,
    )
    print(json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
