#!/usr/bin/env python3
"""Audit every returned Lean declaration in an ordered PM batch manifest."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

from pm_constraint_audit import classify_reconstruction
from pm_constraint_manifest import load_item_registry
from verify_dependencies import declaration_body, strip_lean_comments, _occurs


class BatchAuditError(ValueError):
    pass


def audit_batch(manifest: dict, source_path: Path, registry: dict[str, dict],
                aliases: dict) -> dict:
    if manifest.get("kind") != "pm-constrained-prover-batch-manifest":
        raise BatchAuditError("not an ordered PM batch manifest")
    declarations = {identifier: item["declaration"] for identifier, item in registry.items()}
    declarations.update(manifest["target_declarations"])
    realization_to_id = dict(aliases.get("lean_realizations", {}))
    declaration_to_id = {declaration: identifier for identifier, declaration in declarations.items()}
    declaration_to_id.update(realization_to_id)
    declaration_to_id["PM.Derivation.detach"] = None

    audits = []
    for item_manifest in manifest["batch_items"]:
        identifier = item_manifest["current_item"]
        body = strip_lean_comments(declaration_body(
            source_path, manifest["target_declarations"][identifier]
        ))
        proof = body.split(":=", 1)[1] if ":=" in body else ""
        used = {
            pm_id for declaration, pm_id in declaration_to_id.items()
            if pm_id is not None and pm_id != identifier and _occurs(proof, declaration)
        }
        # `detach` realizes the reviewed real-variable convention in these
        # schemas; unlike ordinary context declarations, it is a proof use.
        if _occurs(proof, "PM.Derivation.detach"):
            conventions = item_manifest.get("global_conventions", [])
            if "PM1:✱1·11" not in conventions:
                raise BatchAuditError(f"{identifier}: detach lacks reviewed convention")
            used.add("PM1:✱1·11")

        indexed_short = {name.rsplit(".", 1)[-1] for name in declaration_to_id}
        unknown = sorted({
            token for token in re.findall(r"\bstar_[0-9]+(?:_[0-9]+)+\b", proof)
            if token not in indexed_short
        })
        if unknown:
            raise BatchAuditError(f"{identifier}: unindexed returned references {unknown}")
        audits.append(classify_reconstruction(item_manifest, sorted(used)))
    return {
        "kind": "pm-constrained-batch-reconstruction-audit",
        "target_order": list(manifest["target_order"]),
        "all_targets_strict": all(
            audit["classification"] == "strict-closure" for audit in audits
        ),
        "target_audits": audits,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("lean_source", type=Path)
    parser.add_argument("--metadata-dir", type=Path, default=Path("metadata/items"))
    parser.add_argument("--aliases", type=Path, default=Path("metadata/dependency_aliases.json"))
    parser.add_argument("--output", type=Path)
    options = parser.parse_args()
    result = audit_batch(
        json.loads(options.manifest.read_text(encoding="utf-8")),
        options.lean_source,
        load_item_registry(options.metadata_dir),
        json.loads(options.aliases.read_text(encoding="utf-8")),
    )
    rendered = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if options.output:
        options.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
