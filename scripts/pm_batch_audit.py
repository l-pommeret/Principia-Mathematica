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


LOCAL_DECLARATION = re.compile(
    r"(?m)^\s*(?:private\s+)?(?:theorem|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)


def occurs_qualified(body: str, declaration: str) -> bool:
    """Recognize full, unqualified, and namespace-suffix Lean references."""
    if _occurs(body, declaration):
        return True
    short = declaration.rsplit(".", 1)[-1]
    return re.search(
        rf"(?<![A-Za-z0-9_'])"
        rf"(?:[A-Za-z_][A-Za-z0-9_']*\.)+{re.escape(short)}"
        rf"(?![A-Za-z0-9_'])",
        body,
    ) is not None


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
    local_names = set(LOCAL_DECLARATION.findall(source_path.read_text(encoding="utf-8")))
    target_short_to_id = {
        declaration.rsplit(".", 1)[-1]: identifier
        for identifier, declaration in manifest["target_declarations"].items()
    }

    def proof_of(name: str) -> str:
        lines = source_path.read_text(encoding="utf-8").splitlines()
        start = next(
            (index for index, line in enumerate(lines)
             if (match := LOCAL_DECLARATION.match(line)) and match.group(1) == name),
            None,
        )
        if start is None:
            raise BatchAuditError(f"local declaration {name} not found")
        end = next(
            (index for index in range(start + 1, len(lines))
             if LOCAL_DECLARATION.match(lines[index]) or re.match(r"^\s*end\b", lines[index])),
            len(lines),
        )
        body = strip_lean_comments("\n".join(lines[start:end]))
        return body.split(":=", 1)[1] if ":=" in body else ""

    def collect_used(proof: str, identifier: str, conventions: list[str],
                     allowed_items: list[str],
                     visited_helpers: set[str]) -> set[str]:
        used = {
            pm_id for declaration, pm_id in declaration_to_id.items()
            if pm_id is not None and pm_id != identifier
            and occurs_qualified(proof, declaration)
        }
        if occurs_qualified(proof, "PM.Derivation.detach"):
            licensed = set(conventions) | set(allowed_items)
            if "PM1:✱1·11" in licensed:
                used.add("PM1:✱1·11")
            elif "PM1:✱1·1" in licensed:
                used.add("PM1:✱1·1")
            else:
                raise BatchAuditError(
                    f"{identifier}: detach lacks an explicit or reviewed PM rule"
                )
        for local in sorted(local_names):
            if local in visited_helpers or not occurs_qualified(proof, local):
                continue
            if local in target_short_to_id:
                used.add(target_short_to_id[local])
                continue
            visited_helpers.add(local)
            used.update(collect_used(
                proof_of(local), identifier, conventions, allowed_items,
                visited_helpers
            ))
        return used

    audits = []
    for item_manifest in manifest["batch_items"]:
        identifier = item_manifest["current_item"]
        body = strip_lean_comments(declaration_body(
            source_path, manifest["target_declarations"][identifier]
        ))
        proof = body.split(":=", 1)[1] if ":=" in body else ""
        used = collect_used(
            proof, identifier, item_manifest.get("global_conventions", []),
            item_manifest.get("allowed_pm_items", []), set()
        )

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
