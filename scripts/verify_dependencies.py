#!/usr/bin/env python3
"""Audit direct historical/Lean dependency agreement without running Lean.

This deliberately audits the source term supplied to Lean.  GitHub CI's later
``lake build`` step remains the authority that the term was accepted by the
kernel.  Together the two checks establish, for items marked kernel-checked,
both term acceptance and agreement with the dependencies printed in PM.
"""

from __future__ import annotations

import json
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DECL_START = re.compile(r"^\s*(?:theorem|def|abbrev)\s+([A-Za-z0-9_']+)\b")
KNOWN_BRIDGES = {"PM.Derivation.detach"}
KNOWN_SYNTAX_INFRASTRUCTURE = {
    "PM.FirstOrder.neg",
    "PM.FirstOrder.always",
    "PM.FirstOrder.sometimes",
}


class DependencyError(ValueError):
    pass


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments from source text.

    Dependency extraction concerns the term accepted by Lean, not editorial
    prose adjacent to it.  Keep strings intact because printed-reading
    declarations are never audited as theorem bodies.
    """
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth:
            index += 1
        elif source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                break
            result.append("\n")
            index = newline + 1
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


def pm_order(item_id: str) -> tuple[int, int, Fraction]:
    match = re.fullmatch(r"PM([0-9]+):✱([0-9]+)·([0-9]+)", item_id)
    if not match:
        raise DependencyError(f"cannot order PM item ID {item_id}")
    volume, integral, fractional = match.groups()
    return int(volume), int(integral), Fraction(int(fractional), 10 ** len(fractional))


def load_items(root: Path = ROOT) -> list[dict]:
    result = []
    for path in sorted((root / "metadata/items").glob("*.json")):
        batch = json.loads(path.read_text(encoding="utf-8"))
        for item in batch["items"]:
            record = dict(item)
            record["_metadata_path"] = str(path.relative_to(root))
            result.append(record)
    return result


def declaration_body(path: Path, declaration: str) -> str:
    """Return a declaration through the line before the next declaration."""
    short = declaration.rsplit(".", 1)[-1]
    lines = path.read_text(encoding="utf-8").splitlines()
    start = None
    for index, line in enumerate(lines):
        match = DECL_START.match(line)
        if match and match.group(1) == short:
            start = index
            break
    if start is None:
        raise DependencyError(f"declaration {declaration} not found in {path}")
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if DECL_START.match(lines[index]) or re.match(r"^\s*end\b", lines[index]):
            end = index
            break
    return "\n".join(lines[start:end])


def _occurs(body: str, name: str) -> bool:
    variants = (name, name.rsplit(".", 1)[-1])
    return any(re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(variant)}(?![A-Za-z0-9_'])", body)
               for variant in variants)


def reject_unindexed_references(item: dict, body: str, candidates: set[str]) -> None:
    """Reject conspicuous theorem calls that could evade the PM index.

    This is intentionally conservative source auditing, not an elaborator.
    Qualified constants and PM-style theorem names in the proof term must be
    represented by the dependency catalogue. GitHub's Lean step subsequently
    supplies the authoritative elaborated/kernel check.
    """
    proof = body.split(":=", 1)[1] if ":=" in body else ""
    indexed_short = {name.rsplit(".", 1)[-1] for name in candidates}
    for token in re.findall(r"\b[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+", proof):
        if token not in candidates and token.rsplit(".", 1)[-1] not in indexed_short:
            raise DependencyError(f"{item['id']}: unindexed qualified Lean reference {token}")
    for token in re.findall(r"\bstar_[0-9]+(?:_[0-9]+)+\b", proof):
        if token not in indexed_short:
            raise DependencyError(f"{item['id']}: unindexed PM-style Lean reference {token}")


def extract_lean_dependencies(item: dict, declarations: dict[str, str], root: Path = ROOT) -> list[str]:
    if item["kind"] in {"primitive-inference-rule", "primitive-function-inference-rule"}:
        # These are constructors of the Derivation inductive, hence have no
        # proof body and no prior dependencies to extract.
        return []
    body = strip_lean_comments(
        declaration_body(root / item["lean_path"], item["declaration"])
    )
    aliases = json.loads((root / "metadata/dependency_aliases.json").read_text(encoding="utf-8"))
    candidates = set(declarations) | set(aliases["lean_realizations"]) | KNOWN_BRIDGES
    reject_unindexed_references(item, body, candidates | KNOWN_SYNTAX_INFRASTRUCTURE)
    # Longest first avoids treating one fully qualified name as a prefix.
    return sorted(name for name in candidates if name != item["declaration"] and _occurs(body, name))


def normalize(item: dict, lean_dependencies: list[str], declaration_to_id: dict[str, str], root: Path = ROOT) -> list[str]:
    aliases = json.loads((root / "metadata/dependency_aliases.json").read_text(encoding="utf-8"))
    realizations = aliases["lean_realizations"]
    normalized: list[str] = []
    for name in lean_dependencies:
        if name == "PM.Derivation.detach":
            choices = set(aliases["bridges"][name]["resolves_to"])
            selected = [dep for dep in item.get("printed_dependencies", []) if dep in choices]
            if len(selected) != 1:
                raise DependencyError(f"{item['id']}: detach must resolve to exactly one printed primitive rule")
            normalized.extend(selected)
        elif name in declaration_to_id or name in realizations:
            dependency = declaration_to_id.get(name, realizations.get(name))
            # A primitive wrapper merely realizes the current printed Pp.; it
            # does not acquire a historical self-dependency.
            if dependency != item["id"]:
                normalized.append(dependency)
        else:
            raise DependencyError(f"{item['id']}: no PM resolution for Lean dependency {name}")
    for bridge in item.get("dependency_justifications", []):
        if bridge.get("kind") == "metalinguistic-rule-selection":
            if (bridge.get("lean_dependency") != "PM.Derivation.detach" or
                    bridge.get("pm_dependency") not in normalized or not bridge.get("evidence")):
                raise DependencyError(f"{item['id']}: invalid detachment justification {bridge!r}")
            continue
        if bridge.get("kind") != "definitional-reading" or bridge.get("pm_dependency") != "PM1:✱1·01":
            raise DependencyError(f"{item['id']}: unsupported normalization justification {bridge!r}")
        if not bridge.get("evidence"):
            raise DependencyError(f"{item['id']}: normalization justification lacks evidence")
        normalized.append(bridge["pm_dependency"])
    return sorted(set(normalized))


def audit(root: Path = ROOT) -> dict:
    items = load_items(root)
    checked = [item for item in items if item.get("formal_status") == "kernel-checked"]
    declarations = {item["declaration"]: item["id"] for item in items}
    order = {item["id"]: pm_order(item["id"]) for item in items}
    aliases = json.loads((root / "metadata/dependency_aliases.json").read_text(encoding="utf-8"))
    for alias, resolutions in aliases["aliases"].items():
        if not resolutions or any(resolution not in order for resolution in resolutions):
            raise DependencyError(f"alias {alias} has an empty or unknown PM resolution")
    edges = []
    lean_edges = []
    for item in checked:
        for field in ("printed_dependencies", "lean_dependencies", "normalized_dependencies"):
            if field not in item or not isinstance(item[field], list):
                raise DependencyError(f"{item['id']}: missing dependency field {field}")
        actual = extract_lean_dependencies(item, declarations, root)
        if sorted(item["lean_dependencies"]) != actual:
            raise DependencyError(
                f"{item['id']}: Lean dependencies differ: metadata={sorted(item['lean_dependencies'])}, extracted={actual}"
            )
        normalized = normalize(item, actual, declarations, root)
        if sorted(set(item["normalized_dependencies"])) != normalized:
            raise DependencyError(f"{item['id']}: normalized metadata {item['normalized_dependencies']} != {normalized}")
        if sorted(set(item["printed_dependencies"])) != normalized:
            raise DependencyError(
                f"{item['id']}: printed dependencies {item['printed_dependencies']} != normalized Lean dependencies {normalized}"
            )
        for dependency in normalized:
            if dependency not in order:
                raise DependencyError(f"{item['id']}: unknown PM dependency {dependency}")
            if order[dependency] >= order[item["id"]]:
                raise DependencyError(f"{item['id']}: dependency {dependency} is not earlier in the audited corpus")
            edges.append({"from": item["id"], "to": dependency})
        lean_edges.extend({"from": item["id"], "to": dependency}
                          for dependency in actual)
    return {
        "schema_version": 1,
        "coverage": {
            "status": "kernel-checked-items-only",
            "audited_items": len(checked),
            "total_metadata_items": len(items),
        },
        "nodes": [{"id": item["id"], "kind": item["kind"], "formal_status": item["formal_status"]}
                  for item in items],
        "historical_graph": {"edges": edges},
        "lean_graph": {"edges": lean_edges},
        # Kept as a small compatibility convenience for downstream readers.
        "edges": edges,
    }


def main() -> None:
    try:
        graph = audit()
    except (DependencyError, OSError, json.JSONDecodeError) as error:
        print(f"dependency error: {error}", file=sys.stderr)
        raise SystemExit(1)
    print(f"dependency checks passed ({graph['coverage']['audited_items']} kernel-checked items, {len(graph['edges'])} edges)")


if __name__ == "__main__":
    main()
