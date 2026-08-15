#!/usr/bin/env python3
"""Derive the read-only certification registry from catalogue and gate facts.

The catalogue is allowed to state evidence: a printed formula, its source, a
Lean path and declaration, CI provenance, and declared assumptions.  It is not
allowed to decide the result of evaluating that evidence.  In particular this
module deliberately removes every legacy certification conclusion before it
calls the gates.

``--write`` is the sole generator for ``docs/certification_registry.json``.
``--check`` renders the same bytes in memory and rejects a missing or modified
registry.  Neither mode rewrites the 6,203 catalogue items.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from copy import deepcopy
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pm_lean_index import declarations, import_closure  # noqa: E402
from verify_axiom_audit import (  # noqa: E402
    ALLOWED_AXIOMS,
    ToolchainError,
    audit_declarations,
)
from verify_certification_tier import (  # noqa: E402
    REQUIRED_FORMALIZATION_LEVEL,
    TIER_AWAITING,
    TIER_MAX,
    TIER_PREPARED,
    TIER_TYPECHECKED,
    TIER_UNBUILT,
    compute,
    constructor_site,
    duplicate_statements,
    load_batches,
)
from verify_ci_evidence import evidence_failures  # noqa: E402
from verify_judgement_primitives import audit as audit_judgement_primitives  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REGISTRY = ROOT / "docs" / "certification_registry.json"

# These are outputs of the certification computation, even while the legacy
# catalogue still stores them.  Keeping the list here makes the trust boundary
# executable: changing any of these fields cannot change the derived answer.
CONCLUSION_FIELDS = frozenset(
    {
        "certification",
        "certification_tier",
        "formal_status",
        "formalization_level",
    }
)

TIERS = (
    TIER_PREPARED,
    TIER_UNBUILT,
    TIER_TYPECHECKED,
    TIER_AWAITING,
    TIER_MAX,
)

# T8 is necessarily a property of the stored derived registry, not an input to
# an item's tier.  It is enforced by byte-for-byte comparison in ``--check``.
CRITERIA = {
    "T1": "lean_path is in the import closure of Principia.lean",
    "T2": "declaration resolves with the declaration kind required by the item",
    "T3": "the statement is a judgement of the reconstructed object calculus",
    "T4": "the printed string, reading AST, and asserted formula agree",
    "T5": "the kernel reports no disallowed axiom",
    "T6": "the statement is neither vacuous nor duplicated",
    "T7": "CI evidence resolves, is ancestral, successful, and fresh",
    "T8": "the stored registry is exactly the output of this derivation",
    "T9": "every reached non-logical assumption is declared",
    "T10": "every judgement constructor is backed by a printed primitive",
    "T11": "the asserted formula uses PM object notation",
}


class RegistryDerivationError(RuntimeError):
    """The gates could not produce an auditable registry."""


def _facts(item: dict) -> dict:
    """Return a defensive copy with all legacy conclusions erased."""
    return {
        key: deepcopy(value)
        for key, value in item.items()
        if key not in CONCLUSION_FIELDS
    }


def _resolved(item: dict) -> bool:
    lean_path = item.get("lean_path")
    declaration = item.get("declaration")
    if not isinstance(lean_path, str) or not lean_path:
        return False
    if not isinstance(declaration, str) or not declaration:
        return False
    base = declaration.rsplit(".", 1)[-1]
    if base in declarations(lean_path):
        return True
    return constructor_site(lean_path, base) is not None


def _tier(item: dict, resolved: bool, failed: set[str]) -> str:
    """Map factual target state and failed gates to the public tier.

    The order matters.  A catalogue entry with no concrete Lean target remains
    prepared.  A named module outside the aggregate is unbuilt.  Only a
    resolvable declaration can be called Lean-typechecked.  Structural success
    without fresh CI is awaiting-ci, and complete success is kernel-checked.
    """
    lean_path = item.get("lean_path")
    declaration = item.get("declaration")
    has_path = isinstance(lean_path, str) and bool(lean_path.strip())
    has_declaration = isinstance(declaration, str) and bool(declaration.strip())

    if not has_path or not has_declaration:
        return TIER_PREPARED
    if "T1" in failed:
        return TIER_UNBUILT
    if not resolved:
        return TIER_PREPARED
    structural = failed - {"T7"}
    if structural:
        return TIER_TYPECHECKED
    if "T7" in failed:
        return TIER_AWAITING
    return TIER_MAX


def _base_records() -> list[dict]:
    """Run the item-local gates without accepting any stored conclusion."""
    records: list[dict] = []
    seen: set[str] = set()
    for path, batch in load_batches():
        items = batch.get("items", [])
        if not isinstance(items, list):
            raise RegistryDerivationError(f"{path}: items must be a list")
        ci_failures = evidence_failures(path, batch.get("ci_evidence") or {}, items)
        for raw in items:
            if not isinstance(raw, dict):
                raise RegistryDerivationError(f"{path}: item must be an object")
            identifier = raw.get("id")
            if not isinstance(identifier, str) or not identifier:
                raise RegistryDerivationError(f"{path}: item has no string id")
            if identifier in seen:
                raise RegistryDerivationError(f"duplicate catalogue id: {identifier}")
            seen.add(identifier)

            item = _facts(raw)
            # ``compute`` still contains the transitional, claim-based T8.  A
            # neutral synthetic value lets it run its factual T1-T7/T9/T11
            # checks; T8 is then discarded and enforced at registry level.
            probe = dict(item)
            probe["formal_status"] = "<derived>"
            probe["formalization_level"] = REQUIRED_FORMALIZATION_LEVEL
            _, failed, notes = compute(probe, ci_failures)
            failures = set(failed) - {"T8"}
            notes = {key: value for key, value in notes.items() if key != "T8"}

            lean_path = item.get("lean_path") or ""
            declaration = item.get("declaration") or ""
            base = declaration.rsplit(".", 1)[-1]
            declared = declarations(lean_path).get(base) if lean_path else None
            records.append(
                {
                    "id": identifier,
                    "batch": str(path.relative_to(ROOT)),
                    "item": item,
                    "resolved": _resolved(item),
                    "failed": failures,
                    "notes": notes,
                    "_declaration": declared,
                }
            )

    duplicate_groups = duplicate_statements(records)
    duplicate_ids = {
        identifier
        for identifiers in duplicate_groups.values()
        for identifier in identifiers
    }
    for record in records:
        if record["id"] in duplicate_ids:
            record["failed"].add("T6")
            record["notes"]["T6"] = (
                "statement is byte-identical to another catalogue item's in "
                "the same Lean file"
            )
    return records


def _apply_kernel_gates(records: list[dict]) -> dict[str, dict]:
    """Run T5 and T10, adding their per-item consequences in place."""
    structural_candidates = [
        record
        for record in records
        if record["resolved"]
        and not (record["failed"] - {"T7"})
        and "T1" not in record["failed"]
    ]

    names = sorted(
        {
            record["item"].get("declaration")
            for record in structural_candidates
            if isinstance(record["item"].get("declaration"), str)
            and record["item"].get("declaration")
        }
    )
    axiom_results: dict[str, list[str]] = {}
    if names:
        try:
            axiom_results = audit_declarations(names)
        except ToolchainError as error:
            raise RegistryDerivationError(f"T5 could not run: {error}") from error

    for record in structural_candidates:
        name = record["item"].get("declaration")
        axioms = axiom_results.get(name, ["<unresolved>"])
        disallowed = [axiom for axiom in axioms if axiom not in ALLOWED_AXIOMS]
        if disallowed:
            record["failed"].add("T5")
            record["notes"]["T5"] = (
                f"kernel axiom audit reports {', '.join(disallowed)}"
            )

    primitive_problems, primitive_stats = audit_judgement_primitives()
    if not primitive_stats.get("relations"):
        raise RegistryDerivationError("T10 found no judgement relation; gate did not run")
    if primitive_problems:
        detail = "; ".join(primitive_problems)
        for record in structural_candidates:
            record["failed"].add("T10")
            record["notes"]["T10"] = detail

    return {
        "T5": {
            "audited_declarations": len(axiom_results),
            "passed": all(
                all(axiom in ALLOWED_AXIOMS for axiom in axioms)
                for axioms in axiom_results.values()
            ),
        },
        "T10": {
            "passed": not primitive_problems,
            "problems": primitive_problems,
            "statistics": primitive_stats,
        },
    }


def derive_registry() -> dict:
    """Return the canonical registry object; no stored tier is consulted."""
    records = _base_records()
    gate_results = _apply_kernel_gates(records)

    derived_items: list[dict] = []
    counts: Counter[str] = Counter()
    for record in sorted(records, key=lambda value: value["id"]):
        failed = set(record["failed"])
        tier = _tier(record["item"], record["resolved"], failed)
        structural = failed - {"T7"}
        level = REQUIRED_FORMALIZATION_LEVEL if not structural else None
        counts[tier] += 1
        derived_items.append(
            {
                "batch": record["batch"],
                "canonical_integration_eligible": tier == TIER_MAX,
                "certification_tier": tier,
                "diagnostics": {
                    key: record["notes"][key]
                    for key in sorted(record["notes"])
                    if key in failed
                },
                "failed_criteria": sorted(failed),
                "formalization_level": level,
                "id": record["id"],
            }
        )

    return {
        "kind": "pm-derived-certification-registry",
        "schema_version": 1,
        "derivation": {
            "catalogue": "metadata/items/*.json",
            "conclusion_fields_ignored": sorted(CONCLUSION_FIELDS),
            "criteria": CRITERIA,
            "generator": "scripts/derive_certification_registry.py",
        },
        "gate_results": gate_results,
        "census": {tier: counts.get(tier, 0) for tier in TIERS},
        "items": derived_items,
    }


def render(registry: dict) -> str:
    return json.dumps(registry, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def _destination(value: Path) -> Path:
    return value if value.is_absolute() else ROOT / value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write", action="store_true", help="regenerate the registry")
    modes.add_argument(
        "--check",
        action="store_true",
        help="fail unless the stored registry is the exact derived output",
    )
    parser.add_argument(
        "--registry",
        type=Path,
        default=DEFAULT_REGISTRY,
        help=f"registry path (default: {DEFAULT_REGISTRY.relative_to(ROOT)})",
    )
    arguments = parser.parse_args(argv)

    try:
        expected = render(derive_registry())
    except (OSError, json.JSONDecodeError, RegistryDerivationError) as error:
        print(f"certification registry derivation failed: {error}", file=sys.stderr)
        return 1

    destination = _destination(arguments.registry)
    if arguments.write:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(expected, encoding="utf-8")
        print(
            f"derived certification registry written: "
            f"{destination.relative_to(ROOT) if destination.is_relative_to(ROOT) else destination}"
        )
        return 0

    if not destination.is_file():
        print(f"certification registry missing: {destination}", file=sys.stderr)
        return 1
    actual = destination.read_text(encoding="utf-8")
    if actual != expected:
        print(
            "certification registry drift: stored bytes are not the output of "
            f"scripts/derive_certification_registry.py --write ({destination})",
            file=sys.stderr,
        )
        return 1
    registry = json.loads(expected)
    print(
        "certification registry verified "
        f"({len(registry['items'])} items; exact derived bytes)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
