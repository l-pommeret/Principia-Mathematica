#!/usr/bin/env python3
"""Verify the complete printed Errata registry and its apparatus links."""

from __future__ import annotations

import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "metadata/errata/PM1-1910-errata.json"
APPARATUS = ROOT / "metadata/apparatus"
SOURCE_BLOCKS = ROOT / "metadata/source_blocks"
EXPECTED_DERIVATIVE = "1b258d38fac5059d15030f1cc7ee6ea71e441e855099a3a01beb45871956221f"


def fail(message: str) -> None:
    print(f"errata registry error: {message}", file=sys.stderr)
    raise SystemExit(1)


def load_records(directory: Path) -> dict[str, dict]:
    records: dict[str, dict] = {}
    for path in sorted(directory.glob("*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        identifier = record.get("id")
        if not identifier or identifier in records:
            fail(f"missing or duplicate ID in {path}")
        records[identifier] = record
    return records


def verify_registry(root: Path = ROOT) -> dict:
    path = root / REGISTRY.relative_to(ROOT)
    payload = json.loads(path.read_text(encoding="utf-8"))
    if (payload.get("schema_version"), payload.get("id"), payload.get("edition"),
            payload.get("volume")) != (1, "PM1-1910-ERRATA", "first", 1):
        fail("invalid registry header")
    source = payload.get("source", {})
    if source.get("scan_leaf") != 15 or source.get("derivative_sha256") != EXPECTED_DERIVATIVE:
        fail("canonical Errata leaf or derivative hash differs from the audited witness")
    if not source.get("canonical_scan", "").startswith("https://commons.wikimedia.org/"):
        fail("canonical Commons source is missing")
    if len(source.get("scan_sha256", "")) != 64 or source.get("status") != "facsimile-verified":
        fail("global scan provenance is incomplete")

    entries = payload.get("entries")
    if not isinstance(entries, list) or len(entries) != 13:
        fail("the first-edition volume-I registry must contain exactly 13 entries")
    identifiers = [entry.get("id") for entry in entries]
    if None in identifiers or len(set(identifiers)) != 13:
        fail("Errata entry IDs must be present and unique")

    apparatus = load_records(root / APPARATUS.relative_to(ROOT))
    source_blocks = load_records(root / SOURCE_BLOCKS.relative_to(ROOT))
    linked_apparatus: set[str] = set()
    linked = pending = 0
    for entry in entries:
        for field in ("printed_page", "line", "operation", "diplomatic_instruction", "integration"):
            if field not in entry:
                fail(f"{entry['id']} lacks {field}")
        operation = entry["operation"]
        required_by_operation = {
            "replace": {"printed", "corrected"},
            "insert-after": {"anchor", "inserted"},
            "delete": {"deleted"},
        }
        if operation not in required_by_operation:
            fail(f"{entry['id']} has unknown operation {operation!r}")
        if not required_by_operation[operation] <= entry.keys():
            fail(f"{entry['id']} lacks fields required for {operation}")
        integration = entry["integration"]
        status = integration.get("status")
        if status == "integrated":
            linked += 1
            apparatus_id = integration.get("apparatus_id")
            source_item = integration.get("source_item")
            if not apparatus_id or not source_item:
                fail(f"integrated entry {entry['id']} lacks source/apparatus links")
            if apparatus_id in linked_apparatus:
                fail(f"apparatus notice {apparatus_id} is linked more than once")
            linked_apparatus.add(apparatus_id)
            notice = apparatus.get(apparatus_id)
            if notice is None:
                fail(f"{entry['id']} links unknown apparatus notice {apparatus_id}")
            if notice.get("item") != source_item or source_item not in source_blocks:
                fail(f"{entry['id']} source-block link disagrees with its apparatus notice")
            if notice.get("locus", {}).get("printed_page") != entry["printed_page"]:
                fail(f"{entry['id']} page disagrees with its apparatus notice")
        elif status == "pending":
            pending += 1
            if not integration.get("reason"):
                fail(f"pending entry {entry['id']} lacks a reason")
            if integration.get("apparatus_id") or integration.get("source_item"):
                fail(f"pending entry {entry['id']} must not pretend to be integrated")
        else:
            fail(f"{entry['id']} has invalid integration status {status!r}")

    errata_notices = {
        identifier for identifier, notice in apparatus.items()
        if any("ERRATA" in witness.get("siglum", "").upper()
               for witness in notice.get("witnesses", []))
    }
    if linked_apparatus != errata_notices:
        fail(
            "registry/apparatus coverage differs: "
            f"registry-only={sorted(linked_apparatus - errata_notices)}, "
            f"apparatus-only={sorted(errata_notices - linked_apparatus)}"
        )
    if (linked, pending) != (6, 7):
        fail(f"expected six integrated and seven pending entries, found {linked}/{pending}")
    return payload


def main() -> None:
    verify_registry()
    print("Errata registry checks passed (13 entries: 6 integrated, 7 pending)")


if __name__ == "__main__":
    main()
