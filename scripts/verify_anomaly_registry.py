#!/usr/bin/env python3
"""Verify the central PM anomaly register and its reviewed source links."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from generate_anomaly_registry import build


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "metadata/anomalies/PM1-anomaly-register.json"
SCHEMA = ROOT / "metadata/schema/anomaly-registry.schema.json"
CATEGORIES = {
    "printed-error-unofficial", "incomplete-printed-citation", "notation-ambiguity",
    "digital-witness-error", "reconstruction-gap",
}
REQUIRED = {
    "id", "category", "pm_locus", "printed_reading", "printed_citations",
    "corrected_or_added_reading", "canonical_witness_evidence", "digital_witnesses",
    "affected_ast_items_batches", "strict_audit_status", "minimal_relaxation",
    "lean_impact", "review_provenance", "resolution_status",
}
REQUIRED_MANUAL = {
    "PM1-ANOM-Q220-ASSOCIATION-GAP",
    "PM1-ANOM-Q221-FIRST-ARCHIVE-FIDELITY-GAP",
    "PM1-ANOM-Q222-ASSOCIATION-GAP",
}


def fail(message: str) -> None:
    print(f"anomaly registry error: {message}", file=sys.stderr)
    raise SystemExit(1)


def verify_registry(root: Path = ROOT) -> dict:
    path = root / REGISTRY.relative_to(ROOT)
    if not path.exists():
        fail("central registry is missing")
    try:
        actual = json.loads(path.read_text(encoding="utf-8"))
        expected = build(root)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        fail(str(error))
    if actual != expected:
        fail("registry differs from the deterministic apparatus/manual backfill")
    if not (root / SCHEMA.relative_to(ROOT)).exists():
        fail("registry schema is missing")
    if actual.get("schema_version") != 1 or actual.get("id") != "PM1-ANOMALY-REGISTER":
        fail("invalid registry header")
    official = actual.get("official_errata_registry", {})
    if official.get("id") != "PM1-1910-ERRATA" or len(official.get("entry_ids", [])) != 13:
        fail("official Errata must be linked completely, not copied")
    entries = actual.get("entries")
    if not isinstance(entries, list) or not entries:
        fail("entries must be a non-empty list")
    identifiers = [entry.get("id") for entry in entries]
    if len(set(identifiers)) != len(identifiers) or any(not identifier for identifier in identifiers):
        fail("anomaly IDs must be unique and present")
    official_ids = set(official["entry_ids"])
    for entry in entries:
        missing = REQUIRED - entry.keys()
        if missing:
            fail(f"{entry['id']} lacks {sorted(missing)}")
        if entry["category"] not in CATEGORIES:
            fail(f"{entry['id']} has unknown category")
        witness = entry["canonical_witness_evidence"]
        if not witness.get("canonical_scan", "").startswith("https://"):
            fail(f"{entry['id']} lacks canonical witness URL")
        if len(witness.get("sha256", "")) != 64:
            fail(f"{entry['id']} lacks a 64-character canonical reading hash")
        if not entry["review_provenance"]:
            fail(f"{entry['id']} lacks review provenance")
        links = set(entry.get("linked_official_errata_ids", []))
        if not links <= official_ids:
            fail(f"{entry['id']} links an unknown official Errata ID")
        if entry["id"] in official_ids:
            fail("official Errata entry duplicated as an anomaly")
        if entry["category"] == "digital-witness-error" and not entry.get("apparatus_id"):
            fail(f"{entry['id']} digital witness entry lacks apparatus link")
    by_id = {entry["id"]: entry for entry in entries}
    if not REQUIRED_MANUAL <= by_id.keys():
        fail("Q220, Q221, and Q222 reconstruction gaps must be backfilled")
    if by_id["PM1-ANOM-Q222-ASSOCIATION-GAP"]["minimal_relaxation"] != ["PM1:✱2·32"]:
        fail("Q222 must record only the approved minimal ✱2·32 relaxation")
    if by_id["PM1-ANOM-Q221-FIRST-ARCHIVE-FIDELITY-GAP"]["resolution_status"] != "resolved-strict-retry":
        fail("Q221 first-archive gap must remain a resolved reconstruction gap")
    digital = [entry for entry in entries if entry["category"] == "digital-witness-error"]
    if not digital:
        fail("attested digital witness errors were not backfilled")
    return actual


def main() -> None:
    payload = verify_registry()
    digital = sum(entry["category"] == "digital-witness-error" for entry in payload["entries"])
    print(f"anomaly registry checks passed ({len(payload['entries'])} entries; {digital} digital witness errors)")


if __name__ == "__main__":
    main()
