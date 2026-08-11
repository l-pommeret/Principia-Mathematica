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
    "PM1-ANOM-Q222-RELAXED-ARCHIVE-UNCOVERED-CITATIONS",
    "PM1-ANOM-Q222-CHAIN-COMPOSITION-GAP",
    "PM1-ANOM-Q222-RETRY02-FORBIDDEN-OUTPUT",
    "PM1-ANOM-Q222-RETRY03-AUDITED-RELAXED-OUTPUT",
    "PM1-ANOM-Q223-IMPLICIT-COMPOSITION-GAP",
}
REQUIRED_INFRASTRUCTURE_INCIDENT = {
    "id", "batch", "service", "project_id", "task_id", "observed_sequence",
    "authoritative_status", "duplicate_submission", "classification",
    "pm_or_reconstruction_impact", "kernel_impact", "provenance", "resolution_status",
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
    incidents = actual.get("infrastructure_incidents")
    if not isinstance(incidents, list):
        fail("infrastructure incidents must be a list")
    incident_ids = [incident.get("id") for incident in incidents]
    if len(set(incident_ids)) != len(incident_ids) or any(not identifier for identifier in incident_ids):
        fail("infrastructure incident IDs must be unique and present")
    for incident in incidents:
        missing = REQUIRED_INFRASTRUCTURE_INCIDENT - incident.keys()
        if missing:
            fail(f"infrastructure incident {incident.get('id', '<missing>')} lacks {sorted(missing)}")
        if incident["classification"] != "infrastructure-transport-failure":
            fail(f"infrastructure incident {incident['id']} has an unknown classification")
        if incident["pm_or_reconstruction_impact"] != "none established; this is neither a PM source anomaly nor a reconstruction finding":
            fail(f"infrastructure incident {incident['id']} must not be classified as a PM/reconstruction anomaly")
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
        fail("Q220 through Q223 reconstruction gaps must be backfilled")
    if by_id["PM1-ANOM-Q222-ASSOCIATION-GAP"]["minimal_relaxation"] != ["PM1:✱2·32"]:
        fail("Q222 must record only the approved minimal ✱2·32 relaxation")
    if by_id["PM1-ANOM-Q221-FIRST-ARCHIVE-FIDELITY-GAP"]["resolution_status"] != "resolved-strict-retry":
        fail("Q221 first-archive gap must remain a resolved reconstruction gap")
    if (by_id["PM1-ANOM-Q222-RELAXED-ARCHIVE-UNCOVERED-CITATIONS"]
            ["resolution_status"] != "blocked-awaiting-targeted-fidelity-continuation"):
        fail("Q222 terminal archive bypass must remain blocked pending fidelity repair")
    chain = by_id["PM1-ANOM-Q222-CHAIN-COMPOSITION-GAP"]
    if (chain["category"] != "incomplete-printed-citation" or chain.get("strict") is not False
            or chain["minimal_relaxation"] != ["PM1:✱2·06"]
            or chain.get("relaxation_use", [{}])[0].get("uses") != 2):
        fail("Q222 chain gap must record the approved non-strict ✱2·06 relaxation twice")
    forbidden = by_id["PM1-ANOM-Q222-RETRY02-FORBIDDEN-OUTPUT"]
    if forbidden["lean_impact"].get("kind") != "forbidden-output":
        fail("Q222 retry-02 must remain a separate forbidden-output reconstruction gap")
    retry03 = by_id["PM1-ANOM-Q222-RETRY03-AUDITED-RELAXED-OUTPUT"]
    if (retry03.get("strict") is not False
            or retry03["resolution_status"] != "resolved-clean-output-kernel-checked"
            or retry03.get("resolves") != [
                "PM1-ANOM-Q222-ASSOCIATION-GAP",
                "PM1-ANOM-Q222-CHAIN-COMPOSITION-GAP",
                "PM1-ANOM-Q222-RETRY02-FORBIDDEN-OUTPUT",
            ]):
        fail("Q222 retry-03 must preserve its kernel-checked documented relaxation")
    q223 = by_id["PM1-ANOM-Q223-IMPLICIT-COMPOSITION-GAP"]
    if (q223["category"] != "incomplete-printed-citation" or q223.get("strict") is not False
            or q223["minimal_relaxation"] != ["PM1:✱1·6"]
            or [entry.get("target") for entry in q223.get("relaxation_use", [])]
            != ["PM1:✱3·27", "PM1:✱3·31"]):
        fail("Q223 must record the exact two-locus non-strict ✱1·6 relaxation")
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
