#!/usr/bin/env python3
"""Generate the central anomaly register from reviewed apparatus plus manual audits."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
APPARATUS = ROOT / "metadata/apparatus"
MANUAL = ROOT / "metadata/anomalies/manual"
ERRATA = ROOT / "metadata/errata/PM1-1910-errata.json"
OUTPUT = ROOT / "metadata/anomalies/PM1-anomaly-register.json"


def reading_hash(reading: str) -> str:
    return hashlib.sha256(reading.encode("utf-8")).hexdigest()


def canonical_witness(record: dict) -> dict:
    witnesses = record["witnesses"]
    canonical = next(
        (witness for witness in witnesses
         if "SCAN" in witness["siglum"].upper()),
        None,
    )
    if canonical is None:
        raise ValueError(f"{record['id']} has no canonical scan witness")
    locus = record["locus"]
    return {
        "canonical_scan": canonical["uri"],
        "scan_leaf": locus["scan_leaf"],
        "sha256": reading_hash(record["diplomatic_reading"]),
        "hash_kind": "UTF-8 canonical diplomatic reading",
    }


def digital_entry(record: dict) -> dict:
    locus = record["locus"]
    digital = [
        {"siglum": witness["siglum"], "reading": witness["reading"], "uri": witness["uri"]}
        for witness in record["witnesses"]
        if "SCAN" not in witness["siglum"].upper()
    ]
    return {
        "id": f"PM1-ANOM-{record['id']}",
        "category": "digital-witness-error",
        "pm_locus": {
            "volume": locus["volume"],
            "printed_pages": [locus["printed_page"]],
            "scan_leaves": [locus["scan_leaf"]],
            "items": [record["item"]],
            "line_or_formula": locus.get("line_or_formula", ""),
        },
        "printed_reading": record["diplomatic_reading"],
        "printed_citations": [],
        "corrected_or_added_reading": record.get("other_reading", record["diplomatic_reading"]),
        "canonical_witness_evidence": canonical_witness(record),
        "digital_witnesses": digital,
        "affected_ast_items_batches": {
            "items": [record["item"]],
            "batches": [],
            "ast_effect": "None unless a separately reviewed item audit says otherwise.",
        },
        "strict_audit_status": "not-applicable: witness collation only",
        "minimal_relaxation": [],
        "lean_impact": {
            "kind": "canonical-source-preserved",
            "status": "no-PM-emendation",
        },
        "review_provenance": [f"metadata/apparatus/{record['_filename']}"],
        "resolution_status": "recorded-in-apparatus",
        "apparatus_id": record["id"],
        "linked_official_errata_ids": [],
    }


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build(root: Path = ROOT) -> dict:
    apparatus = root / APPARATUS.relative_to(ROOT)
    manual = root / MANUAL.relative_to(ROOT)
    errata = load_json(root / ERRATA.relative_to(ROOT))
    entries: list[dict] = []
    for path in sorted(apparatus.glob("*.json")):
        record = load_json(path)
        if record.get("classification") == "digital-witness-error":
            record["_filename"] = path.name
            entries.append(digital_entry(record))
    for path in sorted(manual.glob("*.json")):
        entries.extend(load_json(path)["entries"])
    entries.sort(key=lambda entry: entry["id"])
    return {
        "schema_version": 1,
        "id": "PM1-ANOMALY-REGISTER",
        "official_errata_registry": {
            "id": errata["id"],
            "path": "metadata/errata/PM1-1910-errata.json",
            "entry_ids": [entry["id"] for entry in errata["entries"]],
            "policy": "Official Errata are linked here and never duplicated as anomaly entries.",
        },
        "entries": entries,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = build()
    rendered = json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != rendered:
            raise SystemExit("anomaly registry is stale; run generate_anomaly_registry.py")
        print(f"anomaly registry is current ({len(payload['entries'])} entries)")
        return
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(rendered, encoding="utf-8")
    print(f"generated {OUTPUT.relative_to(ROOT)} ({len(payload['entries'])} entries)")


if __name__ == "__main__":
    main()
