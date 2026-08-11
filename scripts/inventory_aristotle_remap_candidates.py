#!/usr/bin/env python3
"""Inventory Q228--Q251 archives before attempting an interface remap.

An audit hash is not an archive.  This small read-only gate prevents the
remapper from treating a historical audit record as a locally available Lean
artifact.  It deliberately makes no Aristotle, Lean, CI, or promotion call.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
FIRST = 228
LAST = 251
ARCHIVE_NAME = re.compile(r"^(Q\d+)(?:[-].*)?\.tar\.gz$")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def audit_records(root: Path) -> dict[str, dict[str, Any]]:
    records: dict[str, dict[str, Any]] = {}
    for relative, key in (
        ("reviews/Q228-Q244-aristotle-archive-audit.json", "archives"),
        ("reviews/Q235-Q251-kernel-link-audit.json", "batches"),
    ):
        path = root / relative
        if not path.is_file():
            continue
        payload = json.loads(path.read_text(encoding="utf-8"))
        for record in payload.get(key, []):
            batch = record.get("batch")
            if isinstance(batch, str) and re.fullmatch(r"Q\d+", batch):
                previous = records.get(batch, {})
                # The kernel-link audit is a later, more specific statement;
                # retain the first audit fields as historical provenance.
                records[batch] = {**previous, **record}
    return records


def available_archives(root: Path) -> dict[str, list[dict[str, str]]]:
    found: dict[str, list[dict[str, str]]] = {}
    result_dir = root / "aristotle/results"
    if not result_dir.is_dir():
        return found
    for path in sorted(result_dir.glob("Q*.tar.gz")):
        match = ARCHIVE_NAME.fullmatch(path.name)
        if match is None:
            continue
        batch = match.group(1)
        found.setdefault(batch, []).append({
            "path": str(path.relative_to(root)),
            "sha256": sha256_file(path),
        })
    return found


def inventory(root: Path) -> dict[str, Any]:
    audits = audit_records(root)
    archives = available_archives(root)
    batches: list[dict[str, Any]] = []
    for number in range(FIRST, LAST + 1):
        batch = f"Q{number}"
        audit = audits.get(batch, {})
        expected = audit.get("archive_sha256", audit.get("sha256"))
        files = archives.get(batch, [])
        status: str
        reason: str
        if not files:
            if isinstance(expected, str):
                status = "blocked-archive-not-present"
                reason = "immutable archive hash is audited, but no matching local archive exists"
            else:
                status = "blocked-no-immutable-archive-audit"
                reason = audit.get("reason", "no immutable terminal archive is recorded")
        elif not isinstance(expected, str):
            status = "blocked-archive-has-no-audited-hash"
            reason = "local archive exists but audit supplies no immutable SHA-256"
        elif any(file["sha256"] == expected for file in files):
            status = "available-hash-matched"
            reason = audit.get("reason", audit.get("integration", "requires 1:1 remap"))
        else:
            status = "blocked-archive-hash-mismatch"
            reason = "no local archive digest matches the audited immutable SHA-256"
        link_status = audit.get("status", audit.get("link_status"))
        mapping_possible = status == "available-hash-matched" and link_status in {"linkable", "pending-remap"}
        batches.append({
            "batch": batch,
            "status": status,
            "reason": reason,
            "audited_archive_sha256": expected,
            "audit_status": link_status,
            "available_archives": files,
            "interface_mapping_possible": mapping_possible,
        })
    candidates = [record for record in batches if record["interface_mapping_possible"]]
    blockers = [record for record in batches if record["status"].startswith("blocked")]
    return {
        "kind": "pm-aristotle-interface-remap-availability",
        "scope": "Q228-Q251",
        "policy": {
            "read_only": True,
            "canonical_integration_forbidden": True,
            "no_local_lean_or_ci_was_run": True,
        },
        "batches": batches,
        "first_transplant_candidate": candidates[0]["batch"] if candidates else None,
        "first_exact_blocker": blockers[0] if blockers else None,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    options = parser.parse_args()
    report = inventory(ROOT)
    rendered = json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if options.report:
        options.report.parent.mkdir(parents=True, exist_ok=True)
        options.report.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    if report["first_transplant_candidate"] is None:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
