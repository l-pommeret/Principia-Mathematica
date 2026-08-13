#!/usr/bin/env python3
"""Repository-level checks for the source-critical PM edition."""

from __future__ import annotations

import hashlib
import json
import re
import sys
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BEGIN = re.compile(r"PM-VERBATIM-BEGIN\s+(\S+)")
END = re.compile(r"PM-VERBATIM-END\s+(\S+)")
EXCERPT_BEGIN = re.compile(r"PM-SOURCE-EXCERPT-BEGIN\s+(\S+)")
EXCERPT_END = re.compile(r"PM-SOURCE-EXCERPT-END\s+(\S+)")


class EditorialError(ValueError):
    pass


def fail(message: str) -> None:
    raise EditorialError(message)


def check_verbatim_blocks() -> None:
    seen: dict[str, Path] = {}
    for path in sorted((ROOT / "Principia").rglob("*.lean")):
        stack: list[str] = []
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if match := BEGIN.search(line):
                item = match.group(1)
                if stack:
                    fail(f"nested PM-VERBATIM block at {path}:{number}")
                if item in seen:
                    fail(f"duplicate PM-VERBATIM ID {item} in {seen[item]} and {path}")
                seen[item] = path
                stack.append(item)
            if "[sic]" in line and stack:
                fail(f"[sic] alters canonical verbatim bytes at {path}:{number}; use apparatus")
            if match := END.search(line):
                item = match.group(1)
                if not stack or stack.pop() != item:
                    fail(f"unmatched PM-VERBATIM end {item} at {path}:{number}")
        if stack:
            fail(f"unclosed PM-VERBATIM block {stack[-1]} in {path}")
    if not seen:
        fail("no PM-VERBATIM blocks found")


def check_suspicious_diplomatic_unicode() -> None:
    """Reject known OCR/transcription artefacts inside diplomatic blocks.

    A combining diaeresis was previously used as an ad-hoc stand-in for PM's
    breve/converse and relational-image marks (for example ``P̈``).  It is not
    part of the project's diplomatic alphabet and silently reverses meaning.
    """
    suspicious = re.compile(r"[A-Za-zΑ-ω]\u0308")
    for item_id, body in collect_verbatim().items():
        if match := suspicious.search(body):
            token = match.group(0)
            fail(f"suspicious combining-diaeresis token {token!r} in {item_id}")


def collect_verbatim() -> dict[str, str]:
    blocks: dict[str, str] = {}
    pattern = re.compile(
        r"PM-VERBATIM-BEGIN\s+(\S+)\n(.*?)\nPM-VERBATIM-END\s+(\S+)",
        re.DOTALL,
    )
    for path in sorted((ROOT / "Principia").rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        for match in pattern.finditer(source):
            begin, body, end = match.groups()
            if begin != end:
                fail(f"verbatim ID mismatch {begin}/{end} in {path}")
            blocks[begin] = body
    return blocks


def check_excerpt_blocks() -> None:
    for path in sorted((ROOT / "Principia").rglob("*.lean")):
        stack: list[str] = []
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if match := EXCERPT_BEGIN.search(line):
                if stack:
                    fail(f"nested PM-SOURCE-EXCERPT block at {path}:{number}")
                stack.append(match.group(1))
            if match := EXCERPT_END.search(line):
                item = match.group(1)
                if not stack or stack.pop() != item:
                    fail(f"unmatched PM-SOURCE-EXCERPT end {item} at {path}:{number}")
        if stack:
            fail(f"unclosed PM-SOURCE-EXCERPT block {stack[-1]} in {path}")


def check_apparatus() -> None:
    required = {
        "id", "item", "locus", "classification", "diplomatic_reading",
        "witnesses", "evidence", "status", "review",
    }
    identifiers: set[str] = set()
    for path in sorted((ROOT / "metadata" / "apparatus").glob("*.json")):
        try:
            record = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            fail(f"invalid apparatus JSON {path}: {error}")
        missing = required - record.keys()
        if missing:
            fail(f"{path} lacks required fields: {sorted(missing)}")
        if record["id"] in identifiers:
            fail(f"duplicate apparatus ID {record['id']}")
        identifiers.add(record["id"])
        witnesses = record["witnesses"]
        if not isinstance(witnesses, list) or not witnesses:
            fail(f"{path} must cite at least one witness")
        for witness in witnesses:
            if not {"siglum", "reading", "uri"} <= witness.keys():
                fail(f"incomplete witness in {path}")
        classification = record["classification"]
        marker = record.get("marker")
        if classification == "authorial-print-sic" and marker != "sic":
            fail(f"confirmed printed error in {path} must carry marker 'sic'")
        if classification == "digital-witness-error" and marker == "sic":
            fail(f"digital witness error in {path} must not attribute sic to PM")


def check_item_metadata() -> None:
    blocks = collect_verbatim()
    metadata_ids: set[str] = set()
    required_item_fields = {
        "id", "kind", "printed", "lean_path", "declaration", "formal_scope",
        "source_status", "formal_status",
    }
    for path in sorted((ROOT / "metadata" / "items").glob("*.json")):
        try:
            batch = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            fail(f"invalid item metadata JSON {path}: {error}")
        items = batch.get("items")
        if not isinstance(items, list) or not items:
            fail(f"{path} must contain a nonempty items array")
        if len(items) > 5:
            fail(f"{path} exceeds the campaign batch cap of five items")
        for item in items:
            missing_fields = required_item_fields - item.keys()
            if missing_fields:
                fail(
                    f"{path} item {item.get('id')!r} lacks required fields: "
                    f"{sorted(missing_fields)}"
                )
            item_id = item.get("id")
            if not item_id or item_id in metadata_ids:
                fail(f"missing or duplicate item ID {item_id!r} in {path}")
            metadata_ids.add(item_id)
            if item_id not in blocks:
                fail(f"metadata item {item_id} has no PM-VERBATIM block")
            printed = " ".join(item.get("printed", "").split())
            verbatim = " ".join(blocks[item_id].split())
            if printed not in verbatim:
                fail(f"printed reading for {item_id} does not occur in its verbatim block")
            lean_path = ROOT / item.get("lean_path", "")
            if not lean_path.is_file():
                fail(f"Lean path for {item_id} does not exist: {lean_path}")
        formal_statuses = {item.get("formal_status") for item in items}
        evidence = batch.get("ci_evidence", {})
        evidence_values = {
            evidence.get("commit"), evidence.get("run"), evidence.get("conclusion")
        }
        if formal_statuses in ({"prepared"}, {"awaiting-ci"}):
            if evidence_values != {"pending"}:
                fail(
                    f"{path} prepared/awaiting-ci batch must have entirely pending "
                    "CI evidence"
                )
        elif formal_statuses == {"kernel-checked"}:
            if "pending" in evidence_values:
                fail(f"{path} mixes pending and successful CI evidence")
            if evidence.get("conclusion") != "success" or not evidence.get("run"):
                fail(f"{path} lacks successful immutable CI evidence")
        else:
            fail(
                f"{path} must contain only prepared items, only awaiting-ci "
                "items, or only kernel-checked items"
            )
    numbered = {item_id for item_id in blocks if "✱" in item_id}
    missing = numbered - metadata_ids
    if missing:
        fail(f"numbered verbatim items lack metadata: {sorted(missing)}")


def check_source_block_metadata() -> None:
    blocks = collect_verbatim()
    required = {
        "id", "edition", "volume", "kind", "title", "source_range",
        "lean_path", "witnesses", "source_status", "critical_status",
        "transcription", "canonical_body", "review",
    }
    identifiers: set[str] = set()
    directory = ROOT / "metadata" / "source_blocks"
    for path in sorted(directory.glob("*.json")):
        try:
            record = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            fail(f"invalid source-block JSON {path}: {error}")
        missing = required - record.keys()
        if missing:
            fail(f"{path} lacks required fields: {sorted(missing)}")
        item_id = record["id"]
        if item_id in identifiers:
            fail(f"duplicate source-block ID {item_id}")
        identifiers.add(item_id)
        if item_id not in blocks:
            fail(f"source-block metadata {item_id} has no PM-VERBATIM block")
        lean_path = ROOT / record["lean_path"]
        if not lean_path.is_file():
            fail(f"Lean path for source block {item_id} does not exist: {lean_path}")
        witnesses = record["witnesses"]
        if not isinstance(witnesses, list) or not witnesses:
            fail(f"{path} must cite at least one witness")
        if sum(witness.get("role") == "canonical" for witness in witnesses) != 1:
            fail(f"{path} must identify exactly one canonical witness")
        for witness in witnesses:
            if not {"siglum", "role", "uri"} <= witness.keys():
                fail(f"incomplete witness in {path}")
        body = blocks[item_id].encode("utf-8")
        canonical = record["canonical_body"]
        expected_length = canonical.get("byte_length")
        expected_hash = canonical.get("sha256")
        if expected_length != len(body):
            fail(
                f"canonical byte length for {item_id} is {expected_length}, "
                f"not {len(body)}"
            )
        actual_hash = hashlib.sha256(body).hexdigest()
        if expected_hash != actual_hash:
            fail(
                f"canonical SHA-256 for {item_id} is {expected_hash}, "
                f"not {actual_hash}"
            )
        review = record["review"]
        if record["critical_status"] == "no-authorial-print-error-detected":
            if review.get("apparatus_required") or review.get("sic_required"):
                fail(f"{path} contradicts its no-error critical status")


def report_all() -> list[str]:
    """Collect one deterministic failure from each independent editorial gate."""
    errors = []
    for check in (
        check_verbatim_blocks,
        check_suspicious_diplomatic_unicode,
        check_excerpt_blocks,
        check_apparatus,
        check_item_metadata,
        check_source_block_metadata,
    ):
        try:
            check()
        except EditorialError as error:
            errors.append(f"{check.__name__}: {error}")
    return errors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report-all", action="store_true")
    options = parser.parse_args()
    if options.report_all:
        errors = report_all()
        if errors:
            print("\n".join(f"editorial error: {error}" for error in errors), file=sys.stderr)
            raise SystemExit(1)
        print("editorial checks passed")
        return
    try:
        check_verbatim_blocks()
        check_suspicious_diplomatic_unicode()
        check_excerpt_blocks()
        check_apparatus()
        check_item_metadata()
        check_source_block_metadata()
    except EditorialError as error:
        print(f"editorial error: {error}", file=sys.stderr)
        raise SystemExit(1)
    print("editorial checks passed")


if __name__ == "__main__":
    main()
