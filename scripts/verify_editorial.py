#!/usr/bin/env python3
"""Repository-level checks for the source-critical PM edition."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BEGIN = re.compile(r"PM-VERBATIM-BEGIN\s+(\S+)")
END = re.compile(r"PM-VERBATIM-END\s+(\S+)")
EXCERPT_BEGIN = re.compile(r"PM-SOURCE-EXCERPT-BEGIN\s+(\S+)")
EXCERPT_END = re.compile(r"PM-SOURCE-EXCERPT-END\s+(\S+)")


def fail(message: str) -> None:
    print(f"editorial error: {message}", file=sys.stderr)
    raise SystemExit(1)


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
        if formal_statuses == {"awaiting-ci"}:
            if evidence_values != {"pending"}:
                fail(
                    f"{path} awaiting-ci batch must have entirely pending "
                    "CI evidence"
                )
        elif formal_statuses == {"kernel-checked"}:
            if "pending" in evidence_values:
                fail(f"{path} mixes pending and successful CI evidence")
            if evidence.get("conclusion") != "success" or not evidence.get("run"):
                fail(f"{path} lacks successful immutable CI evidence")
        else:
            fail(
                f"{path} must contain only awaiting-ci items or only "
                "kernel-checked items"
            )
    numbered = {item_id for item_id in blocks if "✱" in item_id}
    missing = numbered - metadata_ids
    if missing:
        fail(f"numbered verbatim items lack metadata: {sorted(missing)}")


def main() -> None:
    check_verbatim_blocks()
    check_excerpt_blocks()
    check_apparatus()
    check_item_metadata()
    print("editorial checks passed")


if __name__ == "__main__":
    main()
