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


def main() -> None:
    check_verbatim_blocks()
    check_apparatus()
    print("editorial checks passed")


if __name__ == "__main__":
    main()

