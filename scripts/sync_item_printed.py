#!/usr/bin/env python3
"""Synchronize derivable item readings from canonical PM-VERBATIM blocks.

The source block is authoritative.  By default this command is a read-only CI
check.  ``--write`` repairs only stale ``printed`` fields; it never creates
source text, changes proof status, or promotes an item.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BLOCK = re.compile(
    r"PM-VERBATIM-BEGIN\s+(\S+)\n(.*?)\nPM-VERBATIM-END\s+(\S+)",
    re.DOTALL,
)


def canonical_readings() -> dict[str, str]:
    readings: dict[str, str] = {}
    for path in sorted((ROOT / "Principia").rglob("*.lean")):
        for begin, body, end in BLOCK.findall(path.read_text(encoding="utf-8")):
            if begin != end:
                raise SystemExit(f"mismatched PM-VERBATIM block {begin}/{end}: {path}")
            if begin in readings:
                raise SystemExit(f"duplicate PM-VERBATIM block: {begin}")
            readings[begin] = " ".join(body.split())
    return readings


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="read-only check (the default)")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    if args.check and args.write:
        parser.error("--check and --write are mutually exclusive")
    readings = canonical_readings()
    stale: list[str] = []
    for path in sorted((ROOT / "metadata" / "items").glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        changed = False
        for item in data.get("items", []):
            item_id = item.get("id")
            canonical = readings.get(item_id)
            if canonical is None:
                continue
            current = " ".join(item.get("printed", "").split())
            if current and current in canonical:
                continue
            stale.append(item_id)
            if args.write:
                item["printed"] = canonical
                changed = True
        if changed:
            path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if stale and not args.write:
        print("stale printed fields: " + ", ".join(stale))
        return 1
    action = "synchronized" if args.write else "checked"
    print(f"{action} {len(readings)} canonical readings; stale={len(stale)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
