#!/usr/bin/env python3
"""Promote homogeneous awaiting-CI catalogues using immutable green evidence.

This intentionally performs no network lookup.  The caller must first verify
that the supplied run is successful for the exact supplied commit (the
campaign CI wrapper does that).  ``--check`` previews the deterministic set;
``--write`` performs the metadata transition atomically per JSON file.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SHA = re.compile(r"[0-9a-f]{40}")
RUN = re.compile(r"https://github\.com/[^/]+/[^/]+/actions/runs/[0-9]+")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--commit", required=True)
    parser.add_argument("--run", required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    if args.check == args.write:
        parser.error("select exactly one of --check or --write")
    if not SHA.fullmatch(args.commit) or not RUN.fullmatch(args.run):
        parser.error("immutable 40-hex commit and GitHub Actions run URL required")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if head != args.commit:
        raise SystemExit(f"evidence commit {args.commit} is not checked-out HEAD {head}")

    files: list[Path] = []
    item_count = 0
    for path in sorted((ROOT / "metadata" / "items").glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        items = data.get("items", [])
        if not items or {item.get("formal_status") for item in items} != {"awaiting-ci"}:
            continue
        evidence = data.get("ci_evidence", {})
        if {evidence.get("commit"), evidence.get("run"), evidence.get("conclusion")} != {"pending"}:
            raise SystemExit(f"non-pending evidence in awaiting batch: {path}")
        files.append(path)
        item_count += len(items)
        if args.write:
            for item in items:
                item["formal_status"] = "kernel-checked"
                item["integration_status"] = "canonical-kernel-checked"
                if "integration_blocked" in item:
                    item["integration_blocked"] = False
            data["ci_evidence"] = {
                "commit": args.commit,
                "run": args.run,
                "conclusion": "success",
            }
            path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"{'promoted' if args.write else 'would promote'} {item_count} items in {len(files)} catalogues")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
