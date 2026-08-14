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
REQUIRED_FORMALIZATION_LEVEL = "pm-derivation-v1"


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
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", args.commit, "HEAD"], cwd=ROOT
    )
    if ancestry.returncode:
        raise SystemExit(f"evidence commit {args.commit} is not an ancestor of HEAD")

    snapshot_paths = subprocess.check_output(
        ["git", "grep", "-l", '"formal_status": "awaiting-ci"', args.commit, "--", "metadata/items"],
        cwd=ROOT,
        text=True,
    ).splitlines()
    eligible: set[str] = set()
    for tagged_path in snapshot_paths:
        path = tagged_path.split(":", 1)[1]
        raw = subprocess.check_output(["git", "show", f"{args.commit}:{path}"], cwd=ROOT, text=True)
        data = json.loads(raw)
        eligible.update(
            item["id"] for item in data.get("items", [])
            if item.get("formal_status") == "awaiting-ci"
        )

    files: list[Path] = []
    item_count = 0
    for path in sorted((ROOT / "metadata" / "items").glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        items = data.get("items", [])
        selected = [item for item in items if item.get("id") in eligible]
        if not selected:
            continue
        if len(selected) != len(items) or {item.get("formal_status") for item in items} != {"awaiting-ci"}:
            raise SystemExit(f"evidence batch changed membership/status and must be split first: {path}")
        weak = [
            item["id"] for item in selected
            if item.get("formalization_level") != REQUIRED_FORMALIZATION_LEVEL
        ]
        if weak:
            raise SystemExit(
                "refusing to promote semantic translations as PM proofs; "
                f"missing formalization_level={REQUIRED_FORMALIZATION_LEVEL}: "
                + ", ".join(weak)
            )
        evidence = data.get("ci_evidence", {})
        if {evidence.get("commit"), evidence.get("run"), evidence.get("conclusion")} != {"pending"}:
            raise SystemExit(f"non-pending evidence in awaiting batch: {path}")
        files.append(path)
        item_count += len(selected)
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
