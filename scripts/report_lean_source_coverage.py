#!/usr/bin/env python3
"""Conservative source-to-Lean coverage report for numbered PM items.

This report deliberately does not equate every ``star_*`` declaration with a
proved PM proposition.  It separates nominal mappings from declarations whose
body is an obvious alias, reflexivity proof, or premise pass-through.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "Principia"

SOURCE_ID = re.compile(r"✱\s*(\d+)·([0-9]+)")
VERBATIM_ID = re.compile(r"PM-VERBATIM-BEGIN\s+(PM\d+:✱?\d+·\d+)")
DECL = re.compile(
    r"(?ms)^\s*(theorem|def|abbrev)\s+star_(\d+)_([0-9]+)\b(.*?)(?=^\s*(?:theorem|def|abbrev|namespace|end)\b|\Z)"
)
DIRECT = re.compile(
    r"(?s):=\s*(?:by\s+)?(?:rfl|Iff\.rfl|[A-Za-z_][A-Za-z0-9_.]*|fun\s+\w+\s*=>\s*\w+)\s*$"
)
STAR_CALL = re.compile(r":=\s*(?:@?[A-Za-z0-9_.]*star_\d+_\d+\b)")


def source_ids() -> dict[tuple[str, str], set[Path]]:
    found: dict[tuple[str, str], set[Path]] = defaultdict(set)
    for path in LEAN_ROOT.rglob("*.lean"):
        text = path.read_text(encoding="utf-8", errors="ignore")
        if "Source" not in path.name and "PM-VERBATIM" not in text:
            continue
        for star, item in SOURCE_ID.findall(text):
            found[(star, item)].add(path.relative_to(ROOT))
    return found


def declarations() -> dict[tuple[str, str], list[tuple[Path, str, str]]]:
    found: dict[tuple[str, str], list[tuple[Path, str, str]]] = defaultdict(list)
    for path in LEAN_ROOT.rglob("*.lean"):
        if "Source" in path.name or "Targets" in path.name:
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        for kind, star, item, body in DECL.findall(text):
            found[(star, item)].append((path.relative_to(ROOT), kind, body.strip()))
    return found


def editorial_metadata_counts() -> tuple[int, int, int, int]:
    """Return numbered blocks, catalogued blocks, and uncatalogued blocks."""
    blocks: set[str] = set()
    for path in LEAN_ROOT.rglob("*.lean"):
        blocks.update(VERBATIM_ID.findall(path.read_text(encoding="utf-8", errors="ignore")))
    metadata_ids: set[str] = set()
    kernel_checked_ids: set[str] = set()
    for path in (ROOT / "metadata" / "items").glob("*.json"):
        payload = json.loads(path.read_text(encoding="utf-8"))
        for item in payload.get("items", []):
            if isinstance(item, dict) and isinstance(item.get("id"), str):
                metadata_ids.add(item["id"])
                if item.get("formal_status") == "kernel-checked":
                    kernel_checked_ids.add(item["id"])
    catalogued = len(blocks & metadata_ids)
    return len(blocks), catalogued, len(blocks - metadata_ids), len(kernel_checked_ids)


def is_alias(kind: str, body: str) -> bool:
    if kind != "theorem":
        return True
    return bool(DIRECT.search(body) or STAR_CALL.search(body))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument("--details", type=Path, help="write per-ID TSV audit details")
    parser.add_argument(
        "--verify-pipeline",
        action="store_true",
        help="fail unless pipeline.json records the current coverage counters",
    )
    args = parser.parse_args()
    sources = source_ids()
    decls = declarations()
    mapped = sources.keys() & decls.keys()
    unmapped = sources.keys() - decls.keys()
    duplicate = {key for key in mapped if len(decls[key]) > 1}
    alias_only = {
        key for key in mapped if all(is_alias(kind, body) for _, kind, body in decls[key])
    }
    strict_candidates = mapped - alias_only - duplicate
    numbered_blocks, catalogued_blocks, missing_metadata, kernel_checked = editorial_metadata_counts()

    report = {
        "locally_transcribed_source_ids": len(sources),
        "nominally_mapped_ids": len(mapped),
        "unmapped_ids": len(unmapped),
        "duplicate_declaration_ids": len(duplicate),
        "alias_or_pass_through_only_ids": len(alias_only),
        "strict_proof_candidates": len(strict_candidates),
        "numbered_verbatim_blocks": numbered_blocks,
        "numbered_blocks_with_item_metadata": catalogued_blocks,
        "numbered_blocks_missing_item_metadata": missing_metadata,
        "kernel_checked_editorial_ids": kernel_checked,
        "kernel_checked_all_pm_percent": round(100 * kernel_checked / 9845, 2),
        "nominal_local_corpus_percent": round(100 * len(mapped) / len(sources), 2),
        "strict_candidate_local_corpus_percent": round(
            100 * len(strict_candidates) / len(sources), 2
        ),
        "notes": [
            "the denominator is the locally transcribed corpus, not all 9845 PM items",
            "strict candidates require item-level semantic audit; this is not a proof claim",
        ],
    }
    if args.verify_pipeline:
        pipeline = json.loads((ROOT / "pipeline.json").read_text(encoding="utf-8"))
        recorded = pipeline.get("lean_source_coverage")
        if not isinstance(recorded, dict):
            raise SystemExit("pipeline.json lacks lean_source_coverage")
        mismatches = {
            key: {"recorded": recorded.get(key), "actual": value}
            for key, value in report.items()
            if key != "notes" and recorded.get(key) != value
        }
        if mismatches:
            raise SystemExit(
                "pipeline.json coverage is stale: "
                + json.dumps(mismatches, sort_keys=True)
            )
    if args.details:
        lines = ["star\titem\tstatus\tsource_paths\tdeclaration_paths"]
        for key in sorted(sources, key=lambda value: (int(value[0]), int(value[1]))):
            status = (
                "unmapped" if key in unmapped else
                "duplicate" if key in duplicate else
                "alias-only" if key in alias_only else
                "strict-candidate"
            )
            src = ",".join(map(str, sorted(sources[key])))
            dec = ",".join(str(row[0]) for row in decls.get(key, []))
            lines.append(f"{key[0]}\t{key[1]}\t{status}\t{src}\t{dec}")
        args.details.write_text("\n".join(lines) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for key, value in report.items():
            if key != "notes":
                print(f"{key}={value}")
        for note in report["notes"]:
            print(f"note={note}")


if __name__ == "__main__":
    main()
