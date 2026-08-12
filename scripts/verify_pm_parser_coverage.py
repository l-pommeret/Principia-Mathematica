#!/usr/bin/env python3
"""Require every catalogued formal PM item to have a deliberate parser route."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

from pm_syntax import parse_statement
from verify_dependencies import load_items


ROOT = Path(__file__).resolve().parents[1]
METALINGUISTIC_KINDS = {
    "derived-metalinguistic-rule",
    "primitive-inference-rule",
    "primitive-function-inference-rule",
    "primitive-formation-rule",
    "type-proposition",
    "function-existence",
}


class ParserCoverageError(ValueError):
    pass


def audit(root: Path = ROOT) -> dict:
    parsed = []
    metalinguistic = []
    architecture_gated = []
    reviewed_parser_gaps = []
    for item in load_items(root):
        identifier = item["id"]
        if str(item.get("integration_status", "")).startswith("blocked-architecture"):
            architecture_gated.append(identifier)
            continue
        if item["kind"] in METALINGUISTIC_KINDS:
            metalinguistic.append(identifier)
            continue
        if item.get("parser_status") == "reviewed-gap":
            evidence = root / str(item.get("parser_evidence", ""))
            if not evidence.is_file() or not str(item.get("parser_evidence", "")).startswith("reviews/"):
                raise ParserCoverageError(f"{identifier}: reviewed parser gap lacks review evidence")
            reviewed_parser_gaps.append(identifier)
            continue
        try:
            ast = parse_statement(item["printed"])
        except ValueError as error:
            raise ParserCoverageError(f"{identifier}: {error}") from error
        canonical = json.dumps(
            ast.to_dict(), ensure_ascii=False, sort_keys=True, separators=(",", ":")
        )
        parsed.append({
            "id": identifier,
            "ast_sha256": hashlib.sha256(canonical.encode("utf-8")).hexdigest(),
        })
    if not parsed:
        raise ParserCoverageError("no object-language statements parsed")
    return {
        "kind": "pm-parser-coverage-audit",
        "object_language": parsed,
        "metalinguistic_rules": sorted(metalinguistic),
        "architecture_gated": sorted(architecture_gated),
        "reviewed_parser_gaps": sorted(reviewed_parser_gaps),
        "counts": {
            "object_language": len(parsed),
            "metalinguistic_rules": len(metalinguistic),
            "architecture_gated": len(architecture_gated),
            "reviewed_parser_gaps": len(reviewed_parser_gaps),
            "total": len(parsed) + len(metalinguistic) + len(architecture_gated) + len(reviewed_parser_gaps),
        },
    }


def main() -> None:
    try:
        result = audit()
    except (ParserCoverageError, OSError, json.JSONDecodeError) as error:
        print(f"PM parser coverage error: {error}", file=sys.stderr)
        raise SystemExit(1)
    counts = result["counts"]
    print(
        "PM parser coverage passed "
        f"({counts['object_language']} object statements, "
        f"{counts['metalinguistic_rules']} metalinguistic rules, "
        f"{counts['architecture_gated']} architecture-gated)"
    )


if __name__ == "__main__":
    main()
