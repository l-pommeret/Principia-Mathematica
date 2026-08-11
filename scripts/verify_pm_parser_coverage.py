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
}


class ParserCoverageError(ValueError):
    pass


def audit(root: Path = ROOT) -> dict:
    parsed = []
    metalinguistic = []
    architecture_gated = []
    for item in load_items(root):
        identifier = item["id"]
        if str(item.get("integration_status", "")).startswith("blocked-architecture"):
            architecture_gated.append(identifier)
            continue
        if item["kind"] in METALINGUISTIC_KINDS:
            metalinguistic.append(identifier)
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
        "counts": {
            "object_language": len(parsed),
            "metalinguistic_rules": len(metalinguistic),
            "architecture_gated": len(architecture_gated),
            "total": len(parsed) + len(metalinguistic) + len(architecture_gated),
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
