#!/usr/bin/env python3
"""Parse a printed PM demonstration into an ordered, non-proving skeleton."""

from __future__ import annotations

from dataclasses import dataclass
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load_alias_registry(path: Path = ROOT / "metadata/dependency_aliases.json") -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    return {
        "aliases": payload["aliases"],
        "historical_scopes": payload.get("historical_scopes", {}),
    }


ALIAS_REGISTRY = load_alias_registry()
PRINTED_ALIASES = ALIAS_REGISTRY["aliases"]

REFERENCE = re.compile(r"✱([0-9]+)·([0-9]+(?:·[0-9]+)*)")
LINE_REFERENCE = re.compile(r"\(([0-9]+)\)")
SUBSTITUTION = re.compile(r"[\[(]([^\]\n()]*?/[^\]\n()]*?)[\])]" )


def expand_reference(text: str, volume: int = 1) -> list[str]:
    match = REFERENCE.fullmatch(text)
    if match is None:
        raise ValueError(f"not a PM reference: {text!r}")
    number, suffixes = match.groups()
    return [f"PM{volume}:✱{number}·{suffix}" for suffix in suffixes.split("·")]


def item_order(item_id: str) -> tuple[int, int]:
    match = re.fullmatch(r"PM[0-9]+:✱([0-9]+)·([0-9]+)", item_id)
    if match is None:
        raise ValueError(f"invalid current PM item {item_id!r}")
    number, suffix = match.groups()
    # Preserve decimal ordering: ·3 < ·31 < ·311 < ·32.
    return int(number), int(suffix) * 10 ** (12 - len(suffix))


def alias_candidates(alias: str, current_item: str | None) -> tuple[list[str], str]:
    candidates = PRINTED_ALIASES[alias]
    scopes = ALIAS_REGISTRY["historical_scopes"].get(alias)
    if not scopes:
        return candidates, "exact" if len(candidates) == 1 else "form-family"
    if current_item is None:
        return candidates, "locus-required"
    current = item_order(current_item)
    matches = []
    for scope in scopes:
        after_start = "from" not in scope or current >= item_order(scope["from"])
        before_end = "before" not in scope or current < item_order(scope["before"])
        if after_start and before_end:
            matches.append(scope)
    if len(matches) != 1:
        raise ValueError(f"alias {alias} has no unique historical scope at {current_item}")
    return list(matches[0]["candidates"]), "historically-scoped-family"


def step_blocks(source: str) -> list[str]:
    blocks: list[list[str]] = []
    current: list[str] | None = None
    for line in source.splitlines():
        stripped = line.strip()
        if stripped.startswith("⊢"):
            if current:
                blocks.append(current)
            current = [stripped]
        elif current is not None and (stripped.startswith("[") or stripped.startswith("[(")):
            current.append(stripped)
        elif current is not None and stripped == "":
            blocks.append(current)
            current = None
    if current:
        blocks.append(current)
    rendered = ["\n".join(lines) for lines in blocks]
    if rendered:
        return rendered
    # Short demonstrations are often printed entirely in the reference
    # bracket following the proposition, without a separate `Dem.` block.
    return [f"⊢ . {match.group(1).strip()}"
            for match in re.finditer(r"\[([^\]]+)\]", source)]


def parse_step(block: str, volume: int = 1, current_item: str | None = None) -> dict:
    events: list[tuple[int, dict]] = []
    for match in REFERENCE.finditer(block):
        events.append((match.start(), {
            "kind": "printed-reference",
            "printed": match.group(0),
            "normalized_candidates": expand_reference(match.group(0), volume),
        }))
    for alias, resolutions in PRINTED_ALIASES.items():
        for match in re.finditer(rf"(?<![A-Za-z]){re.escape(alias)}(?![A-Za-z])", block):
            resolved, status = alias_candidates(alias, current_item)
            events.append((match.start(), {
                "kind": "printed-alias", "printed": alias,
                "normalized_candidates": resolved,
                "resolution_status": status,
            }))
    substitutions = [" ".join(match.group(1).split()) for match in SUBSTITUTION.finditer(block)]
    labels = list(LINE_REFERENCE.finditer(block))
    trailing = re.search(r"\(([0-9]+)\)\s*$", block)
    produced = trailing.group(1) if trailing else None
    used = [match.group(1) for match in labels
            if trailing is None or match.start() != trailing.start()]
    for match in labels:
        if trailing is not None and match.start() == trailing.start():
            continue
        events.append((match.start(), {
            "kind": "line-reference", "printed": f"({match.group(1)})",
            "line": match.group(1),
        }))
    return {
        "printed": block,
        "events": [event for _, event in sorted(events, key=lambda pair: pair[0])],
        "substitutions": substitutions,
        "uses_lines": used,
        "produces_line": produced,
    }


def parse_demonstration(source: str, volume: int = 1,
                        current_item: str | None = None) -> dict:
    blocks = step_blocks(source)
    return {
        "kind": "pm-demonstration-skeleton",
        "volume": volume,
        "current_item": current_item,
        "steps": [parse_step(block, volume, current_item) for block in blocks],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--volume", type=int, default=1)
    parser.add_argument("--item")
    options = parser.parse_args()
    result = parse_demonstration(
        options.source.read_text(encoding="utf-8"), options.volume, options.item
    )
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
