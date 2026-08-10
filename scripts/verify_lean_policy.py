#!/usr/bin/env python3
"""Reject proof escape hatches in Lean code while ignoring historical prose."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(
    r"\b(sorry|admit)\b|(?:^|\n)\s*(axiom|constant)\b|\bunsafe\s+(def|theorem)\b"
)


def code_without_comments_or_strings(source: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end < 0:
                result.extend(" " * (len(source) - index))
                break
            result.extend(" " * (end - index))
            index = end
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def main() -> None:
    failed = False
    paths = [ROOT / "Principia.lean", *sorted((ROOT / "Principia").rglob("*.lean"))]
    for path in paths:
        code = code_without_comments_or_strings(path.read_text(encoding="utf-8"))
        for match in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            print(f"forbidden Lean declaration '{match.group(0)}' at {path}:{line}", file=sys.stderr)
            failed = True
    if failed:
        raise SystemExit(1)
    print("Lean source policy checks passed")


if __name__ == "__main__":
    main()
