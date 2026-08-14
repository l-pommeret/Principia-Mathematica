#!/usr/bin/env python3
"""What must be derived next, and what is blocked until it is.

*Principia Mathematica* is one dependency chain, not a collection of chapters.
Its whole apparatus rests on 23 printed primitive propositions, all in ✱1, ✱9,
✱10, ✱11 and ✱12; every other proposition is derived from those through the
demonstrations PM prints.  So a chapter cannot be reconstructed before the
propositions its demonstrations cite exist — and the useful question is never
"which chapter next" but "which propositions unblock the most work".

This report answers that.  It is descriptive: it never fails, and it changes
nothing.  Use it to choose the next wave of work.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pm_lean_index import ROOT, declarations, import_closure  # noqa: E402

ITEMS = ROOT / "metadata" / "items"


def load() -> dict[str, dict]:
    items: dict[str, dict] = {}
    for path in sorted(ITEMS.glob("*.json")):
        batch = json.loads(path.read_text(encoding="utf-8"))
        for item in batch.get("items", []):
            if isinstance(item.get("id"), str):
                items[item["id"]] = item
    if not items:
        raise SystemExit(f"no catalogue items under {ITEMS}")
    return items


def formalised(items: dict[str, dict]) -> set[str]:
    """Items whose declaration exists in a module the kernel compiles."""
    done: set[str] = set()
    closure = import_closure()
    for identifier, item in items.items():
        path = item.get("lean_path")
        base = (item.get("declaration") or "").rsplit(".", 1)[-1]
        if path and path in closure and base and declarations(path).get(base):
            done.add(identifier)
    return done


def star_of(identifier: str) -> str:
    return identifier.split("·")[0]


def frontier(items: dict[str, dict], done: set[str]):
    """Cited-but-unformalised propositions, and who waits on them."""
    blocked_by: dict[str, set[str]] = defaultdict(set)
    for identifier, item in items.items():
        for dependency in item.get("printed_dependencies") or []:
            if not isinstance(dependency, str) or dependency not in items:
                continue
            if dependency not in done:
                blocked_by[dependency].add(identifier)
    return blocked_by


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--star", help="restrict to one star, e.g. PM1:✱4")
    parser.add_argument("--json", type=Path)
    arguments = parser.parse_args()

    items = load()
    done = formalised(items)
    blocked_by = frontier(items, done)
    waiting = set().union(*blocked_by.values()) if blocked_by else set()

    print(f"catalogue items                     : {len(items)}")
    print(f"with a compiled Lean declaration    : {len(done)}")
    print(f"cited but never formalised          : {len(blocked_by)}")
    print(f"items waiting on at least one       : {len(waiting)}")

    ranked = sorted(
        blocked_by.items(), key=lambda entry: (-len(entry[1]), entry[0])
    )
    if arguments.star:
        ranked = [e for e in ranked if star_of(e[0]) == arguments.star]

    print(f"\nmost blocking propositions (top {arguments.top}):")
    for identifier, dependents in ranked[: arguments.top]:
        item = items[identifier]
        print(
            f"  {len(dependents):4} waiting  {identifier:16} "
            f"{item.get('kind', '?'):22} {item.get('lean_path', '(no path)')}"
        )

    by_star = Counter(star_of(identifier) for identifier in blocked_by)
    print("\nfrontier by star (where the work is):")
    for star, count in by_star.most_common(20):
        print(f"  {count:4}  {star}")

    if arguments.json:
        arguments.json.write_text(
            json.dumps(
                {
                    identifier: {
                        "kind": items[identifier].get("kind"),
                        "lean_path": items[identifier].get("lean_path"),
                        "declaration": items[identifier].get("declaration"),
                        "printed": items[identifier].get("printed"),
                        "blocks": sorted(dependents),
                    }
                    for identifier, dependents in ranked
                },
                ensure_ascii=False,
                indent=1,
            ),
            encoding="utf-8",
        )
        print(f"\nwritten to {arguments.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
