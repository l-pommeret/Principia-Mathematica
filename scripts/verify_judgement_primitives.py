#!/usr/bin/env python3
"""No constructor without a printed primitive proposition.

Criterion T3 asks whether a statement is a judgement of an inductive relation.
That is a check on *shape*, and shape alone is cheap to fake: an inductive
relation with one catch-all constructor makes every theorem a one-line
constructor application while satisfying T3, T5 and T6.

This gate checks the relations themselves.  ``PM.Derivation``
(``Principia/Deduction/System.lean``) is the reference: six constructors, one per
printed primitive proposition of ✱1, and nothing else.  A relation whose
constructors do not each answer to a printed primitive is an axiom set wearing
the costume of a calculus, and the propositions it "derives" are assumed.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pm_lean_index import (  # noqa: E402
    ROOT,
    import_closure,
    judgement_relations,
    source,
)

ITEMS = ROOT / "metadata" / "items"

#: Kinds a constructor may legitimately answer to.  A *definition* is not among
#: them: PM's ``Df`` are eliminable abbreviations, and turning one into a
#: constructor makes an abbreviation irreducible — an addition to the system
#: rather than a reconstruction of it.
PRIMITIVE_KINDS = frozenset({
    "primitive-proposition",
    "primitive-idea",
    "primitive-formation-rule",
    "primitive-inference-rule",
    "primitive-function-inference-rule",
})

#: Constructors that carry no PM number because they are syntax rather than
#: inference — the base cases of an intrinsically typed formation judgement, for
#: instance.  Such a constructor is legitimate, but it must be *declared*: an
#: undeclared one is indistinguishable from an assumption smuggled in, and
#: changing a relation's sort to move it out of this gate's view is evasion, not
#: a fix.  The registry is deliberately small and every entry carries a reason.
REGISTRY = ROOT / "metadata" / "judgement_constructors.json"

_CONSTRUCTOR = re.compile(r"(?m)^\s*\|\s*([A-Za-z_][A-Za-z0-9_'!]*)")
_STAR_NAME = re.compile(r"^star_(\d+)_(\d+)$")


def catalogue_kinds() -> dict[str, str]:
    """Map every PM id to its catalogued ``kind``."""
    kinds: dict[str, str] = {}
    for path in sorted(ITEMS.glob("*.json")):
        batch = json.loads(path.read_text(encoding="utf-8"))
        for item in batch.get("items", []):
            identifier = item.get("id")
            if isinstance(identifier, str):
                kinds[identifier] = item.get("kind", "")
    if not kinds:
        raise SystemExit(f"no catalogue items found under {ITEMS}")
    return kinds


def constructor_to_pm_ids(constructor: str) -> list[str]:
    """Candidate PM ids a constructor name could answer to.

    ``star_1_11`` is ambiguous between ✱1·11 and ✱1·1·1; PM numbering makes the
    first reading correct, and both spellings are offered so a catalogue that
    uses either is matched rather than spuriously failed.
    """
    match = _STAR_NAME.match(constructor)
    if not match:
        return []
    star, part = match.groups()
    return [f"PM1:✱{star}·{part}", f"PM2:✱{star}·{part}", f"PM3:✱{star}·{part}"]


def relation_constructors() -> dict[str, tuple[str, list[str]]]:
    """Map each judgement relation to ``(module, constructor names)``."""
    relations = judgement_relations()
    found: dict[str, tuple[str, list[str]]] = {}
    for module in sorted(import_closure()):
        text = source(module)
        for name in relations:
            match = re.search(
                r"(?m)^\s*inductive\s+" + re.escape(name) + r"\b", text
            )
            if not match:
                continue
            tail = text[match.end():]
            stop = re.search(
                r"(?m)^\s*(?:inductive|structure|def|theorem|lemma|abbrev|end|namespace)\b",
                tail,
            )
            body = tail[: stop.start()] if stop else tail
            found[name] = (module, _CONSTRUCTOR.findall(body))
    return found


def declared_exemptions() -> dict[tuple[str, str], str]:
    """Registered syntax-carrier constructors, keyed by (relation, constructor)."""
    if not REGISTRY.is_file():
        return {}
    data = json.loads(REGISTRY.read_text(encoding="utf-8"))
    exemptions: dict[tuple[str, str], str] = {}
    for entry in data.get("exemptions", []):
        relation = entry.get("relation")
        constructor = entry.get("constructor")
        reason = (entry.get("reason") or "").strip()
        if not relation or not constructor:
            raise SystemExit(f"{REGISTRY}: an exemption lacks relation/constructor")
        if len(reason) < 40:
            raise SystemExit(
                f"{REGISTRY}: {relation}.{constructor} has no substantive reason; "
                "an exemption without an argument from the printed text is an "
                "assumption in disguise"
            )
        exemptions[(relation, constructor)] = reason
    return exemptions


def audit() -> tuple[list[str], dict[str, int]]:
    kinds = catalogue_kinds()
    exemptions = declared_exemptions()
    problems: list[str] = []
    stats: dict[str, int] = defaultdict(int)

    for relation, (module, constructors) in sorted(relation_constructors().items()):
        stats["relations"] += 1
        if not constructors:
            problems.append(
                f"{module}: `{relation}` is a judgement relation with no "
                "constructors; it can never be inhabited, so every theorem over "
                "it is vacuously general"
            )
            continue
        for constructor in constructors:
            stats["constructors"] += 1
            if (relation, constructor) in exemptions:
                stats["declared-syntax-carriers"] += 1
                continue
            candidates = constructor_to_pm_ids(constructor)
            if not candidates:
                problems.append(
                    f"{module}: `{relation}.{constructor}` is not named for a "
                    "printed proposition (expected `star_<star>_<part>`); a "
                    "constructor invented for convenience is an assumption"
                )
                continue
            matched = [pm for pm in candidates if pm in kinds]
            if not matched:
                problems.append(
                    f"{module}: `{relation}.{constructor}` answers to no "
                    f"catalogued proposition (tried {', '.join(candidates)})"
                )
                continue
            kind = kinds[matched[0]]
            if kind not in PRIMITIVE_KINDS:
                problems.append(
                    f"{module}: `{relation}.{constructor}` asserts {matched[0]}, "
                    f"catalogued as `{kind}`, not a primitive proposition. "
                    + (
                        "PM's `Df` are eliminable abbreviations and must be "
                        "`def`s that unfold, never constructors."
                        if "definition" in kind
                        else "A derived proposition must be derived, not assumed."
                    )
                )
                continue
            stats["primitive-backed"] += 1
    return problems, dict(stats)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-all", action="store_true")
    arguments = parser.parse_args()

    problems, stats = audit()
    if not stats.get("relations"):
        print("no judgement relations were found; the gate did not run", file=sys.stderr)
        return 1

    if problems:
        shown = problems if arguments.report_all else problems[:1]
        for problem in shown:
            print(f"  {problem}", file=sys.stderr)
        print(
            f"\n{len(problems)} constructor(s) across {stats['relations']} "
            "judgement relations are not backed by a printed primitive "
            f"proposition ({stats.get('primitive-backed', 0)} of "
            f"{stats.get('constructors', 0)} are)",
            file=sys.stderr,
        )
        return 1
    print(
        f"judgement primitives verified ({stats['constructors']} constructors "
        f"across {stats['relations']} relations; "
        f"{stats.get('primitive-backed', 0)} backed by a printed primitive, "
        f"{stats.get('declared-syntax-carriers', 0)} declared syntax carriers)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
