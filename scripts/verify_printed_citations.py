#!/usr/bin/env python3
"""The Lean proof must take the route the printed demonstration takes.

Criteria T1–T10 establish that a proof *is* a derivation in the reconstructed
calculus, from PM's primitives, with no axiom.  None of them asks whether it is
*PM's* derivation.  A proof could satisfy all ten and still reach the printed
proposition by a route Whitehead and Russell never licensed.

PM prints its citations explicitly.  The demonstration of ✱2·01 reads

    [Taut  ∼p/p]       ⊢ : ∼p ∨ ∼p . ⊃ . ∼p          (1)
    [(1).(✱1·01)]      ⊢ : p ⊃ ∼p . ⊃ . ∼p

so ✱2·01 is licensed to use ✱1·2 and ✱1·01, and nothing else.  This gate asks
the kernel what the proof term actually contains — ``#print`` with
``pp.fullNames`` emits the elaborated term, so a lemma reached through ``simp``
or a helper is as visible as one written by hand — and compares that with the
catalogued printed citations.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ITEMS = ROOT / "metadata" / "items"

#: Editorial interface lemmas that stand for a printed rule rather than adding
#: one.  ``detach`` combines ✱1·1 and ✱1·11 without identifying them (see
#: Principia/Deduction/System.lean); using it is using those rules.
INTERFACE_LEMMAS = {
    "PM.Derivation.detach": {"✱1·1", "✱1·11"},
    "PM.Derivation.instantiateSchema": set(),
}

#: PM's own abbreviated titles (Principia/Deduction/PrintedNames.lean).  A proof
#: that writes `Taut` is citing ✱1·2 exactly as the printed demonstration does.
PRINTED_TITLES = {
    "PM.Derivation.Taut": "✱1·2",
    "PM.Derivation.Add": "✱1·3",
    "PM.Derivation.Perm": "✱1·4",
    "PM.Derivation.Assoc": "✱1·5",
    "PM.Derivation.Sum": "✱1·6",
}

_STAR_CONST = re.compile(r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)*star_(\d+)_(\d+)\b")
#: The header line ``#print`` emits, in every shape it actually emits it.
#:
#: Reading only ``^(theorem|def) (\S+)`` missed most of the library and said so
#: in the worst possible way — as 85 declarations "the build does not contain",
#: when each existed under the exact catalogued name.  ``#print`` writes a
#: polymorphic definition as ``def star_13_01.{u_1}``, so the universe suffix
#: became part of the key; it keeps attributes, so ``@[reducible] def`` did not
#: match at all; and it announces a constructor with its own keyword.  The gate
#: was therefore judging 24 proofs while reporting on 87, and nothing said so.
_THEOREM_LINE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:theorem|def|abbrev|instance|constructor)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*?)(?:\.\{[^}]*\})?(?=[\s:{(]|$)"
)


def catalogued(statuses: set[str]) -> dict[str, dict]:
    """Certified items, keyed by declaration."""
    found: dict[str, dict] = {}
    for path in sorted(ITEMS.glob("*.json")):
        batch = json.loads(path.read_text(encoding="utf-8"))
        for item in batch.get("items", []):
            if item.get("formal_status") in statuses and item.get("declaration"):
                found[item["declaration"]] = item
    return found


def print_terms(declarations: list[str]) -> dict[str, str]:
    """Elaborated proof term of each declaration, via ``#print``."""
    body = "\n".join(f"#print {name}" for name in sorted(set(declarations)))
    program = f"import Principia\nset_option pp.fullNames true\n\n{body}\n"
    with tempfile.TemporaryDirectory(prefix="pm-citations-") as directory:
        probe = Path(directory) / "Citations.lean"
        probe.write_text(program, encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    output = result.stdout + "\n" + result.stderr
    if "theorem" not in output and "def" not in output:
        raise SystemExit(
            "`#print` produced nothing parsable; run `lake build` first.\n"
            + output.strip()[:2000]
        )
    terms: dict[str, str] = {}
    current: str | None = None
    chunk: list[str] = []
    for line in output.splitlines():
        match = _THEOREM_LINE.match(line)
        if match:
            if current:
                terms[current] = "\n".join(chunk)
            current = match.group(1)
            chunk = [line]
        elif current:
            chunk.append(line)
    if current:
        terms[current] = "\n".join(chunk)
    return terms


def used_propositions(declaration: str, term: str) -> set[str]:
    """PM ids the elaborated proof term actually depends on."""
    used: set[str] = set()
    for lemma, stands_for in INTERFACE_LEMMAS.items():
        if lemma in term:
            used |= stands_for
    for title, number in PRINTED_TITLES.items():
        if title in term:
            used.add(number)
    own = _STAR_CONST.search(declaration)
    for match in _STAR_CONST.finditer(term):
        star, part = match.groups()
        if own and (star, part) == own.groups():
            continue  # the declaration's own name in its signature
        # The volume prefix is not recoverable from the Lean name; accept any.
        used.add(f"✱{star}·{part}")
    return used


#: Catalogue kinds that classify a proposition as a rule *about* assertions
#: rather than a proposition *of* the calculus.
#:
#: PM draws this line itself. ✱3·03 reads "Given two asserted elementary
#: propositional functions ⊢.φp and ⊢.ψp …, we have ⊢ . φp . ψp": it says what
#: one may assert, not what holds in the object language. Such a rule is
#: discharged by the architecture — `PM.Derivation.detach` embodies ✱1·1 and
#: ✱1·11 without identifying them — so it cannot be expected to appear as a
#: constant in a proof term, and demanding it would report admissibility rules as
#: missing citations while masking the departures from the printed text that
#: actually matter.
METALINGUISTIC_KINDS = frozenset({
    "derived-metalinguistic-rule",
    "metatheoretic-principle",
    "primitive-inference-rule",
    "primitive-function-inference-rule",
    "primitive-formation-rule",
    "significance-proposition",
})


def _metalinguistic_ids() -> set[str]:
    """PM numbers the catalogue classifies as rules about assertion."""
    found: set[str] = set()
    for path in sorted(ITEMS.glob("*.json")):
        try:
            batch = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        for item in batch.get("items", []):
            if item.get("kind") in METALINGUISTIC_KINDS:
                identifier = item.get("id")
                if isinstance(identifier, str) and "✱" in identifier:
                    found.add(identifier.split(":", 1)[-1])
    return found


def cited_propositions(item: dict, metalinguistic: set[str] | None = None) -> set[str]:
    cited: set[str] = set()
    for entry in item.get("printed_dependencies", []) or []:
        if isinstance(entry, str) and "✱" in entry:
            number = entry.split(":", 1)[-1]
            if metalinguistic and number in metalinguistic:
                continue
            cited.add(number)
    return cited


def audit(statuses: set[str]) -> tuple[list[str], dict[str, int]]:
    items = catalogued(statuses)
    if not items:
        raise SystemExit(
            f"no catalogue item carries formal_status in {sorted(statuses)}; "
            "nothing was audited"
        )
    terms = print_terms(list(items))
    metalinguistic = _metalinguistic_ids()
    problems: list[str] = []
    stats: dict[str, int] = defaultdict(int)

    for declaration, item in sorted(items.items()):
        term = terms.get(declaration)
        if term is None:
            problems.append(
                f"{item['id']}: `{declaration}` produced no term; the catalogue "
                "claims a declaration the build does not contain"
            )
            continue
        stats["audited"] += 1
        used = used_propositions(declaration, term)
        cited = cited_propositions(item, metalinguistic)

        if not cited:
            stats["no-citations-recorded"] += 1
            continue

        # The decisive direction.  PM abbreviates: its demonstrations cite the
        # substantive steps and leave routine transitions implicit ("this
        # process ... will therefore be abbreviated"), so a Lean term legitimately
        # mentions more than the print does.  The converse is not legitimate: if
        # the printed demonstration says "by ✱4·38" and the proof term never
        # touches ✱4·38, the Lean proof is not a reconstruction of that
        # demonstration — it is an independent re-derivation of the same theorem.
        unused = {
            citation for citation in cited
            if citation not in used and _reachable_form(citation, used)
        }
        if unused:
            problems.append(
                f"{item['id']}: printed demonstration cites {sorted(unused)}, "
                f"which the proof term never uses. It proves the proposition by "
                f"another route (term uses {sorted(used)[:8]}...)"
            )
            continue
        stats["follows-the-print"] += 1
        if used - cited:
            stats["more-explicit-than-print"] += 1
    return problems, dict(stats)


def _reachable_form(citation: str, used: set[str]) -> bool:
    """Whether a citation is in a shape this gate can honestly judge.

    PM compresses several numbers into one bracket — ``✱5·3·32`` cites both
    ✱5·3 and ✱5·32, and ``✱4·62·51`` cites ✱4·62 and ✱4·51.  Treating such a
    compound as a single missing citation would be a false positive, so a
    compound counts as satisfied when any of its components is used.
    """
    parts = citation.lstrip("✱").split("·")
    if len(parts) <= 2:
        return True
    star = parts[0]
    return not any(f"✱{star}·{part}" in used for part in parts[1:])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--status", action="append", default=None)
    parser.add_argument("--report-all", action="store_true")
    arguments = parser.parse_args()
    statuses = set(arguments.status or ["kernel-checked", "awaiting-ci"])

    problems, stats = audit(statuses)
    if problems:
        shown = problems if arguments.report_all else problems[:1]
        for problem in shown:
            print(f"  {problem}", file=sys.stderr)
        print(
            f"\n{len(problems)} of {stats.get('audited', 0)} proofs do not "
            "follow their printed demonstration: they prove the proposition by "
            "a route of their own instead of the one PM prints",
            file=sys.stderr,
        )
        return 1
    print(
        f"printed citations verified ({stats.get('faithful', 0)} proofs follow "
        f"their printed demonstration; {stats.get('cited-but-unused', 0)} cite "
        "more than they use)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
