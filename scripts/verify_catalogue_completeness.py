#!/usr/bin/env python3
"""Require every proposition printed in the witnesses to have a catalogue entry.

The other witness gate, ``verify_printed_against_witness.py``, judges the
*text* of blocks we already catalogued.  It is therefore blind by construction
to a proposition we never catalogued at all: an absent entry produces no
divergence, no unsupported notation, no report line -- nothing.  A catalogue
shorter than the book looks exactly like a catalogue that agrees with it.

This gate closes that hole from the other side.  It enumerates the propositions
actually printed in the Gutenberg witnesses and requires each one to appear in
``metadata/items``.  It is deterministic and textual: no model, no heuristic
matching, no inference about meaning.

Two properties of PM's typesetting drive the parse, and both were found by
measurement rather than assumed:

*   PM concatenates its references.  ``*10·11·21`` is not a proposition, it is
    the citation "by ✱10·11 and ✱10·21".  A statement is therefore recognised
    only at the start of a line and only with exactly two number components,
    while citations occur inside brackets and carry more.

*   The compositor sets a minority of numbers with an ordinary full stop --
    ``*33.151.``, ``*71.28.`` -- where the rest of the book carries the middle
    dot ``·``.  Both forms are regular statements.  A parse keyed on ``·``
    alone silently drops them, which is precisely how ✱33·151 and ✱71·28 came
    to be missing from the catalogue.  Note that ``WITNESS_RE`` in
    ``verify_printed_against_witness.py`` still has this defect; widening it
    changes that gate's verdicts and is deliberately not done here.

Exemptions exist for the case the maintainer anticipated: a witness reading
that is manifestly not a proposition of the printed book (a Gutenberg
transcription artefact).  They require a written justification, because a
dispensation without a stated reason is indistinguishable from a silenced
failure.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ITEMS_DIR = ROOT / "metadata" / "items"
DEFAULT_EXEMPTIONS = ROOT / "metadata" / "catalogue_completeness_exemptions.json"
MIN_REASON_LENGTH = 40

WITNESSES = {
    "PM1": ROOT / "metadata" / "witnesses" / "gutenberg" / "pg78050-tex.txt",
    "PM2": ROOT / "metadata" / "witnesses" / "gutenberg" / "pg78255-tex.txt",
}

#: Volumes whose catalogue must be complete for CI to pass.
#:
#: Volume I is the volume under certification, and its catalogue is complete.
#: Volume II is enumerated by the same parse and its shortfall is printed on
#: every run -- it is measured debt, not a silenced failure -- but it does not
#: fail CI while volume I is the objective.  The distinction is deliberate: a
#: gate that fails by a thousand items on work nobody has started yet stops
#: reporting anything, because it is red whatever happens.  Add "PM2" here the
#: day volume II is catalogued; nothing else needs to change.
CERTIFIED_VOLUMES = ("PM1",)

#: A printed statement: start of line, ``*`` , chapter, separator, number, and a
#: terminating full stop.  Exactly two components -- a third would make it one
#: of PM's concatenated citations.  Both separators are accepted; see module
#: docstring.
#:
#: The number must be followed *immediately* by mathematics.  Requiring only
#: that mathematics occur somewhere nearby admits running prose: the witness
#: contains "The first use of the following proposition occurs in the proof of
#: *234·12. Its utility lies in ...", where a citation opens a line and a
#: display follows two sentences later.  Anchoring the opening delimiter
#: rejects it without an exception list.
STATEMENT_RE = re.compile(
    r"(?:^|\n)[ \t]*\*(\d+)[·.](\d+)\.\s{0,4}(\\\(|\\\[|\\begin)"
)


@dataclass(frozen=True)
class Statement:
    identifier: str
    excerpt: str


def parse_witness(path: Path, volume: str) -> dict[str, Statement]:
    text = path.read_text(encoding="utf-8", errors="replace")
    found: dict[str, Statement] = {}
    for match in STATEMENT_RE.finditer(text):
        chapter, number, _opening = match.groups()
        identifier = f"{volume}:✱{chapter}·{number}"
        excerpt = " ".join(text[match.end() - 2:match.end() + 88].split())
        found.setdefault(identifier, Statement(identifier, excerpt))
    return found


def catalogue_identifiers() -> set[str]:
    identifiers: set[str] = set()
    for path in sorted(ITEMS_DIR.glob("*.json")):
        try:
            document = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise SystemExit(f"catalogue illisible : {path.name} ({error})")
        for item in document.get("items", []):
            identifier = item.get("id")
            if isinstance(identifier, str):
                identifiers.add(identifier)
    return identifiers


def load_exemptions(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"registre de dispenses illisible : {error}")
    exemptions: dict[str, str] = {}
    for entry in document.get("exemptions", []):
        identifier = entry.get("id")
        reason = entry.get("reason", "")
        if not isinstance(identifier, str) or not isinstance(reason, str):
            raise SystemExit("dispense malformée : 'id' et 'reason' sont requis")
        if len(reason.strip()) < MIN_REASON_LENGTH:
            raise SystemExit(
                f"dispense insuffisamment justifiée pour {identifier} : "
                f"{MIN_REASON_LENGTH} caractères au minimum"
            )
        exemptions[identifier] = reason.strip()
    return exemptions


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-all", action="store_true",
                        help="lister aussi les entrées du catalogue absentes du témoin")
    parser.add_argument("--exemptions", type=Path, default=DEFAULT_EXEMPTIONS)
    arguments = parser.parse_args()

    exemptions = load_exemptions(arguments.exemptions)
    catalogued = catalogue_identifiers()

    printed: dict[str, Statement] = {}
    for volume, path in WITNESSES.items():
        if not path.exists():
            print(f"témoin absent : {path.relative_to(ROOT)}", file=sys.stderr)
            return 1
        printed.update(parse_witness(path, volume))

    absent = sorted(
        set(printed) - catalogued - set(exemptions),
        key=lambda name: [int(part) for part in re.findall(r"\d+", name)],
    )
    missing = [name for name in absent if name.split(":")[0] in CERTIFIED_VOLUMES]
    observed = [name for name in absent if name.split(":")[0] not in CERTIFIED_VOLUMES]
    stale = sorted(set(exemptions) & catalogued)

    for volume in WITNESSES:
        count = sum(1 for name in printed if name.startswith(f"{volume}:"))
        shortfall = sum(1 for name in absent if name.startswith(f"{volume}:"))
        judged = "certifié" if volume in CERTIFIED_VOLUMES else "mesuré, non bloquant"
        print(f"{volume} : {count} énoncés imprimés relevés, "
              f"{shortfall} sans entrée au catalogue ({judged})")
    print(f"catalogue : {len(catalogued)} entrées")

    if arguments.report_all:
        unwitnessed = sorted(
            identifier for identifier in catalogued
            if identifier.split(":")[0] in WITNESSES and identifier not in printed
        )
        print(f"catalogué sans énoncé relevé dans le témoin : {len(unwitnessed)}")

    if stale:
        print("\nDISPENSES DEVENUES INUTILES — la proposition est maintenant cataloguée :")
        for identifier in stale:
            print(f"  {identifier}")

    if observed and arguments.report_all:
        print(f"\nDETTE MESURÉE, HORS VOLUME CERTIFIÉ : {len(observed)}")
        for identifier in observed[:20]:
            print(f"  {identifier:<14} {printed[identifier].excerpt}")
        if len(observed) > 20:
            print(f"  … et {len(observed) - 20} autres")

    if missing:
        print(f"\nIMPRIMÉ MAIS NON CATALOGUÉ, VOLUME CERTIFIÉ : {len(missing)}")
        for identifier in missing:
            print(f"  {identifier:<14} {printed[identifier].excerpt}")
        return 1

    if stale:
        return 1

    certified = ", ".join(CERTIFIED_VOLUMES)
    print(f"\ntout énoncé imprimé dans {certified} a une entrée au catalogue")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
