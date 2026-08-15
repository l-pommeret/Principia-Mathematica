#!/usr/bin/env python3
"""A two-sided proposition must assert two sides.

PM writes many propositions as equivalences: ✱10·23 reads
``⊢ :. (x).φx ⊃ p . ≡ : (∃x).φx . ⊃ . p``.  The reconstruction gives each side
its own definition — ``star_10_23_left`` and ``star_10_23_right`` — and the
reading's ``parsed`` field is supposed to tie the printed string to the
assertion of their equivalence.

Nothing checked that it did.  Three theorems were written whose ``parsed``
named one side twice, or a shared "normal form" twice: the statement collapsed
to ``N ≡ N``, and ✱4·2 — reflexivity, which PM proves in one line — discharged
it.  Each compiled, each depended on no axiom, each was written in PM's own
notation, and each was false to the printed proposition.  This is the shape the
969 spurious certifications had, and it is invisible to every other gate:

* the axiom audit sees a pure proof, because ``N ≡ N`` *is* pure;
* T11 sees PM's connectives, because the collapsed formula still uses them;
* T4 compares the printed string to the AST, but the AST it is handed is
  already the collapsed one;
* the printed-citation gate sees ✱4·2 cited and ✱4·2 used.

The defect is one level below all of them, in how the reading was built.  So
the check is deliberately narrow and syntactic: when a file defines both
``<base>_left`` and ``<base>_right``, the ``parsed`` of ``<base>_reading`` must
mention both.  It says nothing about whether the proof is right — only that the
statement has two sides to prove.

Legitimate collapse exists and is not what this gate forbids.  ✱13·1 reads
``x = y .≡ : φ!x .⊃φ . φ!y`` and both sides *do* become the same tree once
✱13·01 is eliminated; PM proves it by ✱4·2 for exactly that reason.  There the
two sides are still built independently, from their own printed forms, and the
collapse is a consequence.  What is forbidden is defining them as the same
expression and calling the consequence a premise.

The same defect wears a second costume.  An implication whose antecedent and
consequent are the same expression collapses to ``N ⊃ N``, and ✱2·08 — identity,
which PM also proves in one line — discharges it.  Three readings were written
that way, and all three were the scope-transport proposition, the one lock the
first volume turns on:

* ✱9·21 printed ``(x).φx ⊃ ψx . ⊃ : (x).φx . ⊃ . (x).ψx``, three quantifiers,
  against an AST holding one, over an identity;
* ✱20·63 and ✱21·63 printed ``(α). p ∨ fα . ⊃ : p . ∨ . (α). fα`` against
  ``A ⊃ A``.

So the check runs over implications too.  Here the exemption is a different
animal and gets its own list: PM *prints* genuine identities — ✱9·23 is
``⊢:(x).φx.⊃.(x).φx  [Id.✱9·13·21]``, ✱23·42 is ``⊢.R⪽R`` — and for those the
reading is right to assert one expression against itself, because that is what
the page says.  Recording the printed line is what separates the two cases, and
only a reader can do it.
"""

from __future__ import annotations

import argparse
import re
import sys
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

#: Propositions whose two printed sides genuinely coincide once PM's own `Df`
#: is eliminated, each recorded with the definition that justifies it.  The
#: exemption is deliberately explicit: a collapse that is a consequence of the
#: printed definitions is faithful, one written into the reading by hand is the
#: defect this gate exists to catch, and only a reader can tell them apart.
EXEMPTIONS = ROOT / "metadata" / "two_sided_exemptions.json"


def _payload() -> dict:
    if not EXEMPTIONS.is_file():
        return {}
    return json.loads(EXEMPTIONS.read_text(encoding="utf-8"))


def exempted() -> set[str]:
    return {
        entry["proposition"]
        for entry in _payload().get("exemptions", [])
        if entry.get("justifying_definition") and len(entry.get("reason", "")) >= 40
    }


def printed_identities() -> set[str]:
    """Propositions PM prints as an identity, each with the line that says so.

    ✱9·23 is ``⊢:(x).φx.⊃.(x).φx``.  A reading that asserts one expression
    against itself is *faithful* there, and the printed line is the evidence.
    Requiring it quoted keeps this list from becoming a place to put whatever
    the implication check happens to reject.
    """
    return {
        entry["proposition"]
        for entry in _payload().get("printed_identities", [])
        if entry.get("printed_line") and len(entry.get("reason", "")) >= 40
    }

#: Where the reconstructed derivations live.
DERIVATION_TREES = ("Principia/Deduction", "Principia/Syntax")

#: Where a reading's ``parsed`` stops.  The trailing ``\b`` must not apply to
#: ``/--``: a hyphen followed by a space is no word boundary, so an earlier
#: version never stopped at a docstring and swallowed the binders of whatever
#: declaration came next — which is how ``star_14_18`` and ``star_23_42`` were
#: reported against `negation : signature.Negation order`, text belonging to a
#: `private theorem` below them.  ``private`` and its neighbours are listed for
#: the same reason.
_READING = re.compile(
    r"(?ms)^def\s+(star_[0-9_]+)_reading\b.*?\bparsed\s*:=(.*?)"
    r"(?=\n\s*(?:(?:private|protected|noncomputable|def|theorem|abbrev"
    r"|instance|structure|inductive|namespace|section|end)\b|/--|@\[)|\Z)"
)


def sources() -> list[Path]:
    found: list[Path] = []
    for tree in DERIVATION_TREES:
        base = ROOT / tree
        if base.is_dir():
            found.extend(sorted(base.rglob("*.lean")))
    return found


#: The equivalence constructors of the reconstruction.  ``star_4_01`` is PM's
#: printed ✱4·01, ``equivalence`` its abbreviation in the ramified syntax.
_EQUIVALENCE = re.compile(
    r"\b(?:star_4_01|equivalence)\b(?P<rest>.*)", re.S
)

#: The implication constructors.  ``star_1_01`` is PM's printed ✱1·01,
#: ``implication`` its abbreviation in the ramified syntax.  ``sameImplication``
#: does not match: the word boundary sits before a capital.
_IMPLICATION = re.compile(
    r"\b(?:star_1_01|implication)\b(?P<rest>.*)", re.S
)


def _arguments(text: str) -> list[str]:
    """Top-level parenthesised arguments of an application, in order."""
    found: list[str] = []
    depth = 0
    current: list[str] = []
    for character in text:
        if character == "(":
            depth += 1
            if depth == 1:
                current = []
                continue
        elif character == ")":
            depth -= 1
            if depth == 0:
                found.append(re.sub(r"\s+", " ", "".join(current)).strip())
                continue
            if depth < 0:
                break
        if depth >= 1:
            current.append(character)
    return found


#: Where a declaration's body stops — the same boundary the reading regex uses.
_DECLARATION_END = (
    r"(?=\n\s*(?:(?:private|protected|noncomputable|def|theorem|abbrev"
    r"|instance|structure|inductive|namespace|section|end)\b|/--|@\[)|\Z)"
)

_DEFINITION = re.compile(
    r"(?ms)^def\s+([A-Za-z_][A-Za-z0-9_']*)\b(?:.*?):=(.*?)" + _DECLARATION_END
)


def definition_bodies(text: str) -> dict[str, str]:
    """Every `def` in the module, mapped to its body with runs of whitespace
    collapsed so that layout does not hide an identity."""
    return {
        match.group(1): re.sub(r"\s+", " ", match.group(2)).strip()
        for match in _DEFINITION.finditer(text)
    }


def _same_bodied_members(base: str, bodies: dict[str, str]) -> tuple[str, str] | None:
    """The two members of ``base`` whose definitions have the same body.

    Naming a term twice is not building it twice.  ✱10·23 was reinstated with
    ``star_10_23_right`` whose body was character-for-character
    ``star_10_23_normalForm``'s — so ✱4·2 discharged it, exactly as in the
    collapse this gate exists to catch, while the argument-level check saw two
    different expressions and passed.  The printed right member is
    ``(∃x).φx ⊃ p`` and carries an existential the tree never had.
    """
    members = [f"{base}_left", f"{base}_right", f"{base}_normalForm"]
    present = [name for name in members if name in bodies]
    for index, name in enumerate(present):
        for other in present[index + 1:]:
            if bodies[name] and bodies[name] == bodies[other]:
                return name, other
    return None


def _repeated_argument(parsed: str, head: re.Pattern[str]) -> str | None:
    """The first argument ``head`` receives twice, if any.

    Whatever the two sides are called, the connective must not receive the same
    expression twice.  ✱10·22 passed ``star_10_22_normalForm …`` as both
    arguments and so escaped a check written around ``_left``/``_right`` names.
    """
    application = head.search(parsed)
    if not application:
        return None
    arguments = [
        argument for argument in _arguments(application.group("rest")) if argument
    ]
    return next(
        (
            argument
            for index, argument in enumerate(arguments)
            if argument in arguments[index + 1:]
        ),
        None,
    )


def one_sided_readings(paths: list[Path]) -> list[str]:
    """Readings whose two asserted sides are the same expression."""
    problems: list[str] = []
    allowed = exempted()
    identities = printed_identities()
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="replace")
        relative = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        bodies = definition_bodies(text)
        for match in _READING.finditer(text):
            base, parsed = match.group(1), match.group(2)

            # Before the exemptions, and deliberately: an exemption certifies
            # that a collapse FOLLOWS from PM's own Df.  Two definitions with
            # the same body have not collapsed — they were never built apart,
            # and no Df can license that.  ✱10·23 carried a valid exemption for
            # ✱9·02--·03 while its right member was a copy of the shared normal
            # form, which is how it passed.
            same = _same_bodied_members(base, bodies)
            if same is not None:
                first, second = same
                problems.append(
                    f"{relative}: `{first}` and `{second}` are defined by the "
                    f"same body, `{bodies[first][:60]}`. Naming a term twice is "
                    "not building it twice: the statement collapses and ✱4·2 "
                    "discharges it.\n"
                    "      Build each member from ITS OWN printed form — ✱10·23's "
                    "right member is `(∃x).φx ⊃ p` and must carry the existential "
                    "through ✱1·01 and ✱9·02, not start from the left member's "
                    "✱9·03. A collapse PM's Df makes unavoidable is faithful, but "
                    "it must be the CONSEQUENCE of two constructions, never the "
                    "premise of one."
                )
                continue

            if base in allowed:
                continue

            repeated = _repeated_argument(parsed, _EQUIVALENCE)
            if repeated is None and base not in identities:
                # `N ⊃ N`, discharged by ✱2·08, is the same defect wearing a
                # second costume.  PM does print genuine identities, so this
                # branch has its own exemption list, keyed on the printed line.
                implied = _repeated_argument(parsed, _IMPLICATION)
                if implied is not None:
                    problems.append(
                        f"{relative}: `{base}_reading` asserts an implication whose "
                        f"antecedent and consequent are the same expression, "
                        f"`{implied[:60]}`. The statement collapses to `N ⊃ N` and "
                        "✱2·08 discharges it: build each side from its own printed "
                        "form.\n"
                        "      If PM PRINTS the proposition as an identity — ✱9·23 "
                        "is `⊢:(x).φx.⊃.(x).φx  [Id.✱9·13·21]`, ✱23·42 is `⊢.R⪽R` — "
                        "then asserting one expression against itself is faithful. "
                        "Record it under `printed_identities` in "
                        "metadata/two_sided_exemptions.json, quoting the printed "
                        "line that says so."
                    )
                    continue

            if repeated is not None:
                problems.append(
                    f"{relative}: `{base}_reading` asserts an equivalence whose "
                    f"two sides are the same expression, `{repeated[:60]}`. The "
                    "statement collapses to `N ≡ N` and reflexivity discharges "
                    "it: build each side from its own printed form.\n"
                    "      If PM's own Df makes the two sides coincide — ✱13·1 "
                    "is `x = y .≡ : φ!x .⊃φ . φ!y`, and ✱13·01 defines `x = y` "
                    "as exactly that — the collapse is faithful, but it must be "
                    "a CONSEQUENCE of building each side from its printed form, "
                    "not a premise written into the reading. Record the "
                    "exemption in metadata/two_sided_exemptions.json with the "
                    "Df that justifies it."
                )
                continue

            left, right = f"{base}_left", f"{base}_right"
            defines_both = re.search(rf"(?m)^def\s+{left}\b", text) and re.search(
                rf"(?m)^def\s+{right}\b", text
            )
            if not defines_both:
                continue
            asserts_left = re.search(rf"\b{left}\b", parsed) is not None
            asserts_right = re.search(rf"\b{right}\b", parsed) is not None
            if asserts_left and asserts_right:
                continue
            missing = left if not asserts_left else right
            problems.append(
                f"{relative}: `{base}_reading` defines `{left}` and `{right}` but "
                f"its `parsed` never mentions `{missing}`. The statement therefore "
                "asserts one side against itself, and reflexivity discharges it: "
                "build each side from its own printed form."
            )
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-all", action="store_true")
    arguments = parser.parse_args()

    paths = sources()
    if not paths:
        print(
            f"no Lean source under {', '.join(DERIVATION_TREES)}; nothing checked",
            file=sys.stderr,
        )
        return 1

    counted = sum(
        len(_READING.findall(path.read_text(encoding="utf-8", errors="replace")))
        for path in paths
    )
    problems = one_sided_readings(paths)
    if problems:
        shown = problems if arguments.report_all else problems[:10]
        for problem in shown:
            print(f"  {problem}", file=sys.stderr)
        if len(problems) > len(shown):
            print(f"  ... and {len(problems) - len(shown)} more", file=sys.stderr)
        print(
            f"\n{len(problems)} two-sided propositions assert only one side. "
            "A proposition PM prints as an equivalence, or as an implication "
            "between two different things, has two sides to prove.",
            file=sys.stderr,
        )
        return 1

    print(f"two-sided readings verified ({counted} readings, {len(paths)} modules)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
