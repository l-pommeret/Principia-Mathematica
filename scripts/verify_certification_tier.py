#!/usr/bin/env python3
"""Compute each catalogue item's certification tier from the Lean sources.

The tier is *derived*, never asserted.  A catalogue item may claim the top tier
only when the Lean tree independently exhibits, for that item, the same shape
the ✱1–✱5 layer exhibits: a printed reading tied to an abstract syntax tree, and
a theorem whose statement is a judgement of the reconstructed object calculus
over exactly that tree.  See ``docs/CERTIFICATION_TIERS.md``.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pm_lean_index import (  # noqa: E402
    ROOT,
    compiled_modules,
    declarations,
    import_closure,
    judgement_relations,
    reading_types,
    lean_string_after,
    normalise_formula,
    normalise_printed,
    source,
)

ITEMS = ROOT / "metadata" / "items"

TIER_MAX = "kernel-checked"
TIER_TYPECHECKED = "lean-typechecked"
TIER_UNBUILT = "unbuilt"
TIER_AWAITING = "awaiting-ci"
TIER_PREPARED = "prepared"

#: The closed tier vocabulary.  Anything else is a status invented in passing.
KNOWN_TIERS = frozenset(
    {TIER_MAX, TIER_TYPECHECKED, TIER_UNBUILT, TIER_AWAITING, TIER_PREPARED}
)

#: Statuses that record intent rather than a verification result, and are
#: therefore not recomputed: an item nobody has formalised yet stays where it is.
#:
#: ``awaiting-ci`` is deliberately NOT here.  It means "structurally sound, no CI
#: evidence yet", so it must still be evaluated — otherwise parking an item there
#: exempts it from every structural criterion, and the tier becomes a place to
#: hide rather than a measurement.  An item that fails only T7 lands back on
#: ``awaiting-ci`` anyway, through the tier assignment below.
INTENT_STATUSES = frozenset({TIER_PREPARED})

#: Catalogue kinds that denote a printed `Df`.  These must be `def`s in Lean.
#:
#: A definition is not a derivation: it asserts nothing, so demanding that its
#: statement be a judgement (T3) or that it carry a demonstration reading (T4)
#: would be demanding the wrong thing.  What it must satisfy is that it unfolds —
#: which is T2's business here.
DEFINITION_KINDS = frozenset(
    {"definition", "notation-definition", "contextual-definition"}
)

#: Catalogue kinds PM prints as primitive: asserted, not derived.  Each is
#: faithfully encoded as a *constructor* of the relevant judgement relation, so
#: T3 and T4 hold by construction — the constructor's type is the judgement.
PRIMITIVE_KINDS = frozenset({
    "primitive-proposition",
    "primitive-idea",
    "primitive-formation-rule",
    "primitive-inference-rule",
    "primitive-function-inference-rule",
})

#: Notations that abbreviate a judgement of an object calculus.  ``⊢ₚ`` is the
#: propositional calculus of ✱1–✱5; ``⊢ᵣ`` is the ramified judgement that
#: carries quantifiers, classes and descriptions from ✱9 onwards.
JUDGEMENT_NOTATION = ("⊢ₚ", "⊢ᵣ")

#: Lean's own logical connectives.  Inside the *object formula* — the part a
#: judgement asserts — these have no business appearing: PM's connectives are
#: object syntax with their own notation (`∼ₚ`, `∨ₚ`, `⊃ₚ`, `∧ₚ`, `≡ₚ`), and a
#: Lean `∧` or `→` there means the statement has slipped out of the reconstructed
#: calculus into the host logic.  The subscripted forms are excluded from the
#: match by the trailing-subscript guard.
HOST_CONNECTIVES = re.compile(r"(?<![ₚᵣ])(?:∧|∨|¬|↔|→|⊃)(?![ₚᵣ])")

#: PM connectives, so a formula can be shown to be written in PM's own notation
#: rather than merely avoiding Lean's.
PM_CONNECTIVES = re.compile(r"∼ₚ|∨ₚ|⊃ₚ|∧ₚ|≡ₚ")


def _qualified(name: str) -> str:
    """Match ``Name`` whether or not it carries a namespace prefix.

    Lean sources write both `Derivation` and `PM.Derivation`, and both
    `ElementaryReading` and `PM.ElementaryReading`.  A lookbehind that rejects a
    preceding dot silently misses every qualified use — which made ✱1–✱5, the
    reference layer, fail the criteria calibrated on it.
    """
    return r"(?<![A-Za-z0-9_])(?:[A-Za-z_][A-Za-z0-9_']*\.)*" + re.escape(name) + r"(?![A-Za-z0-9_'])"

CRITERIA = {
    "T1": "lean_path is outside the import closure of Principia.lean",
    "T2": "declaration is missing, or is not a theorem",
    "T3": "statement is not a judgement of the object calculus",
    "T4": "no printed↔AST reading ties the catalogue statement to the theorem",
    "T5": "declaration depends on a disallowed axiom",
    "T6": "statement is vacuous, or duplicates another item's statement",
    "T7": "CI evidence does not resolve",
    "T8": "formalization_level is missing, or claims more than the tree supports",
    "T9": "depends on a non-logical assumption without declaring it",
    "T11": "the asserted formula is not written in PM's own notation",
    "T12": "the judgement is asserted only under an undischarged hypothesis",
}

#: Catalogue kinds that PM states *with* premises, and which therefore may carry
#: a judgement in their hypotheses.  ✱1·1 reads "anything implied by a true
#: elementary proposition is true": its premises are the rule, not a debt.
#: Everything else PM asserts categorically, with `⊢` and nothing to the left of
#: it, so a theorem of the form `(h : ⊢ᵣ A) → ⊢ᵣ B` proves a conditional PM
#: never states.  Such a theorem is a legitimate step while a chapter is being
#: built — the brief allows naming what is still missing — but it is not a
#: derivation of the printed proposition and must never be certified as one.
PREMISED_KINDS = frozenset({
    "primitive-inference-rule",
    "primitive-function-inference-rule",
    "derived-metalinguistic-rule",
    "metatheoretic-principle",
})

#: Lean names that carry a non-logical PM assumption, mapped to the registry id
#: an item must declare when it reaches them.  Russell treated reducibility as
#: the doubtful axiom of the system; a proof that leans on it silently is not at
#: the ✱1–✱5 standard whatever else it satisfies.
ASSUMPTION_CARRIERS = {
    "ReducibilityDerivation": "PM1:REDUCIBILITY",
    "UnaryReducibility": "PM1:REDUCIBILITY",
    "BinaryReducibility": "PM1:REDUCIBILITY",
    "PredicativeCertificate": "PM1:REDUCIBILITY",
    # The printed primitives themselves.  Reducibility may be carried by a type
    # *or* asserted by a constructor named for the proposition; tracking only
    # the type names would let a proof reach ✱12·1 without the assumption ever
    # being declared — which is precisely the axiom Russell held to be the
    # doubtful one, so it is the one that must never travel silently.
    "star_12_1": "PM1:REDUCIBILITY",
    "star_12_11": "PM1:REDUCIBILITY",
    "AxiomOfInfinity": "PM2:INFINITY",
    "star_120_03": "PM2:INFINITY",
    "MultiplicativeAxiom": "PM2:MULTIPLICATIVE",
    "star_88_03": "PM2:MULTIPLICATIVE",
}

#: Item fields that may carry a declared assumption id.  Several spellings are
#: in use in the catalogue; all are accepted so the check reports a genuine
#: omission rather than a vocabulary mismatch.
ASSUMPTION_FIELDS = (
    "direct_assumptions",
    "inherited_assumptions",
    "non_logical_assumptions",
)

#: Declared level an item must carry to be promotable at all.  Agreed with the
#: parallel formalisation effort (see ``dialogue.md``): the field is mandatory
#: for ``awaiting-ci`` and ``kernel-checked``, and a field that claims the level
#: without satisfying T1–T7 is itself a gate failure.
REQUIRED_FORMALIZATION_LEVEL = "pm-derivation-v1"


def load_batches() -> list[tuple[Path, dict]]:
    batches = []
    for path in sorted(ITEMS.glob("*.json")):
        try:
            batches.append((path, json.loads(path.read_text(encoding="utf-8"))))
        except json.JSONDecodeError as error:
            raise SystemExit(f"unreadable catalogue file {path}: {error}") from error
    if not batches:
        raise SystemExit(f"no catalogue files found under {ITEMS}")
    return batches


#: A binder whose type is a judgement: `(h : ⊢ᵣ φ)`, `{d : PM.Derivation …}`,
#: `[e : DerivationEvidence …]`.  Only the binder head is matched; the type is
#: examined by the caller, which knows the judgement vocabulary.
_BINDER = re.compile(r"[({\[]\s*[^:()\[\]{}]+:\s*([^()\[\]{}]*(?:\([^()]*\)[^()\[\]{}]*)*)")


def _hypothesised_judgements(statement: str) -> list[str]:
    """Judgement-typed hypotheses the statement leaves undischarged.

    ``_statement_formula`` searches the whole statement, so it finds the
    judgement of ``(h : ⊢ᵣ A) : ⊢ᵣ B`` in the *hypothesis* and reports the
    theorem as a judgement.  That is how a conditional derivation could be
    certified as a derivation — the theorem would assert, not that PM's
    proposition holds, but that it follows from something the catalogue never
    establishes.
    """
    found: list[str] = []
    relations = judgement_relations()
    for match in _BINDER.finditer(statement):
        binder_type = match.group(1)
        for notation in JUDGEMENT_NOTATION:
            if notation in binder_type:
                found.append(binder_type.strip())
                break
        else:
            for relation in relations:
                if re.search(_qualified(relation), binder_type):
                    found.append(binder_type.strip())
                    break
    return found


def _statement_formula(statement: str) -> tuple[str, str] | None:
    """``(judgement name, asserted formula)``, or ``None`` if not a judgement.

    Only an inductive ``Prop``-valued relation counts.  A ``structure`` whose
    fields the caller supplies — the shape of ``Star_11_42Derivation`` — is
    inhabited without any derivation having taken place, so it is not a
    judgement however it is named.
    """
    for notation in JUDGEMENT_NOTATION:
        position = statement.find(notation)
        if position >= 0:
            return notation, statement[position + len(notation):]
    for relation in judgement_relations():
        match = re.search(_qualified(relation), statement)
        if match:
            return relation, statement[match.end():]
    return None


VACUOUS_BODY = re.compile(r"^\s*(?:fun\s+(\w+)\s*(?:=>|↦)\s*\1|id|Iff\.rfl|rfl)\s*$")
SELF_RELATION = re.compile(r"^(.*?)(=|↔|→|⊃ₚ)(.*)$")


def _is_vacuous(statement: str, body: str) -> str | None:
    """Return a reason when a statement carries no commitment."""
    formula = statement.split(":")[-1] if ":" in statement else statement
    for connective in ("↔", "=", "→"):
        if connective in formula:
            left, _, right = formula.partition(connective)
            if left.strip() and normalise_formula(left) == normalise_formula(right):
                return f"statement is `X {connective} X`"
    if VACUOUS_BODY.match(body.strip()) and "↔" not in formula and "=" not in formula:
        stripped = formula.strip()
        if "→" in stripped:
            left, _, right = stripped.partition("→")
            if normalise_formula(left) == normalise_formula(right):
                return "proof term is the identity on a self-implication"
    return None


def constructor_site(lean_path: str, name: str) -> str | None:
    """The judgement relation ``name`` is a constructor of, if it is one.

    PM's primitive propositions are asserted, not derived, so the faithful
    encoding is a constructor of the derivation relation — ``star_1_2`` at
    ``System.lean:28``.  Such an item satisfies T3 and T4 by construction: the
    constructor's type *is* the judgement, indexed by the printed formula.
    """
    if not lean_path:
        return None
    text = source(lean_path)
    for relation in judgement_relations():
        match = re.search(r"(?m)^\s*inductive\s+" + re.escape(relation) + r"\b", text)
        if not match:
            continue
        tail = text[match.end():]
        stop = re.search(
            r"(?m)^\s*(?:inductive|structure|def|theorem|lemma|abbrev|end|namespace)\b",
            tail,
        )
        body = tail[: stop.start()] if stop else tail
        if re.search(r"(?m)^\s*\|\s*" + re.escape(name) + r"\b", body):
            return relation
    return None


def _declared_assumptions(item: dict) -> set[str]:
    declared: set[str] = set()
    for field in ASSUMPTION_FIELDS:
        value = item.get(field)
        if isinstance(value, str):
            declared.add(value)
        elif isinstance(value, list):
            for entry in value:
                if isinstance(entry, str):
                    declared.add(entry)
                elif isinstance(entry, dict) and isinstance(entry.get("id"), str):
                    declared.add(entry["id"])
    return declared


def undeclared_assumptions(item: dict, lean_path: str, declared) -> set[str]:
    """Non-logical assumptions the item reaches but does not record.

    The reach test is textual and deliberately local: it looks at the statement
    and proof term of the declaration itself, plus the item's recorded Lean
    dependencies.  It therefore under-reports rather than over-reports — a
    transitive dependency through a helper is not caught — so a clean result is
    not a proof of independence, only the absence of a visible undeclared use.
    """
    if declared is None:
        return set()
    surface = declared.statement + declared.body
    dependencies = " ".join(
        entry for entry in item.get("lean_dependencies", []) if isinstance(entry, str)
    )
    recorded = _declared_assumptions(item)
    reached = {
        assumption
        for carrier, assumption in ASSUMPTION_CARRIERS.items()
        if carrier in surface or carrier in dependencies
    }
    return reached - recorded


def compute(item: dict, evidence_failures: list[str]) -> tuple[str, list[str], dict]:
    """Return ``(tier, failed_criteria, diagnostics)`` for one catalogue item."""
    failed: list[str] = []
    notes: dict[str, str] = {}

    recorded = item.get("formal_status")
    # Every item is evaluated, whatever it currently records.  Returning early
    # for `prepared` made unevaluated items indistinguishable from conformant
    # ones in every census — 2735 items silently counted as passing because
    # nobody had looked at them.  A tier must never be flattered by ignorance.
    # `prepared` is still honoured below: an item that fails stays where it is,
    # and one that passes has genuinely earned the promotion.

    lean_path = item.get("lean_path") or ""
    declaration = item.get("declaration") or ""
    base = declaration.rsplit(".", 1)[-1]

    if lean_path not in import_closure():
        failed.append("T1")
        # `globs` in lakefile.toml make lake *compile* every module, which is why
        # a broken orphan now breaks the build.  That is not enough to certify:
        # a module outside the import closure of Principia.lean is invisible to
        # `import Principia`, so `#print axioms` cannot audit it (T5) and it is
        # not part of the published library at all.
        detail = (
            "compiled by lake, but unreachable from `import Principia`"
            if lean_path in compiled_modules()
            else "compiled by nothing"
        )
        notes["T1"] = f"{lean_path} is {detail}"

    index = declarations(lean_path) if lean_path else {}
    declared = index.get(base)

    # A printed primitive proposition is realised as a *constructor* of the
    # judgement relation, not as a theorem: `PM.Derivation.star_1_2` is a
    # constructor at System.lean:28, and asserting it is exactly what PM does.
    # Looking only for top-level declarations made the six primitives of ✱1 —
    # the reference the whole standard is calibrated on — fail T2.
    primitive = constructor_site(lean_path, base) if declared is None else None
    if primitive is not None:
        if item.get("kind") not in PRIMITIVE_KINDS:
            failed.append("T2")
            notes["T2"] = (
                f"{base} is a constructor of `{primitive}`, which only a "
                f"primitive proposition may be; this item is catalogued as "
                f"{item.get('kind')!r}"
            )
        else:
            # T3 and T4 are satisfied by construction here: the constructor's
            # own type is the judgement, indexed by the printed formula's AST.
            return (TIER_MAX if not failed else TIER_TYPECHECKED), sorted(set(failed)), notes
    elif declared is None:
        failed.append("T2")
        notes["T2"] = f"{declaration!r} not found in {lean_path}"
    elif item.get("kind") in DEFINITION_KINDS:
        # PM's `Df` are eliminable abbreviations: the printed text expands them
        # away.  A `theorem` stating the definition asserts it instead, which
        # makes an abbreviation irreducible and adds to the system.
        if declared.kind not in {"def", "abbrev"}:
            failed.append("T2")
            notes["T2"] = (
                f"{base} is catalogued as `{item.get('kind')}` but declared as a "
                f"`{declared.kind}`; a printed Df must be a `def` that unfolds"
            )
    elif declared.kind not in {"theorem", "lemma"}:
        failed.append("T2")
        notes["T2"] = f"{base} is a `{declared.kind}`, not a theorem"

    if declared is not None:
        judgement = _statement_formula(declared.statement)
        formula = judgement[1] if judgement else None
        is_definition = item.get("kind") in DEFINITION_KINDS
        if judgement is None and not is_definition:
            failed.append("T3")
            notes["T3"] = (
                "statement is not an application of an inductive Prop-valued "
                "derivation relation (a structure with caller-supplied fields "
                "does not count)"
            )

        # PM's own page decides whether a premise is legitimate.  What it
        # asserts categorically it prints with `⊢`; what it states as a rule it
        # prints as prose — "If φy is true whatever possible argument y may be,
        # then (x).φx is true" (✱10·11) carries no turnstile, and its premise is
        # the rule rather than a debt.  So the turnstile, not the catalogue's
        # kind, is what distinguishes a conditional proof from a faithful one.
        printed = item.get("printed") or ""
        asserted_categorically = "⊢" in printed
        if (
            not is_definition
            and asserted_categorically
            and item.get("kind") not in PREMISED_KINDS
        ):
            hypotheses = _hypothesised_judgements(declared.statement)
            if hypotheses:
                failed.append("T12")
                notes["T12"] = (
                    f"{base} assumes {hypotheses[0]!r}: it derives the "
                    "proposition only from a judgement the catalogue does not "
                    "establish. PM asserts this proposition categorically, so a "
                    "conditional proof of it is a step towards the derivation, "
                    "not the derivation"
                )

        reading = declarations(lean_path).get(f"{base}_reading")
        if is_definition:
            reading = None  # a Df asserts nothing, so it reads nothing
        elif reading is None:
            failed.append("T4")
            notes["T4"] = f"no `def {base}_reading` in {lean_path}"
        elif not any(
            re.search(_qualified(name), reading.statement) for name in reading_types()
        ):
            failed.append("T4")
            notes["T4"] = (
                f"{base}_reading is not typed by a printed↔AST reading structure "
                f"(accepted: {', '.join(sorted(reading_types())) or 'none'})"
            )
        else:
            printed = lean_string_after(reading.body, "printed")
            parsed_match = re.search(
                r"parsed\s*:=\s*(.+?)(?=\n\s*\w+\s*:=|\Z)", reading.body, re.S
            )
            catalogue_printed = normalise_printed(item.get("printed", ""))
            if printed is None:
                failed.append("T4")
                notes["T4"] = f"{base}_reading has no printed := PM.pmPrinted \"…\""
            elif normalise_printed(printed) != catalogue_printed:
                failed.append("T4")
                notes["T4"] = (
                    "printed reading differs from the catalogue\n"
                    f"      lean:      {normalise_printed(printed)!r}\n"
                    f"      catalogue: {catalogue_printed!r}"
                )
            elif parsed_match is None:
                failed.append("T4")
                notes["T4"] = f"{base}_reading has no parsed := field"
            elif formula is not None and normalise_formula(
                parsed_match.group(1)
            ) != normalise_formula(formula):
                failed.append("T4")
                notes["T4"] = (
                    "the reading's AST is not the formula the theorem asserts\n"
                    f"      reading: {normalise_formula(parsed_match.group(1))}\n"
                    f"      theorem: {normalise_formula(formula)}"
                )

        # The asserted formula must be PM's syntax, not Lean's.  A host `∧` or
        # `→` inside it means the statement left the object calculus.
        if formula is not None:
            host = HOST_CONNECTIVES.search(formula)
            if host:
                failed.append("T11")
                notes["T11"] = (
                    f"the asserted formula uses Lean's `{host.group(0)}` where PM "
                    "has its own connective (∼ₚ ∨ₚ ⊃ₚ ∧ₚ ≡ₚ); the statement has "
                    "slipped out of the object calculus into the host logic"
                )
            elif not PM_CONNECTIVES.search(formula) and len(formula.strip()) > 3:
                notes["T11"] = (
                    "the asserted formula contains no PM connective; check it is "
                    "object syntax and not a host-level abbreviation"
                )

        undeclared = undeclared_assumptions(item, lean_path, declared)
        if undeclared:
            failed.append("T9")
            notes["T9"] = (
                "reaches non-logical assumption(s) "
                + ", ".join(sorted(undeclared))
                + " without declaring them"
            )

        vacuity = _is_vacuous(declared.statement, declared.body)
        if vacuity:
            failed.append("T6")
            notes["T6"] = vacuity

    if evidence_failures:
        failed.append("T7")
        notes["T7"] = "; ".join(evidence_failures)

    level = item.get("formalization_level")
    structural = [criterion for criterion in failed if criterion != "T7"]
    if level is None:
        failed.append("T8")
        notes["T8"] = (
            f"no formalization_level; {REQUIRED_FORMALIZATION_LEVEL!r} is required "
            "to be promotable"
        )
    elif level == REQUIRED_FORMALIZATION_LEVEL and structural:
        failed.append("T8")
        notes["T8"] = (
            f"declares {level!r} but fails {', '.join(structural)} — a declared "
            "level may not exceed what the Lean tree exhibits"
        )
    elif level != REQUIRED_FORMALIZATION_LEVEL and not structural:
        notes["T8"] = (
            f"declares {level!r} while satisfying every structural criterion; "
            "the field understates the tree"
        )

    # An item nobody has formalised stays `prepared`; one that now satisfies
    # every criterion is promoted on the strength of the tree, not of a claim.
    if failed and recorded == TIER_PREPARED:
        tier = TIER_PREPARED
    elif "T1" in failed:
        tier = TIER_UNBUILT
    elif failed == ["T7"] or (failed and set(failed) == {"T7"}):
        tier = TIER_AWAITING
    elif failed:
        tier = TIER_TYPECHECKED
    else:
        tier = TIER_MAX
    return tier, sorted(set(failed)), notes


def duplicate_statements(records: list[dict]) -> dict[str, list[str]]:
    """Map a normalised statement to the item ids sharing it inside one file."""
    grouped: dict[tuple[str, str], list[str]] = defaultdict(list)
    for record in records:
        declared = record.get("_declaration")
        if declared is None:
            continue
        key = (declared.path, normalise_formula(declared.statement))
        grouped[key].append(record["id"])
    return {
        f"{path}::{statement[:60]}": ids
        for (path, statement), ids in grouped.items()
        if len(ids) > 1
    }


def head_commit() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True
    )
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def gather() -> list[dict]:
    """Compute every item's tier.  Returns one record per catalogue item."""
    try:
        from verify_ci_evidence import evidence_failures
    except ImportError as error:  # pragma: no cover - wiring failure must be loud
        raise SystemExit(
            "scripts/verify_ci_evidence.py is required for criterion T7: "
            f"{error}"
        ) from error

    records: list[dict] = []
    for path, batch in load_batches():
        items = batch.get("items", [])
        reasons = evidence_failures(path, batch.get("ci_evidence") or {}, items)
        for item in items:
            tier, failed, notes = compute(item, reasons)
            base = (item.get("declaration") or "").rsplit(".", 1)[-1]
            declared = declarations(item.get("lean_path") or "").get(base)
            records.append(
                {
                    "id": item.get("id"),
                    "batch": str(path.relative_to(ROOT)),
                    "recorded": item.get("formal_status"),
                    "recorded_integration": item.get("integration_status"),
                    "tier": tier,
                    "failed": failed,
                    "notes": notes,
                    "_declaration": declared,
                }
            )

    duplicates = duplicate_statements(records)
    shared_ids = {identifier for ids in duplicates.values() for identifier in ids}
    for record in records:
        if record["id"] in shared_ids and record["tier"] == TIER_MAX:
            record["tier"] = TIER_TYPECHECKED
            record["failed"] = sorted(set(record["failed"]) | {"T6"})
            record["notes"]["T6"] = (
                "statement is byte-identical to another catalogue item's in the "
                "same file"
            )
    return records


def census(records: list[dict]) -> str:
    tiers = Counter(record["tier"] for record in records)
    criteria = Counter(
        criterion for record in records for criterion in record["failed"]
    )
    lines = ["tier census:"]
    for tier, count in tiers.most_common():
        lines.append(f"  {count:5}  {tier}")
    lines.append("failed criteria (items may fail several):")
    for criterion, count in criteria.most_common():
        lines.append(f"  {count:5}  {criterion}  {CRITERIA[criterion]}")
    return "\n".join(lines)


def discrepancies(records: list[dict]) -> list[str]:
    """Recorded statuses that claim more than the Lean tree supports."""
    problems = []
    for record in records:
        recorded = record["recorded"]
        if recorded in INTENT_STATUSES and record["tier"] in INTENT_STATUSES:
            continue
        if recorded != record["tier"]:
            detail = "; ".join(
                f"{criterion}: {record['notes'][criterion]}"
                for criterion in record["failed"]
                if criterion in record["notes"]
            )
            problems.append(
                f"{record['id']} ({record['batch']}) records {recorded!r} "
                f"but the tree supports {record['tier']!r}\n    {detail}"
            )
        integration = record["recorded_integration"] or ""
        if integration.startswith("canonical-") and record["tier"] != TIER_MAX:
            problems.append(
                f"{record['id']} ({record['batch']}) records integration "
                f"{integration!r} while its tier is {record['tier']!r}"
            )
    return problems


def write_tiers(records: list[dict]) -> tuple[int, int]:
    """Rewrite catalogue statuses to the computed tiers."""
    by_batch: dict[str, list[dict]] = defaultdict(list)
    for record in records:
        by_batch[record["batch"]].append(record)

    commit = head_commit()
    changed_items = 0
    changed_files = 0
    for relative, batch_records in sorted(by_batch.items()):
        path = ROOT / relative
        batch = json.loads(path.read_text(encoding="utf-8"))
        by_id = {record["id"]: record for record in batch_records}
        touched = False
        for item in batch.get("items", []):
            record = by_id.get(item.get("id"))
            # `prepared` was once treated as an editorial marker `--write` would
            # not touch.  That deadlocked: `discrepancies()` reports an item
            # recorded as `prepared` whose tree supports more, and `--write`
            # refused to be the thing that fixed it.  The repository's principle
            # is that tiers are computed, never declared, so the computed tier
            # always applies; nothing demotes a genuinely unbuilt item, because
            # its computed tier is `prepared` too.
            if record is None:
                continue
            if item.get("formal_status") != record["tier"]:
                item["formal_status"] = record["tier"]
                touched = True
                changed_items += 1
            integration = item.get("integration_status") or ""
            if integration.startswith("canonical-") and record["tier"] != TIER_MAX:
                item["integration_status"] = "provisional-" + integration[len("canonical-"):]
                touched = True
            if record["tier"] != TIER_MAX:
                certification = {
                    "tier": record["tier"],
                    "failed_criteria": record["failed"],
                    "computed_at_commit": commit,
                }
                if item.get("certification") != certification:
                    item["certification"] = certification
                    touched = True
            elif "certification" in item:
                del item["certification"]
                touched = True
        if touched:
            path.write_text(
                json.dumps(batch, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
            changed_files += 1
    return changed_items, changed_files


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail on any discrepancy")
    parser.add_argument("--report", action="store_true", help="print the census only")
    parser.add_argument("--write", action="store_true", help="apply computed tiers")
    parser.add_argument("--json", type=Path, help="dump per-item computation")
    arguments = parser.parse_args()
    if arguments.check and arguments.write:
        parser.error("--check and --write are mutually exclusive")

    records = gather()
    if arguments.json:
        arguments.json.write_text(
            json.dumps(
                [
                    {key: value for key, value in record.items() if key != "_declaration"}
                    for record in records
                ],
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )

    if arguments.report:
        print(census(records))
        return 0

    if arguments.write:
        items, files = write_tiers(records)
        print(f"applied computed tiers to {items} items in {files} catalogues")
        return 0

    problems = discrepancies(records)
    if problems:
        print(census(records), file=sys.stderr)
        print(
            f"\n{len(problems)} catalogue items claim more than the Lean tree "
            "supports:\n",
            file=sys.stderr,
        )
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    print(f"certification tiers verified ({len(records)} items)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
