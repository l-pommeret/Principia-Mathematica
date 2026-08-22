#!/usr/bin/env python3
"""Audit direct historical/Lean dependency agreement without running Lean.

This deliberately audits the source term supplied to Lean.  GitHub CI's later
``lake build`` step remains the authority that the term was accepted by the
kernel.  Together the two checks establish, for items marked kernel-checked,
both term acceptance and agreement with the dependencies printed in PM.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
import argparse
from dataclasses import dataclass
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DECL_START = re.compile(
    r"^\s*(?:theorem|def|abbrev|inductive|structure)\s+([A-Za-z0-9_']+)\b"
)
KNOWN_BRIDGES = {"PM.Derivation.detach"}

#: PM's own abbreviated titles for ✱1·2–✱1·6, declared in
#: Principia/Deduction/PrintedNames.lean.  PM cites these propositions by title
#: inside its demonstrations — `[Taut ∼p/p]`, not `[✱1·2]` — so a proof that
#: writes `Taut` is citing ✱1·2 exactly as the printed page does.  They are
#: abbreviations, not new content: each is definitionally the numbered
#: proposition it names.
#: Names of the calculus itself — types and their evidence, not proof steps.
#: They appear in a proof term as ascriptions and anonymous constructors
#: (`⟨DerivationEvidence.star_1_2 p⟩`), and flagging them as uncited
#: dependencies would report the calculus as a dependency of every proof in it.
def catalogued_definition_names() -> set[str]:
    """PM-style Lean names of catalogued definitions.

    PM's demonstrations cite definitions in brackets — `[(✱1·01)]` — as often as
    they cite propositions, so a proof term mentioning a catalogued `Df` is
    citing the printed text, not evading the index.  Whether that citation is
    *licensed* for a given item is the printed-citation gate's question, not
    this one's.
    """
    import glob as _glob
    names: set[str] = set()
    for path in _glob.glob(str(ROOT / "metadata" / "items" / "*.json")):
        try:
            batch = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        for item in batch.get("items", []):
            if item.get("kind") not in {
                "definition", "notation-definition", "contextual-definition"
            }:
                continue
            identifier = item.get("id", "")
            match = re.search(r"✱(\d+)·(\d+)", identifier)
            if match:
                names.add(f"star_{match.group(1)}_{match.group(2)}")
    return names


CALCULUS_TYPES = {
    "PM.Derivation", "PM.DerivationEvidence", "PM.Elementary", "PM.Formation",
    "PM.RealContext", "PM.RealVar", "PM.RealType",
}

PRINTED_TITLES = {
    "PM.Derivation.Taut": "PM.Derivation.star_1_2",
    "PM.Derivation.Add": "PM.Derivation.star_1_3",
    "PM.Derivation.Perm": "PM.Derivation.star_1_4",
    "PM.Derivation.Assoc": "PM.Derivation.star_1_5",
    "PM.Derivation.Sum": "PM.Derivation.star_1_6",
}
PRIMITIVE_DECLARATION_KINDS = {
    "primitive-inference-rule",
    "primitive-function-inference-rule",
    "primitive-formation-rule",
}
KNOWN_SYNTAX_INFRASTRUCTURE = {
    # Lean's proof constructors for the ambient logic are carrier
    # infrastructure, not historical PM theorem citations.
    "Classical.choice",
    "Classical.byContradiction",
    "Classical.byCases",
    "Classical.em",
    "False.elim",
    "Fin.elim0",
    "True.intro",
    "Eq.symm",
    "Eq.mpr",
    "Eq.mp",
    # Kernel arithmetic reassociation used internally by the typed finite
    # relation-power infrastructure (✱91), not a historical PM citation.
    "Nat.add_assoc",
    # Kernel successor on natural numbers, used for ramified order arithmetic.
    "Nat.succ",
    "RightGenerated.base",
    "RightGenerated.step",
    "And.left",
    "And.right",
    "Iff.rfl",
    "Or.inl",
    "Or.inr",
    "List.cons_ne_nil",
    "Bool.or_eq_true",
    "Iff.rfl",
    "PM.Elementary",
    # Extensional empty-class constant used as carrier infrastructure by the
    # typed ✱60 reconstruction; it is not a historical theorem dependency.
    "PM.Architecture.Star60Kernel.Empty",
    "PM.Architecture.Star60Kernel.Singleton",
    # Local type-cardinal carrier, not the unrelated PM2 ✱103 source object.
    "Star116SecondKernel.CardinalClass",
    "PM.Formation.ofElementary",
    "Elementary.schemaInstance",
    "NormalizesScoped.disjCongr",
    "NormalizesScoped.disjLeftReverse",
    "NormalizesScoped.disjRightReverse",
    "NormalizesScoped.negCongr",
    "NormalizesScoped.negAlways",
    "NormalizesScoped.negSometimes",
    "NormalizesScoped.star_9_05_disj_independent_left",
    "NormalizesScoped.star_9_05_disj_independent_right",
    "PM.FirstOrder.neg",
    "PM.FirstOrder.always",
    "PM.FirstOrder.sometimes",
    "PM.FirstOrder.disjRightElementary",
    "PM.FirstOrder.disjElementaryLeft",
    "PM.FirstOrder.disjAlwaysSometimes",
    "PM.FirstOrder.disjSometimesAlways",
    "PM.Apparent.openHead",
    "PM.Apparent.elementaryValue",
    # Typed constructors used by the function-formation results ✱9·61–·62.
    # They build indexed syntax and carry no historical theorem edge.
    "PM.Apparent.disj",
    "PM.FirstOrder.disjRightMatrix",
    # Capture-safe real/apparent scope operations and syntactic occurrence
    # predicates.  These form and inspect indexed syntax; they are not PM
    # theorem dependencies.
    "Apparent.Significant",
    "Apparent.significant",
    "Apparent.abstractRealHead",
    "Apparent.openRealHead",
    "Apparent.openRealHead_abstractRealHead",
    "NormalizesScopedAt.disjCongr",
    "OrderedAssertion.elementary",
    # A fixed assigned-order target is a carrier spelling, not a historical
    # theorem dependency.  ✱9·3's actual proof dependency is the separately
    # indexed closed matrix-schema judgement below.
    "FirstOrderQ259.star_9_3_target",
    "Star921MatrixKernel.star_9_3_ordered_target",
    # Formula-level syntax operations: substitution, renaming, instantiation,
    # casting and the ✱11 stability helpers built from them. They form and
    # inspect indexed syntax and can never be a PM citation. Widening the
    # audited tiers brought the ✱11 proofs into scope, which is how these
    # surfaced; they were always carrier infrastructure.
    "Formula.instantiate",
    "Formula.substitute_cast",
    "Formula.substitute_of_pointwise",
    "Formula.substitute_eq_self",
    "Formula.closed_substitute",
    "Formula.rename_substitute_of_pointwise",
    "Formula.weakenReal_cast",
    "Formula.star11AlwaysStable",
    "Formula.star11AlwaysStable_weakenReal_instantiate",
    "Formula.star11SometimesStable",
    "Formula.star11SometimesStableRaw",
    "Formula.star11SometimesStableRaw_normalize",
    "Formula.star11SometimesStable_weakenReal_instantiate",
    "Formula.star11FixSecond",
    "Formula.star11FixSecond_implication",
    "Formula.star11Implication_weakenReal_instantiate",
    "Formula.star11CastCongr",
    "Formula.star11FixSecond_shift",
    # Assertion-level cast on a derivation: carrier plumbing, never a citation.
    "Derivation.castAssertion",
}

# Theorem-specific records may name fields after mathematical operations
# (`product`, `sum`, ...).  A field label in a structure literal is syntax,
# not a reference to an unrelated declaration sharing that short name.
STRUCTURE_FIELD_ASSIGNMENT = re.compile(r"\b([A-Za-z_][A-Za-z0-9_']*)\s*:=")

# Closed, theorem-specific packaging definitions are transparent nodes in the
# historical graph.  Expand their bodies rather than treating the package as
# an extra PM proposition.
TRANSPARENT_DEPENDENCY_WRAPPERS = {
    "Star10Q271Prerequisites.star_10_33_composition": (
        "Principia/Architecture/Star10Q271Prerequisites.lean",
        "PM.Architecture.Star10Q271Prerequisites.star_10_33_composition",
    ),
}

LEAN_IDENTIFIER = re.compile(
    r"(?<![A-Za-z0-9_'])([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*)(?![A-Za-z0-9_'.])"
)


@dataclass(frozen=True)
class DependencyIndex:
    """Lookup tables allowing one lexical scan of each audited declaration."""

    candidates: frozenset[str]
    by_short: dict[str, frozenset[str]]
    by_suffix: dict[str, frozenset[str]]
    realizations: frozenset[str]

    @classmethod
    def build(cls, declarations: dict[str, str], aliases: dict) -> "DependencyIndex":
        realizations = frozenset(aliases["lean_realizations"])
        candidates = frozenset(set(declarations) | set(realizations) | KNOWN_BRIDGES)
        by_short: dict[str, set[str]] = defaultdict(set)
        by_suffix: dict[str, set[str]] = defaultdict(set)
        for name in candidates:
            by_short[name.rsplit(".", 1)[-1]].add(name)
            parts = name.split(".")
            # Exact names are looked up directly. Only qualified shortened
            # suffixes belong here; a final component is handled by by_short.
            for start in range(1, len(parts) - 1):
                by_suffix[".".join(parts[start:])].add(name)
        return cls(
            candidates,
            {key: frozenset(values) for key, values in by_short.items()},
            {key: frozenset(values) for key, values in by_suffix.items()},
            realizations,
        )


class DependencyError(ValueError):
    pass


def auditable_declaration(item: dict) -> str | None:
    """Return the item's Lean declaration, or exclude an unformalized item."""
    declaration = item.get("declaration")
    if declaration:
        return declaration
    if "formalization_level" in item:
        raise DependencyError(
            f"{item['id']}: formalization_level is present but declaration is missing"
        )
    # Removing Principia/Architecture legitimately left catalogued propositions
    # without a Lean declaration.  They are not proved nodes, so dependency
    # auditing must ignore them rather than count them as conforming.
    return None


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments from source text.

    Dependency extraction concerns the term accepted by Lean, not editorial
    prose adjacent to it.  Keep strings intact because printed-reading
    declarations are never audited as theorem bodies.
    """
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth:
            index += 1
        elif source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                break
            result.append("\n")
            index = newline + 1
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


def pm_order(item_id: str) -> tuple[int, int, Fraction]:
    match = re.fullmatch(r"PM([0-9]+):✱([0-9]+)·([0-9]+)", item_id)
    if not match:
        raise DependencyError(f"cannot order PM item ID {item_id}")
    volume, integral, fractional = match.groups()
    return int(volume), int(integral), Fraction(int(fractional), 10 ** len(fractional))


def load_items(root: Path = ROOT) -> list[dict]:
    result = []
    for path in sorted((root / "metadata/items").glob("*.json")):
        batch = json.loads(path.read_text(encoding="utf-8"))
        for item in batch["items"]:
            record = dict(item)
            for inherited in ("parser_status", "parser_evidence"):
                if inherited not in record and inherited in batch:
                    record[inherited] = batch[inherited]
            record["_metadata_path"] = str(path.relative_to(root))
            result.append(record)
    return result


def load_assumptions(root: Path = ROOT) -> dict[str, dict]:
    """Load the reviewed non-logical-assumption catalogue.

    This catalogue is deliberately independent of theorem nodes: an axiom or
    scoped hypothesis is not smuggled into the historical proof graph as if it
    were an earlier proposition.
    """
    payload = json.loads((root / "metadata/assumptions.json").read_text(encoding="utf-8"))
    if payload.get("schema_version") != 1 or not isinstance(payload.get("assumptions"), list):
        raise DependencyError("invalid non-logical assumption registry header")
    result: dict[str, dict] = {}
    required = {
        "id", "label", "volume", "loci", "status", "editorial_note",
        "lean_parameter_types",
    }
    allowed_statuses = {
        "catalogued-not-yet-formalized",
        "catalogued-locus-pending-source-audit",
        "formalized-explicit-hypothesis",
    }
    for record in payload["assumptions"]:
        if not isinstance(record, dict) or not required <= record.keys():
            raise DependencyError(f"incomplete non-logical assumption record {record!r}")
        identifier = record["id"]
        if identifier in result:
            raise DependencyError(f"duplicate non-logical assumption ID {identifier}")
        if not re.fullmatch(r"PM[123]:[A-Z][A-Z0-9_-]*", identifier):
            raise DependencyError(f"invalid non-logical assumption ID {identifier!r}")
        if record["volume"] != int(identifier[2]) or record["status"] not in allowed_statuses:
            raise DependencyError(f"incoherent non-logical assumption record {identifier}")
        if not isinstance(record["loci"], list) or not record["loci"]:
            raise DependencyError(f"non-logical assumption {identifier} has no locus")
        parameter_types = record["lean_parameter_types"]
        if (not isinstance(parameter_types, list) or
                len(parameter_types) != len(set(parameter_types)) or
                any(not isinstance(name, str) or not re.fullmatch(
                    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+", name
                ) for name in parameter_types)):
            raise DependencyError(
                f"non-logical assumption {identifier} has invalid Lean parameter types"
            )
        result[identifier] = record
    return result


def assumption_closure(items: list[dict], registry: dict[str, dict]) -> dict[str, dict[str, list[str]]]:
    """Validate and compute direct/inherited assumptions through PM edges.

    Metadata remains backwards compatible: an item declaring neither field has
    no assumptions. Once one field is introduced both are required, making the
    inherited closure an auditable assertion rather than generated decoration.
    """
    by_id = {item["id"]: item for item in items}
    visiting: set[str] = set()
    memo: dict[str, dict[str, list[str]]] = {}

    def visit(item_id: str) -> dict[str, list[str]]:
        if item_id in memo:
            return memo[item_id]
        if item_id in visiting:
            raise DependencyError(f"cycle while computing assumption closure at {item_id}")
        visiting.add(item_id)
        item = by_id[item_id]
        has_direct = "direct_assumptions" in item
        has_inherited = "inherited_assumptions" in item
        if has_direct != has_inherited:
            raise DependencyError(
                f"{item_id}: direct_assumptions and inherited_assumptions must be declared together"
            )
        direct = item.get("direct_assumptions", [])
        declared_inherited = item.get("inherited_assumptions", [])
        if not isinstance(direct, list) or not isinstance(declared_inherited, list):
            raise DependencyError(f"{item_id}: assumption fields must be lists")
        if len(direct) != len(set(direct)) or len(declared_inherited) != len(set(declared_inherited)):
            raise DependencyError(f"{item_id}: duplicate non-logical assumption ID")
        unknown = (set(direct) | set(declared_inherited)) - registry.keys()
        if unknown:
            raise DependencyError(f"{item_id}: unknown non-logical assumptions {sorted(unknown)}")
        inherited: set[str] = set()
        for dependency in item.get("normalized_dependencies", []):
            if dependency not in by_id:
                raise DependencyError(f"{item_id}: unknown PM dependency {dependency}")
            dependency_assumptions = visit(dependency)
            inherited.update(dependency_assumptions["effective"])
        if set(declared_inherited) != inherited:
            raise DependencyError(
                f"{item_id}: inherited assumptions {sorted(declared_inherited)} "
                f"!= dependency closure {sorted(inherited)}"
            )
        if set(direct) & inherited:
            raise DependencyError(f"{item_id}: an assumption cannot be both direct and inherited")
        result = {
            "direct": sorted(direct),
            "inherited": sorted(inherited),
            "effective": sorted(set(direct) | inherited),
        }
        memo[item_id] = result
        visiting.remove(item_id)
        return result

    for identifier in by_id:
        visit(identifier)
    return memo


def declaration_body(path: Path, declaration: str) -> str:
    """Return a declaration through the line before the next declaration."""
    short = declaration.rsplit(".", 1)[-1]
    lines = path.read_text(encoding="utf-8").splitlines()
    start = None
    for index, line in enumerate(lines):
        match = DECL_START.match(line)
        if match and match.group(1) == short:
            start = index
            break
    if start is None:
        raise DependencyError(f"declaration {declaration} not found in {path}")
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if DECL_START.match(lines[index]) or re.match(r"^\s*end\b", lines[index]):
            end = index
            break
    return "\n".join(lines[start:end])


def declaration_header(body: str) -> str:
    """Return the declaration portion before its value/proof.

    This deliberately remains a source-level audit.  A scoped non-logical
    assumption must occur in a named ordinary parameter of the declaration;
    mentioning it only in the proof body, or resolving it through an instance,
    must not satisfy the gate.
    """
    clean = strip_lean_comments(body)
    if ":=" in clean:
        return clean.split(":=", 1)[0]
    match = re.search(r"(?m)^\s*where\s*$", clean)
    return clean[:match.start()] if match else clean


def verify_assumption_parameters(
    item: dict,
    usage: dict[str, list[str]],
    registry: dict[str, dict],
    body: str,
) -> list[dict[str, str]]:
    """Match every effective assumption to an explicit Lean parameter.

    Metadata names the parameter and its registered base type. Requiring the
    exact effective closure makes inherited assumptions visible in descendant
    theorem signatures instead of allowing them to disappear into proof terms.
    """
    effective = set(usage["effective"])
    bindings = item.get("assumption_parameters")
    if not effective:
        if bindings not in (None, {}):
            raise DependencyError(
                f"{item['id']}: assumption_parameters declared with empty assumption closure"
            )
        return []
    if not isinstance(bindings, dict) or set(bindings) != effective:
        actual = sorted(bindings) if isinstance(bindings, dict) else []
        raise DependencyError(
            f"{item['id']}: assumption parameter bindings {actual} "
            f"!= effective assumptions {sorted(effective)}"
        )

    header = declaration_header(body)
    verified: list[dict[str, str]] = []
    seen_parameters: set[str] = set()
    for assumption in sorted(effective):
        binding = bindings[assumption]
        if not isinstance(binding, dict) or set(binding) != {"parameter", "lean_type"}:
            raise DependencyError(f"{item['id']}: invalid binding for {assumption}")
        parameter = binding["parameter"]
        lean_type = binding["lean_type"]
        if (not isinstance(parameter, str) or
                not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", parameter)):
            raise DependencyError(f"{item['id']}: invalid parameter name for {assumption}")
        if parameter in seen_parameters:
            raise DependencyError(f"{item['id']}: assumption parameter {parameter} is reused")
        seen_parameters.add(parameter)
        allowed = registry[assumption]["lean_parameter_types"]
        if lean_type not in allowed:
            raise DependencyError(
                f"{item['id']}: Lean type {lean_type!r} is not registered for {assumption}"
            )
        # Only `(name : Type ...)` counts. In particular `[name : Type]`, a
        # body-only occurrence, or an anonymous parameter cannot pass.
        pattern = re.compile(
            rf"\(\s*{re.escape(parameter)}\s*:\s*"
            rf"{re.escape(lean_type)}(?![A-Za-z0-9_'.])"
        )
        if not pattern.search(header):
            raise DependencyError(
                f"{item['id']}: no explicit scoped parameter "
                f"({parameter} : {lean_type} ...) in Lean declaration header"
            )
        verified.append({
            "assumption": assumption,
            "parameter": parameter,
            "lean_type": lean_type,
        })
    return verified


def _occurs(body: str, name: str) -> bool:
    # Generic helper names such as ``derive`` are not stable dependency
    # identities.  Their fully-qualified or explicitly registered short alias
    # must occur exactly; otherwise unrelated closed-kernel witnesses sharing
    # the helper name are spuriously recorded as dependencies.
    variants = (name,) if name.endswith(".derive") else (name, name.rsplit(".", 1)[-1])
    short = name.rsplit(".", 1)[-1]
    body_without_field_labels = re.sub(
        rf"\b{re.escape(short)}\s*:=", "", body
    )
    return any(re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(variant)}(?![A-Za-z0-9_'])", body)
               if "." in variant else
               re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(variant)}(?![A-Za-z0-9_'])",
                         body_without_field_labels)
               for variant in variants)


def reject_unindexed_references(item: dict, body: str, candidates: set[str]) -> None:
    """Reject conspicuous theorem calls that could evade the PM index.

    This is intentionally conservative source auditing, not an elaborator.
    Qualified constants and PM-style theorem names in the proof term must be
    represented by the dependency catalogue. GitHub's Lean step subsequently
    supplies the authoritative elaborated/kernel check.
    """
    proof = body.split(":=", 1)[1] if ":=" in body else ""
    # A printed title stands for the numbered proposition it abbreviates, so it
    # is indexed whenever that proposition is.
    candidates = set(candidates) | {
        title for title, numbered in PRINTED_TITLES.items()
        if numbered in candidates or numbered.rsplit(".", 1)[-1] in
        {name.rsplit(".", 1)[-1] for name in candidates}
    }
    indexed_short = {name.rsplit(".", 1)[-1] for name in candidates}
    for token in re.findall(r"\b[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+", proof):
        # The same allowlist the two checks below already consult. Kernel
        # carrier names such as Nat.succ can never be a PM citation, and
        # demanding an index entry for one reports a defect that does not
        # exist. Widening the audited tiers brought proofs into scope that use
        # them, which is how the omission surfaced.
        if token in CALCULUS_TYPES or token in KNOWN_SYNTAX_INFRASTRUCTURE:
            continue
        if token not in candidates and token.rsplit(".", 1)[-1] not in indexed_short:
            raise DependencyError(f"{item['id']}: unindexed qualified Lean reference {token}")
    definitions = catalogued_definition_names()
    for token in re.findall(r"\bstar_[0-9]+(?:_[0-9]+)+\b", proof):
        if token in definitions:
            continue
        if token not in indexed_short:
            raise DependencyError(f"{item['id']}: unindexed PM-style Lean reference {token}")


def lean_identifier_tokens(body: str) -> list[tuple[str, bool]]:
    """Return non-field identifiers and whether each is qualified."""
    tokens: list[tuple[str, bool]] = []
    for match in LEAN_IDENTIFIER.finditer(body):
        token = match.group(1)
        remainder = body[match.end():]
        is_field_label = "." not in token and re.match(r"\s*:=", remainder) is not None
        if not is_field_label:
            tokens.append((token, "." in token))
    return tokens


def extract_lean_dependencies(
    item: dict, declarations: dict[str, str], root: Path = ROOT,
    dependency_index: DependencyIndex | None = None,
) -> list[str]:
    declaration = auditable_declaration(item)
    if declaration is None:
        return []
    if (item["kind"] in PRIMITIVE_DECLARATION_KINDS or
            ".OrderedAssertion." in declaration):
        # These are inductive constructors, hence have no declaration body
        # and no prior dependencies to extract.
        return []
    body = strip_lean_comments(
        declaration_body(root / item["lean_path"], declaration)
    )
    # A proof written with PM's own abbreviated title cites the numbered
    # proposition that title names: `[Taut ∼p/p]` is a citation of ✱1·2, exactly
    # as the printed demonstration writes it.  Normalising here keeps the
    # extracted dependencies in the catalogue's vocabulary.
    for title, numbered in PRINTED_TITLES.items():
        body = body.replace(title, numbered)
    for token, (path, wrapper_declaration) in TRANSPARENT_DEPENDENCY_WRAPPERS.items():
        if token in body:
            body += "\n" + strip_lean_comments(
                declaration_body(root / path, wrapper_declaration)
            )
    aliases = json.loads((root / "metadata/dependency_aliases.json").read_text(encoding="utf-8"))
    realizations = aliases["lean_realizations"]
    dependency_index = dependency_index or DependencyIndex.build(declarations, aliases)
    candidates = dependency_index.candidates
    reject_unindexed_references(
        item, body,
        candidates | KNOWN_SYNTAX_INFRASTRUCTURE |
        set(TRANSPARENT_DEPENDENCY_WRAPPERS),
    )
    # Scan identifiers once. A field label in a structure literal is syntax,
    # not an unqualified reference. Qualified identifiers are tokens in their
    # own right, so `Foo.bar` deliberately no longer matches `Foo.bar.baz`.
    tokens = lean_identifier_tokens(body)

    found: set[str] = set()
    declared_realizations = dependency_index.realizations.intersection(
        item.get("lean_dependencies", [])
    )
    for token, qualified in tokens:
        if token in KNOWN_SYNTAX_INFRASTRUCTURE:
            continue
        if qualified:
            if token in candidates:
                found.add(token)
            continue
        for name in dependency_index.by_short.get(token, ()):
            # Generic `.derive` helpers require their stable qualified name.
            if name.endswith(".derive"):
                continue
            # Realization aliases normally denote their exact registered
            # spelling. An explicitly declared dependency retains the legacy
            # reviewed short-name escape hatch.
            if name not in dependency_index.realizations or name in declared_realizations:
                found.add(name)
    found.discard(declaration)
    # Resolve shortened qualified projections/constructors only when their
    # final component identifies a unique reviewed candidate. Fully qualified
    # tokens are already handled above and must not spuriously select another
    # declaration with the same short name (for example the Star1 wrapper and
    # the primitive Derivation constructor).
    qualified_tokens = set(re.findall(
        r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+", body
    ))
    for token in qualified_tokens:
        if token in KNOWN_SYNTAX_INFRASTRUCTURE:
            continue
        if token in candidates:
            continue
        suffix_matches = dependency_index.by_suffix.get(token, ())
        if len(suffix_matches) == 1:
            match_name = next(iter(suffix_matches))
            if match_name != declaration:
                found.add(match_name)
        # A qualified spelling in a different namespace is not the indexed
        # theorem merely because its final component is equal.  In particular
        # a secondary `Prop` reading must not become an edge to the primary PM
        # judgment that happens to share `star_N_M` as its short name.
    # Alias tables may deliberately contain both a namespace-relative spelling
    # and its fully qualified spelling for the same reviewed realization.  A
    # single occurrence must yield one graph edge, preferring the exact,
    # longest spelling that occurs in the declaration body.
    realizations = aliases["lean_realizations"]
    canonical: dict[tuple[str, str], str] = {}
    for name in found:
        resolution = declarations.get(name, realizations.get(name, name))
        key = (name.rsplit(".", 1)[-1], resolution)
        current = canonical.get(key)
        if current is None or (name in body, len(name)) > (current in body, len(current)):
            canonical[key] = name
    return sorted(canonical.values())


def normalize(item: dict, lean_dependencies: list[str], declaration_to_id: dict[str, str], root: Path = ROOT) -> list[str]:
    aliases = json.loads((root / "metadata/dependency_aliases.json").read_text(encoding="utf-8"))
    realizations = aliases["lean_realizations"]
    normalized: list[str] = []
    for name in lean_dependencies:
        if name == "PM.Derivation.detach":
            choices = set(aliases["bridges"][name]["resolves_to"])
            justified = [bridge.get("pm_dependency")
                for bridge in item.get("dependency_justifications", [])
                if bridge.get("kind") == "metalinguistic-rule-selection"
                and bridge.get("lean_dependency") == name
                and bridge.get("pm_dependency") in choices]
            selected = justified or [dep for dep in item.get("printed_dependencies", []) if dep in choices]
            if len(selected) != 1:
                raise DependencyError(f"{item['id']}: detach must resolve to exactly one printed primitive rule")
            normalized.extend(selected)
        elif name in declaration_to_id or name in realizations:
            dependency = declaration_to_id.get(name, realizations.get(name))
            # A primitive wrapper merely realizes the current printed Pp.; it
            # does not acquire a historical self-dependency.
            if dependency != item["id"]:
                normalized.append(dependency)
        else:
            raise DependencyError(f"{item['id']}: no PM resolution for Lean dependency {name}")
    for bridge in item.get("dependency_justifications", []):
        if bridge.get("kind") == "metalinguistic-rule-selection":
            if (bridge.get("lean_dependency") != "PM.Derivation.detach" or
                    bridge.get("pm_dependency") not in normalized or not bridge.get("evidence")):
                raise DependencyError(f"{item['id']}: invalid detachment justification {bridge!r}")
            continue
        if bridge.get("kind") != "definitional-reading" or bridge.get("pm_dependency") != "PM1:✱1·01":
            raise DependencyError(f"{item['id']}: unsupported normalization justification {bridge!r}")
        if not bridge.get("evidence"):
            raise DependencyError(f"{item['id']}: normalization justification lacks evidence")
        normalized.append(bridge["pm_dependency"])
    return sorted(set(normalized))


def verify_dependency_alignment(item: dict, normalized: list[str], root: Path = ROOT) -> None:
    """Require exact printed closure, or an exact reviewed relaxation record."""
    printed = set(item["printed_dependencies"])
    normalized_set = set(normalized)
    relaxation = item.get("historical_dependency_relaxation")
    if relaxation is None:
        if printed != normalized_set:
            raise DependencyError(
                f"{item['id']}: printed dependencies {item['printed_dependencies']} "
                f"!= normalized Lean dependencies {normalized}"
            )
        return
    if not isinstance(relaxation, dict):
        raise DependencyError(f"{item['id']}: invalid historical dependency relaxation")
    required = {
        "classification", "added_beyond_print", "printed_but_unused",
        "strict_attempt_evidence", "editorial_note",
    }
    if not required <= relaxation.keys() or relaxation["classification"] != "relaxed-closure":
        raise DependencyError(f"{item['id']}: incomplete historical dependency relaxation")
    added = sorted(normalized_set - printed)
    unused = sorted(printed - normalized_set)
    if relaxation["added_beyond_print"] != added:
        raise DependencyError(
            f"{item['id']}: declared added dependencies "
            f"{relaxation['added_beyond_print']} != {added}"
        )
    if relaxation["printed_but_unused"] != unused:
        raise DependencyError(
            f"{item['id']}: declared unused printed dependencies "
            f"{relaxation['printed_but_unused']} != {unused}"
        )
    evidence = root / relaxation["strict_attempt_evidence"]
    if (not relaxation["editorial_note"] or not evidence.is_file() or
            not relaxation["strict_attempt_evidence"].startswith("reviews/")):
        raise DependencyError(f"{item['id']}: invalid relaxation evidence")


def audit_item(
    item: dict, *, items: list[dict], declarations: dict[str, str], order: dict[str, tuple],
    assumptions: dict[str, dict], assumption_usage: dict[str, dict[str, list[str]]], root: Path,
    dependency_index: DependencyIndex | None = None,
) -> tuple[list[dict], list[dict], list[dict]]:
    """Audit one kernel-checked declaration without masking sibling failures."""
    declaration = auditable_declaration(item)
    if declaration is None:
        return [], [], []
    for field in ("printed_dependencies", "lean_dependencies", "normalized_dependencies"):
        if field not in item or not isinstance(item[field], list):
            raise DependencyError(f"{item['id']}: missing dependency field {field}")
    body = (declaration_body(root / item["lean_path"], declaration)
            if (assumption_usage[item["id"]]["effective"] and
                ".OrderedAssertion." not in declaration) else "")
    verified_parameters = verify_assumption_parameters(
        item, assumption_usage[item["id"]], assumptions, body
    )
    actual = extract_lean_dependencies(item, declarations, root, dependency_index)
    if sorted(item["lean_dependencies"]) != actual:
        raise DependencyError(
            f"{item['id']}: Lean dependencies differ: metadata={sorted(item['lean_dependencies'])}, extracted={actual}"
        )
    normalized = normalize(item, actual, declarations, root)
    if sorted(set(item["normalized_dependencies"])) != normalized:
        raise DependencyError(f"{item['id']}: normalized metadata {item['normalized_dependencies']} != {normalized}")
    verify_dependency_alignment(item, normalized, root)
    edges = []
    for dependency in normalized:
        if dependency not in order:
            raise DependencyError(f"{item['id']}: unknown PM dependency {dependency}")
        if order[dependency] >= order[item["id"]]:
            raise DependencyError(f"{item['id']}: dependency {dependency} is not earlier in the audited corpus")
        edges.append({"from": item["id"], "to": dependency})
    return (
        edges,
        [{"from": item["id"], "to": dependency} for dependency in actual],
        [{"item": item["id"], **evidence} for evidence in verified_parameters],
    )


def audit(root: Path = ROOT, *, report_all: bool = False) -> dict:
    items = load_items(root)
    declared_items = []
    declarations = {}
    for item in items:
        declaration = auditable_declaration(item)
        if declaration is None:
            continue
        declared_items.append(item)
        declarations[declaration] = item["id"]
    assumptions = load_assumptions(root)
    assumption_usage = assumption_closure(items, assumptions)
    # Both tiers are audited, not just the topmost.
    #
    # An awaiting-ci item is one the tree already supports in full; only the CI
    # record is missing. Its dependency structure is therefore exactly as
    # checkable as a kernel-checked one, and auditing it is a strengthening --
    # 129 declarations rather than 3 at the time this was widened.
    #
    # It also removes a deadlock. Recomputing tiers empties the kernel-checked
    # frontier whenever the tree has moved past the last CI run, which is the
    # normal state of a repository mid-work. The audit then covered nothing,
    # the coverage floor refused a vacuous pass, CI could not go green, and no
    # green run existed to re-certify anything. Auditing the frontier the tree
    # supports breaks that circle without lowering any standard.
    AUDITED_TIERS = ("kernel-checked", "awaiting-ci")
    checked = [
        item for item in declared_items
        if item.get("formal_status") in AUDITED_TIERS
    ]
    order = {item["id"]: pm_order(item["id"]) for item in items}
    aliases = json.loads((root / "metadata/dependency_aliases.json").read_text(encoding="utf-8"))
    dependency_index = DependencyIndex.build(declarations, aliases)
    for alias, resolutions in aliases["aliases"].items():
        if not resolutions:
            raise DependencyError(f"alias {alias} has an empty PM resolution")
        try:
            for resolution in resolutions:
                pm_order(resolution)
        except DependencyError as error:
            raise DependencyError(f"alias {alias} has an invalid PM resolution") from error
    for alias, scopes in aliases.get("historical_scopes", {}).items():
        if alias not in aliases["aliases"] or not isinstance(scopes, list) or not scopes:
            raise DependencyError(f"invalid historical alias scope for {alias}")
        for scope in scopes:
            if (not scope.get("evidence") or not scope.get("candidates") or
                    any(candidate not in aliases["aliases"][alias]
                        for candidate in scope["candidates"])):
                raise DependencyError(f"invalid historical alias scope entry for {alias}")
            for boundary in ("from", "before"):
                if boundary in scope:
                    try:
                        pm_order(scope[boundary])
                    except DependencyError as error:
                        raise DependencyError(
                            f"invalid {boundary} boundary for alias {alias}"
                        ) from error
    edges = []
    lean_edges = []
    assumption_parameter_evidence = []
    errors = []
    for item in checked:
        try:
            item_edges, item_lean_edges, item_assumption_evidence = audit_item(
                item, items=items, declarations=declarations, order=order,
                assumptions=assumptions, assumption_usage=assumption_usage, root=root,
                dependency_index=dependency_index,
            )
            edges.extend(item_edges)
            lean_edges.extend(item_lean_edges)
            assumption_parameter_evidence.extend(item_assumption_evidence)
        except DependencyError as error:
            if not report_all:
                raise
            errors.append(str(error))
    graph = {
        "schema_version": 1,
        "coverage": {
            "status": "kernel-checked-items-only",
            "audited_items": len(checked),
            "total_metadata_items": len(items),
        },
        "nodes": [{"id": item["id"], "kind": item["kind"], "formal_status": item["formal_status"]}
                  for item in items],
        "historical_graph": {"edges": edges},
        "lean_graph": {"edges": lean_edges},
        "nonlogical_assumptions": {
            "coverage": {
                "status": "metadata-and-lean-signature-audited-for-kernel-checked-items",
                "lean_parameter_detection": "explicit-named-ordinary-parameters",
            },
            "registry": list(assumptions.values()),
            "direct_edges": [
                {"from": item_id, "to": assumption}
                for item_id, usage in assumption_usage.items()
                for assumption in usage["direct"]
            ],
            "inherited_edges": [
                {"from": item_id, "to": assumption}
                for item_id, usage in assumption_usage.items()
                for assumption in usage["inherited"]
            ],
            "lean_parameter_evidence": assumption_parameter_evidence,
        },
        # Kept as a small compatibility convenience for downstream readers.
        "edges": edges,
    }
    if report_all:
        graph["errors"] = errors
    return graph


def report_all(root: Path = ROOT) -> list[str]:
    """Collect dependency errors for every independently auditable item."""
    return audit(root, report_all=True).get("errors", [])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--report-all", action="store_true",
        help="report every independently auditable dependency error",
    )
    options = parser.parse_args()
    try:
        if options.report_all:
            errors = report_all()
            if errors:
                print("\n".join(errors), file=sys.stderr)
                raise SystemExit(1)
            graph = audit()
            print(f"dependency checks passed ({graph['coverage']['audited_items']} kernel-checked items, {len(graph['edges'])} edges)")
            return
        graph = audit()
    except (DependencyError, OSError, json.JSONDecodeError) as error:
        print(f"dependency error: {error}", file=sys.stderr)
        raise SystemExit(1)
    print(f"dependency checks passed ({graph['coverage']['audited_items']} kernel-checked items, {len(graph['edges'])} edges)")


if __name__ == "__main__":
    main()
