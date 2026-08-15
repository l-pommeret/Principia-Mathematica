# Certification tiers

A tier is *derived*, never asserted. The canonical result is
`docs/certification_registry.json`, generated only by
`scripts/derive_certification_registry.py --write`. Its `--check` mode reruns
the gates and requires byte-for-byte identity with the stored file. A change to
an item's stored tier is therefore rejected even when it is valid JSON.

`scripts/verify_certification_tier.py` is the transitional gate for the current
catalogue, in which `formal_status`, `formalization_level` and `certification`
are still duplicated into 6,203 items. It compares those claims to the tree.
The derived registry goes further: it erases those fields before evaluating an
item, so a conclusion cannot influence its own derivation.

## The standard: ✱1–✱5

The reference is `Principia/FirstEdition/Volume1/Part1/SectionA/Star2.lean`:

```lean
def star_2_01_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ ∼p . ⊃ . ∼p"
  parsed := (p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p
  scopeReading := "The single dots delimit p ⊃ ∼p as antecedent; ∼p is consequent."

theorem star_2_01 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p) :=
  PM.Derivation.star_1_2 (∼ₚ p)
```

Three things hold at once. The printed formula of the catalogue appears verbatim
in the Lean source. It is tied to an abstract syntax tree. And the theorem's
statement *is* a judgement of `PM.Derivation` — an inductive relation whose six
constructors are the six printed primitive propositions of ✱1 — over exactly
that tree, proved by applying those constructors.

Nothing in that theorem is true for a reason other than the derivation.

## Trust boundary: facts and conclusions

The distinction is whether editing a field may legitimately change what the
gates observe, not whether a human or an agent happened to type it.

| Facts supplied to the gates | Why they are facts |
|---|---|
| `id`, `kind`, `printed`, edition/volume, printed page, scan leaf and witness digests | identity and transcription from the printed source |
| `lean_path`, `declaration`, `formal_scope` | the concrete formal target proposed for inspection; existence, kind and reachability are then checked |
| `demonstration_provenance`, `printed_dependencies`, `normalized_dependencies`, `lean_dependencies` | editorial evidence about the printed demonstration and the proposed correspondence |
| `direct_assumptions`, `inherited_assumptions`, `non_logical_assumptions` | explicit declarations of non-logical hypotheses; T9 checks them against what the proof reaches |
| batch `ci_evidence` (`commit`, run URL, conclusion) | an external attestation; T7 derives whether it resolves, is ancestral, successful and fresh |
| parser evidence and an integration/blocking reason | reviewable evidence or routing input; a `*-status` that merely summarizes it should ultimately be derived |

The following are conclusions and must not be accepted from an item:

- `formalization_level`;
- `formal_status` / `certification_tier`;
- `certification.tier`, `certification.failed_criteria` and
  `certification.computed_at_commit`;
- whether an integration may carry the `canonical-` rather than
  `provisional-` prefix;
- any census, coverage percentage, or site badge computed from those values.

`integration_status` currently mixes a factual routing reason (for example an
architecture blocker) with the derived `canonical-/provisional-` prefix. The
migration must split those two meanings rather than copy the mixed field into
the new registry.

## The criteria

| | Criterion | Enforced by |
|---|---|---|
| T1 | `lean_path` is inside the import closure of `Principia.lean` | `verify_certification_tier.py` |
| T2 | `declaration` resolves to a `theorem` in that file | `verify_certification_tier.py` |
| T3 | the statement applies an inductive `Prop`-valued derivation relation | `verify_certification_tier.py` |
| T4 | a `<base>_reading` ties the catalogue's printed string to the AST the theorem asserts | `verify_certification_tier.py` |
| T5 | `#print axioms` reports no axioms | `verify_axiom_audit.py` |
| T6 | the statement is neither vacuous nor a duplicate | `verify_certification_tier.py` |
| T7 | `ci_evidence` resolves, is an ancestor of HEAD, and is not stale | `verify_ci_evidence.py` |
| T8 | the stored derived registry is exactly what the gates recalculate | `derive_certification_registry.py --check` |
| T9 | non-logical assumptions reached are declared | `verify_certification_tier.py` |
| T10 | every constructor of a judgement relation answers to a printed primitive | `verify_judgement_primitives.py` |
| T11 | the asserted formula is written in PM's notation, not Lean's | `verify_certification_tier.py` |
| — | the proof follows the demonstration PM prints | `verify_printed_citations.py` |

Some criteria deserve their reasons stated.

**T1 is the import closure, not the build.** `lakefile.toml` now carries
`globs`, so `lake build` compiles every module under `Principia/` — that is how a
broken orphan module surfaces instead of sitting unread. But a module outside the
import closure of `Principia.lean` is invisible to `import Principia`, so
`#print axioms` cannot reach it and it is not part of the published library.
Compiled is not the same as certified.

**T3 admits only an inductive relation.** A `structure` whose fields the caller
supplies is inhabited without any derivation having taken place. `Star_11_42Derivation`
is such a structure: its fields are `star_11_42_target φ ψ = star_11_42_target φ ψ`
and a generic Lean fact, so it holds for every φ and ψ and commits to nothing.

**T4 compares three things, and founds none of them.** It checks that the
catalogue's `printed` string equals the reading's, and that the reading's `parsed`
AST equals the formula the theorem asserts. It does *not* check that the AST is a
correct reading of the printed string — `scopeReading` is prose, and that link is
editorial. T4 guarantees the link cannot silently drift; it does not establish it.

**T5 allows no axioms at all.** This is not an aspiration: the ✱1–✱5 layer is
measurably axiom-free, including `PM.Derivation.instantiateSchema`. `propext` and
`Quot.sound` are conservative but signal reasoning about Lean quotients and
propositional equalities — a semantic model rather than the object calculus.
`Classical.choice` is never admissible: PM's printed demonstrations in this
fragment license no non-constructive principle.

**T10 is what stops T3 from being cosmetic.** An inductive relation with an
invented constructor satisfies T3, T5 and T6 while assuming its conclusion. A
constructor named `printed_chain` is not a rule of PM. Neither is a `Df`: PM's
definitions are eliminable abbreviations and must be `def`s that unfold, never
constructors — turning one into a constructor makes it irreducible, which adds to
the system rather than reconstructing it.

A constructor that genuinely carries syntax rather than inference — the base
cases of a formation judgement, say — is legitimate, but it must be *declared* in
`metadata/judgement_constructors.json` with an argument from the printed text.
Two are declared today. Moving a calculus from `Prop` to `Type` does not escape
this check: `judgement_relations()` follows a `def X : Prop := Nonempty (Evidence …)`
to its evidence type, because that shape is a faithful reading of PM's `⊢` — "a
finite proof tree exists" — and its constructors are still the printed primitives.

**T11 keeps the syntax PM's.** The formula a judgement asserts must use `∼ₚ`,
`∨ₚ`, `⊃ₚ`, `∧ₚ`, `≡ₚ`. A Lean `∧` or `→` there means the statement has left the
reconstructed calculus for the host logic, whatever else it satisfies.

**The printed-citation check asks the remaining question.** T1–T11 establish that
a proof is a derivation of the printed proposition. `verify_printed_citations.py`
asks whether it is *PM's* derivation: it reads the elaborated proof term through
`#print`, so a lemma reached by `simp` is as visible as one written by hand, and
requires that everything the printed demonstration cites actually appears. The
converse is deliberately not required — PM abbreviates, citing the substantive
steps and leaving routine transitions implicit — so a Lean term legitimately
mentions more than the page does, never less.

## Exact facts → tier function

The registry generator first removes `formal_status`, `formalization_level`,
`certification_tier` and `certification` from every in-memory item. It then runs
the item-local implementation of T1–T7, T9 and T11, the kernel axiom audit for
T5, and the global judgement-constructor audit for T10. Duplicate declarations
are marked T6 independently of their former status. T8 is not an item input: it
is the exact-file comparison performed by `--check`.

For a catalogue item `i`, let `F(i)` be the failed criteria after those gates,
and let `resolves(i)` mean that its declared Lean name is found as a declaration
or legitimate primitive constructor. The tier is the first applicable case:

1. `prepared` if no non-empty `lean_path` and `declaration` pair was supplied,
   or if the named declaration does not resolve in an otherwise imported file;
2. `unbuilt` if a concrete `lean_path` was supplied but T1 fails;
3. `lean-typechecked` if the declaration resolves but any criterion other than
   T7 fails;
4. `awaiting-ci` if the declaration passes every structural/kernel criterion
   and T7 alone fails;
5. `kernel-checked` if no criterion fails.

The derived `formalization_level` is `pm-derivation-v1` exactly when
`F(i) − {T7}` is empty; otherwise it is JSON `null`. Thus lack of CI may delay a
certification tier without denying a structurally complete derivation. The
derived `canonical_integration_eligible` flag is true exactly at
`kernel-checked`.

Definitions retain the existing kind-sensitive interpretation: a printed `Df`
must resolve to an unfoldable `def`/`abbrev`; it is not required to masquerade
as a theorem or a derivation judgement. Primitive propositions may resolve to
constructors only when their catalogue kind says they are primitive.

## The tiers

- **`kernel-checked`** — every criterion holds. Reserved. A reader may take this
  as: the printed proposition has been derived, in a reconstruction of PM's own
  calculus, from PM's own primitives, with no axiom and no escape hatch, and the
  Lean that says so is compiled by CI at a commit that exists.
- **`lean-typechecked`** — a Lean declaration of that name compiles, and nothing
  more is claimed. Its statement may be a proposition of a semantic model rather
  than a judgement of the object calculus. This is *not* a synonym for verified.
- **`unbuilt`** — the module is outside the import closure. Nothing certifies it.
- **`awaiting-ci`** — structurally sound but without resolvable CI evidence.
- **`prepared`** — transcribed and catalogued; no formal claim is made.

An `integration_status` beginning `canonical-` is permitted only at
`kernel-checked`; below it the prefix is rewritten to `provisional-`.

## Migration plan (not executed here)

The removal of the duplicated fields must be one coordinated migration, not a
sequence in which some consumers silently fall back to item claims.

1. Land the generator, the initial derived registry, its anti-falsification
   test, and protection of both generator and registry. Add
   `python3 scripts/derive_certification_registry.py --check` to CI only after
   the generator change has received the separately authorised gate re-pin.
2. Add one registry reader keyed by item `id`. Make all consumers read
   `certification_tier`, `formalization_level`, failed criteria and canonical
   eligibility from it. A missing/duplicate id or a stale registry must be a
   hard error; there must be no fallback to catalogue fields.
3. Break the remaining status-dependent gate cycle. In particular,
   `verify_axiom_audit.py`, `verify_printed_citations.py` and
   `verify_ci_evidence.py` currently select work using `formal_status`. Their
   reusable audit functions must consume factual candidates during derivation;
   their stand-alone reporting modes may read the checked registry afterward.
4. Split factual integration routing/blocker data from the derived
   `canonical_integration_eligible` result. Likewise, keep parser evidence as an
   input but calculate parser/status summaries from it.
5. In one mechanical, reviewable change, remove `formal_status`,
   `formalization_level` and `certification` from all 6,203 items. Do not infer
   or preserve their values: regenerate the registry from the remaining facts.
6. Change schemas and editorial gates to reject those conclusion fields in
   item JSON. Regenerate the registry with `--write`, run `--check`, the full
   test suite and Lean gates, then lock it again with `tools/gate-lock`.

The direct breakage surface found in the current tree is substantial. The
following scripts presently read or write one of the fields being removed:
`build_edition.py`, `pm_constraint_manifest.py`, `pm_context_bundle.py`,
`pm_queue_inventory.py`, `promote_awaiting_ci.py`,
`promote_canonical_backfill.py`, `report_lean_source_coverage.py`,
`verify_axiom_audit.py`, `verify_certification_tier.py`,
`verify_ci_evidence.py`, `verify_dependencies.py`, `verify_editorial.py`,
`verify_pm_parser_coverage.py`, `verify_preflight.py`,
`verify_printed_citations.py`, `verify_retry_registry.py` and
`verify_statement_only_interfaces.py`. Edition/site output, workflow steps and
their fixtures/tests also assume item-local status. Until every one of those
callers uses the checked registry, deleting the fields would either break the
build or, worse, reintroduce a permissive fallback.

This mission does not perform that migration and does not modify any catalogue
item. It also deliberately does not update `metadata/gate_integrity.json`: the
new protected files and changed protection policy must be re-pinned only in the
maintainer's separately authorised gate-integrity workflow.

## What is still not checked

Stated plainly, because a gate list reads as completeness and this one is not.

1. **The parse is not verified.** T4 preserves the printed↔AST link; it does not
   found it. Closing this means parsing the printed string with
   `scripts/pm_syntax.py` and comparing its AST to `parsed`.
2. **The citation whitelist is not enforced at declaration granularity.** A proof
   may use what the printed demonstration does not cite;
   `scripts/verify_dependencies.py` attempts this and leaks.
3. **Coverage is small and will stay small.** Volumes II–III have no derivation
   relation, so their items remain `prepared`. That is the true state, not a
   failure.

The point of the tiers is not to certify many items. It is that `kernel-checked`
should mean something.
