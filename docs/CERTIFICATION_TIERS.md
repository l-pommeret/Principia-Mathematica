# Certification tiers

A tier is *derived*, never asserted. `scripts/verify_certification_tier.py`
recomputes every catalogue item's tier from the Lean sources and from git, and
fails when a recorded `formal_status` claims more than the tree supports. No
script may promote an item; a script may only record what the computation found.

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
| T8 | `formalization_level` is present and does not exceed the tree | `verify_certification_tier.py` |
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
