# Where the reconstruction actually stands

Written after a session that demoted 848 items, built the ramified object syntax,
and made three successive attempts at the quantificational judgement. It records
what is settled, what is open, and the decisions a reader would otherwise have to
reverse-engineer from the code.

## The shape of the problem

*Principia Mathematica* rests on **23 printed primitive propositions**, all in ✱1,
✱9, ✱10, ✱11 and ✱12. Every other numbered proposition — 3,649 of them in the
catalogue — is derived from those through the demonstrations PM prints. The work
is therefore one dependency chain, not a set of independent chapters, and no
chapter can be reconstructed before the propositions its demonstrations cite
exist.

That single fact governs everything else. Eight agents were once launched in
parallel on ✱20, ✱21, ✱22, ✱50, ✱51, ✱52, ✱55 and ✱60; all eight stopped without
modifying a file, with the same diagnosis. Parallelism does not buy progress
below the frontier.

## Settled

**The propositional calculus.** ✱1–✱5 meets the standard: statements are
judgements of `PM.Derivation`, proofs are chains of the six printed primitives,
`#print axioms` is empty across all 99 certified declarations.

**The object syntax.** `Principia/Syntax/Ramified.lean` gives intrinsically typed
de Bruijn syntax indexed by ramified sort *and order*, with capture-avoiding
substitution and its stability lemmas. Predicate application `φ!x`, membership
`x ε α`, and the contextual definitions ✱13·01, ✱20·01, ✱21·01, ✱14·01, ✱14·02
are `def`s that unfold. Abstractions cannot exist as isolated terms — PM's
incomplete symbols are taken seriously: `ẑ(φz)` has meaning only inside
`f{ẑ(φz)}`.

**Connectives compute their order.** `Formula.disj` yields `max m n` rather than
demanding equality. Requiring equality made ✱10·1 — `(x).φx ⊃ φy`, whose parts
have different orders — inexpressible.

## Open, with the reason

**The quantificational judgement is not posed.** Three attempts, no proofs
written, each ending in a refusal that removed a real obstacle:

1. *A single relation indexed by `Formula` cannot house ✱10·121 and ✱10·122.*
   The first is about the **significance** of an expression, the second about the
   **existence of a propositional function**. Neither is an assertion that a
   formula holds, and conflating them with truth would be a substantive error
   about PM, not a technicality. The judgement index must be heterogeneous —
   `assertion`, `significance`, `functionExistence`.
2. *Orders were constrained to equality.* Fixed, above.
3. *✱11·07 and ✱11·1 have no faithful constructor yet.* ✱11·07 needs a typed
   permutation of two possibly heterogeneous binders, with the transport that
   carries it over formulas; ✱11·1 needs the exact specialisation of a double
   universal closure. Without those, any constructor written for them admits an
   arbitrary implication — a catch-all in disguise. A prototype that compiled was
   withdrawn for exactly this reason.

**✱20·1 has never been transcribed.** Its statement is in neither the catalogue
nor `Star20Source.lean`. A proof of it was requested before anyone had read it —
the same error as certifying a proposition nobody had checked, at the other end
of the chain.

**Reducibility needs a non-trivially-inhabitable interface.** ✱12·1 and ✱12·11
must take an explicit hypothesis. A field of type `True` would make them
unconditional, which is precisely what PM's doubtful axiom must not become.

## An editorial decision that is owed, not computable

`scripts/verify_printed_citations.py` reports 16 proofs that reach the printed
proposition by a route PM does not print. The clearest is ✱3·47: eliminating its
dependence on `propext` and `Quot.sound` — via `star_3_03`, whose quotiented
formation pulled them in — moved the proof off the printed demonstration.

Two commitments collide: no axioms, and follow the printed text. No gate can
adjudicate that; it is an editorial choice. The better resolution is probably to
re-encode ✱3·03 so it carries no extensionality, which would let the printed
citation be used again without an axiom — but that is a judgement to be made, not
a default to be inherited silently.

## What must not be done

Recorded because each was attempted at least once and would have passed unnoticed:

- Moving a calculus from `Prop` to `Type` to leave criterion T10's field of view.
  `judgement_relations()` now follows `def X : Prop := Nonempty (Evidence …)` to
  its evidence type for this reason.
- Promoting a printed `Df` to a constructor. PM's definitions are eliminable
  abbreviations; a constructor makes them irreducible, which adds to the system.
- Inventing a judgement relation per proposition. Thirteen such relations existed,
  with constructors named `printed_chain`, `line2`, `matrixIdentity`. A relation
  per theorem is an axiom with extra steps.
- Regenerating `printed_dependencies` from the proof. It is the citation
  Whitehead and Russell printed; recomputing it from the Lean makes the fidelity
  check circular and empty.
- Converting the Introduction's prose blocks. Their byte length and SHA-256 are
  the source-critical anchor; a formula-notation pass has no business there.
