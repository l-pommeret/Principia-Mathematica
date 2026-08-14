# ✱100 source catalogue review

The thirty-nine loci are checked against Project Gutenberg 78255 on printed
pages 14–18 (scan leaves 54–58). Every source ID has a Lean declaration. Legacy batch Q400 entries ·2/·21/·22 are upgraded from source-only status to their current Lean targets. IDs ·34–·36 are duplicated across kernels; metadata deliberately selects SecondKernel for ·34 and the developed OpeningKernel proofs for ·35/·36. The duplicate-declaration audit remains visible. Items stay `prepared` pending semantic promotion except where an item-level audit below explicitly promotes them.

The parser accepts 26 formulas; 13 cardinal-class formulas carry `reviewed-gap`.

## Catalogue 01 strict semantic audit

The opening five items, ✱100·01, ·02, ·1, ·11, and ·12, pass strict typed
equivalence and are promoted in place to `awaiting-ci`.  Definition ·01 reads
`Nc a b` as similarity of `b` and `a`; ·02 reads membership in the range-class
`NC` as being a value `Nc a`.  Proposition ·1 is the pointwise extensional
form of both displayed class equalities and retains both orientations of
similarity.  The canonical citations are retained as historical dependencies:
·1 cites ✱32·13, ✱73·31, and the definition ✱100·01; ·11 cites ✱100·1 and
✱73·1; ·12 cites ✱100·1 and ✱73·11.

For ·11, `Nonempty (ClassEquiv b a)` is the typed encoding of the displayed
existence of a one-to-one relation with the prescribed domain and converse
domain.  For ·12 the same equivalence structure is the exact invariant of the
displayed injective restriction-and-image characterization: a witness may be
restricted to `a`, and conversely an equivalence supplies that restricted
one-to-one relation.  Thus neither target assumes similarity, drops a
quantifier, or proves only one direction.  The five Lean bodies use only local
definitions and the unnumbered symmetry lemma, so the printed citations are
recorded under explicit `relaxed-closure` evidence while the Lean and
normalized numbered-proposition graphs remain empty.  CI evidence remains
pending; no later ✱100 item is promoted by this audit.

## Catalogue 02 strict semantic audit

The four prepared records in the second catalogue were audited.  Propositions
✱100·14, ·15, and ·16 are promoted to `awaiting-ci`: each printed formula is
an existence-and-bijection characterization of membership in `Nc a`, and the
typed `Nonempty (ClassEquiv b a)` target retains both directions, totality on
the represented subtypes, injectivity, surjectivity onto the displayed image,
and the image class `b`.  The inverse orientation of the structure is harmless
because `ClassEquiv` supplies both mutually inverse maps.  Their declarations
are definitional and have no numbered Lean dependency.

✱100·13 is refused and remains `prepared`.  Its source asserts two explicit
equalities with images of classes of one-to-one relations, one through converse
domains and one through domains.  The Lean declaration merely unfolds
`Nc a b ↔ Similar b a`; it defines neither relation-class image and proves
neither displayed equality.  Equinumerosity alone is the common conclusion,
not an exact formalization of this stronger displayed structure.  The split
metadata files partition the four IDs, so no duplicate record is introduced.
