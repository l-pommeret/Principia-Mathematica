# ✱62 source catalogue review

The twenty-nine loci are checked against Project Gutenberg 78050 on printed
pages 415–418 (scan leaves 437–440). Page 414 contains the chapter heading and
introductory synopsis; the numbered diplomatic sequence begins on page 415.
Every source ID resolves uniquely to an
existing Lean declaration and remains `prepared` pending semantic audit.

The parser accepts 1 formulas; 28 historical membership/relation formulas carry
`reviewed-gap` with this review as evidence.

## Semantic audit: catalogue 02

Of loci ✱62·23–26, only ✱62·23 has an exact typed pointwise realization: the
converse domain of membership at `a` is inhabited exactly when `a` has a
member. Loci ·231, ·24, ·25, and ·26 remain prepared because their current Lean
declarations respectively omit an equivalence, replace a range equality by a
special-case implication, replace an image-class equality by pointwise
nonemptiness, or restrict an arbitrary relation by the universal class instead
of reconstructing PM's membership restriction. They are not promoted.

## Semantic audit: catalogue 03

No locus in ✱62·3–·34 is promoted. The current declarations respectively
replace PM's relation-image/type equality with a one-class `EpsImage` identity,
replace it with partial application/evaluation, replace relation equalities by
pointwise membership and negated membership, and reduce the final relational
image/singularization statement to the definition of a generic existential
image. These typed statements compile, but none is the exact printed target.

## Semantic audit: catalogue 04

Only ✱62·44 is promoted: `Included R Eps ↔ ∀ x a, R x a → a x` is the
exact typed pointwise reading of `R ⊂ ε` iff every relational value is
included in its class. Loci ·4 and ·41–·43 remain prepared. Their declarations
prove respectively one fibre of a restriction, singleton self-membership, a
definitional membership transport, and one restricted-domain witness; none
establishes the relation or domain equality printed by PM.
