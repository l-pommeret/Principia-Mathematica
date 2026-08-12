# Q299 exact contextual-description audit

Leaf 206 (p. 184), SHA-256
`d82a452d1485876e6962c1ff219a9304404d429a85cd20e1bdebfdc1db47b3f8`,
and PG 78050 collate ✱14·1, ✱14·101, ✱14·11, ✱14·111, and ✱14·112.

The earlier audit correctly prohibited adding a description constructor to
the term language or mistaking equality of `DescriptionSyntax` trees for an
asserted PM equivalence.  Q299 is now closed by a different, narrower route:
`Star14Q299Kernel.lean` represents only the *contextual definiens* already
licensed by ✱14·01--04.  A description scope is an existential candidate
`b`, the full matrix `∀x, φ(x) ↔ x=b`, and the continuation at `b`.
Two-description scope retains two independently typed candidates and both
characterization matrices in the printed order.

Thus no description is ever made into a Lean term and no choice function is
introduced.  ✱14·1 and ✱14·11 unfold the exact contextual definitions;
✱14·101 and ✱14·112 reuse the corresponding explicit-scope results;
✱14·111 unfolds the complete two-candidate scope.  The translations are
polymorphic and need no `Classical`, decidability, inhabitedness, new axiom,
oracle, `sorry`, or generic assertion rule.

The historical dependency chains remain recorded in metadata.  Lean checks
the complete Russellian contextual propositions directly, rather than
claiming that the repository's object-language syntax has acquired a
description-valued term or an unaudited derivation carrier.
