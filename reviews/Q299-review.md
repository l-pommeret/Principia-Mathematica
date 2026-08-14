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

The historical dependency chains are split into exact catalogue identifiers
in metadata: the conversion citations for ·1 and ·11 use ✱4·2 together
with definitions ✱14·01 and ✱14·02; ·111 uses ✱4·2, definitions
✱14·04/·03, ✱14·1, and ✱11·55.  The two conventional-scope
corollaries ·101 and ·112 cite and call ·1 and ·111 respectively.

## Star2-standard T1–T9 reaudit

All five public declarations are ordinary Lean `Prop` equivalences.  Three
close by definitional reduction (`rfl`), and the other two merely reuse those
Prop theorems.  None is an inductive assertion judgement indexed by the
description AST, and none has a proof term assembled from PM rules.  A `Df`
may license unfolding but does not itself create a derivation constructor.

Consequently all five records are now `prepared`, explicitly blocked on the
missing inductive description judgement, and labelled `secondary-prop-only`.
The Prop translations remain useful secondary checks but are not primary
Star2-standard evidence.  No axiom, `Support`, `sorry`, `admit`, or unsafe
declaration occurs in the targeted module.
