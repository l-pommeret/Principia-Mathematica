# ✱122 catalogue 03 strict semantic audit

Scope: PM2:✱122·152, ·16, ·17, ·2, and ·21 on printed pages
257–258 (scan leaves 297–298), checked against Gutenberg 78255 and the five
namesakes in `Star122Kernel.lean`. All five correspondences are refused.

- **·152** states four restriction equalities for strict posterity; Lean only
  embeds one edge into the custom reflexive `Reach` relation.
- **·16** says strict posterity is irreflexive. Lean assumes an edge and proves
  only the converse edge is impossible from a custom two-cycle field; it does
  not state irreflexivity of transitive posterity.
- **·17** is a full equivalence characterizing progressions by many-one typing,
  posterity irreflexivity, and a domain/ancestral equality. Lean projects only
  `Functional R ∧ Linear R` from its replacement structure.
- **·2** compares any two field members by PM's reflexive ancestral. Lean uses
  the custom `Reach`; without an interpretation theorem these relations cannot
  be identified.
- **·21** is the strict-posterity trichotomy. Lean merely weakens its reflexive
  `Reach` comparison by inserting an unused equality disjunct.

Thus there are no accepted Lean dependency edges and no `awaiting-ci` split.
The printed citations remain recorded in the catalogue.
