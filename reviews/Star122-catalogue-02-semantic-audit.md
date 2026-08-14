# ✱122 catalogue 02 strict semantic audit

Scope: exactly PM2:✱122·141, ·142, ·143, ·15, and ·151 on
first-edition printed page 257 (scan leaf 297). The five source formulae were
checked against Project Gutenberg 78255 and against their namesakes in
`Principia/Architecture/Star122Kernel.lean`. None is an exact formalization,
so the split is homogeneous: five documented refusals and no `awaiting-ci`
record.

- **✱122·141.** PM proves both converse-domain inclusion and the equality of
  field with domain. Lean proves only `field R = domain R` for the replacement
  `Progression`; its `field` is a local disjunction of domain and range, and the
  printed converse-domain claim is absent.
- **✱122·142.** PM quantifies a power `P` of `R` and concludes equality of
  their domains. Lean has no `P` or power predicate: it merely rewrites the
  pointwise implication `field R x → domain R x` using its previous equality.
- **✱122·143.** PM again assumes `P∈PotʻR` and concludes converse-domain
  inclusion for `P`. Lean is the definitional injection `range R ⊆ field R`;
  it omits `P`, powers, and the asserted domain relation.
- **✱122·15.** PM gives four equal forms of `R` under left/right restrictions
  to ancestral and posterity classes of its first member. Lean only says that
  the endpoints of one edge lie in its locally defined field. There are no
  restriction operators, first member, ancestral, posterity, or equalities.
- **✱122·151.** PM gives analogous restriction equalities for the reflexive
  ancestral `R∗`. Lean proves only reflexivity of the custom inductive closure
  `Reach R x x`, with neither restrictions nor progression hypothesis.

Since every correspondence is refused, each accepted Lean dependency graph is
empty. Printed dependencies are retained in the catalogue from the displayed
citations. Compilation of a surrogate is not promotion evidence.
