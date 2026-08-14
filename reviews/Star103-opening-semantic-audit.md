# ✱103 opening strict semantic audit

Scope: exactly five prepared candidates, namely every item in
`PM2-star-103-Q421.json` and the first two items in
`PM2-star-103-Q422.json`. The diplomatic source blocks were compared with the
same-number declarations in `Star103Source.lean` and `Star103Kernel.lean`.
The remaining item ✱103·1 and all later ✱103 catalogues were not audited here.

None of the five candidates is semantically exact, so none is promoted to
`awaiting-ci`:

- ✱103·12 prints `α ∈ N₀cʻα`; Lean's `star_103_12` instead proves symmetry of
  `CardinalClass` membership between arbitrary sets.
- ✱103·2 prints a three-way characterization of `μ ∈ N₀C` by existential
  equalities; Lean's `star_103_2` merely supplies one inhabitant of
  `CardinalClass s`.
- ✱103·26 prints, under `μ ∈ NC`, the equivalence between `α ∈ μ` and
  `N₀cʻα = μ`; Lean's `star_103_26` takes an equinumerosity hypothesis and
  concludes homogeneity of a represented cardinal class. It also introduces
  the Lean-only numbered edge ✱103·14.
- ✱103·01 defines `N₀cʻα` as `Ncʻα ∩ tʻα`; the declaration documented with
  that number instead defines a predicate saying that every two members of a
  class of sets are equinumerous.
- ✱103·02 defines `N₀C` as the domain of `N₀c`; the declaration documented with
  that number instead maps one set to its equinumerosity class.

These are number collisions with a simplified surrogate model, not admissible
typed renderings of the printed formulas. The catalogue records retain
`formal_status: prepared`, identify the actual declarations inspected, and
record explicit semantic-refusal states. There is no exact item in this audit
and therefore no CI promotion.
