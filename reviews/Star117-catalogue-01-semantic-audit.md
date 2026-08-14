# PM II ✱117 catalogue 01 strict semantic audit

Scope: exactly five source-catalogued candidates: ✱117·01, ·05, ·103, ·105,
and ·221. The diplomatic strings were checked against Project Gutenberg 78255,
first-edition pp. 173 and 176 (scan leaves 213 and 216), and against
`Star117Source.lean`. The audit compares full theorem types and object layers,
not proposition numbers or the fact that a surrogate theorem reduces by `rfl`.

No candidate is semantically exact, so none is promoted to `awaiting-ci`.

- **✱117·01** defines `μ > ν` for cardinal objects through representatives
  `N₀cʻα`, `N₀cʻβ` and asymmetric class-existence conditions. Lean instead
  defines `StrictlyLarger A B` directly on arbitrary `Set'` representatives as
  one-way `Embeddable`. No interpretation theorem connects these constructions.
- **✱117·05** includes both `μ,ν∈N₀C` and `μ=smʻʻν` in its equality
  alternative. Lean replaces that entire branch by `Equinumerous A B`, omitting
  the cardinal-domain condition and changing the objects compared.
- **✱117·103** is definitionally symmetric in print, but the Lean `Iff.rfl`
  concerns the surrogate `Set'` relations. Reflexivity does not certify the
  missing interpretation from PM cardinal objects.
- **✱117·105** has the same carrier mismatch and additionally depends on
  Lean's weakened `AtLeast`, which lacks the printed `N₀C` condition.
- **✱117·221** has no same-number Lean declaration. `Embeddable` resembles
  the existential subset/equinumerosity clause, but neither an `Nc` operation
  nor a theorem relating it to the printed cardinal comparison is present.

The printed dependency graph is retained in the catalogue: ✱117·103 prints
a citation to ✱117·04, but that definition is not yet catalogued, so it is
recorded under `printed_but_unused` and deliberately creates no normalized
edge. The same treatment applies to the uncatalogued printed citation ✱117·06
from ✱117·105. Finally, ✱117·221 cites ✱117·22, ✱60·2, and ✱100·1:
the uncatalogued ✱117·22 is `printed_but_unused`, while the two already
catalogued citations remain normalized. Lean dependencies are deliberately
empty because no candidate
is accepted as a formalization. Each failure is recorded once, directly in the
canonical catalogue item, so this audit introduces no duplicate item records.

Parser audit: all five unchanged diplomatic strings fail the current object
parser on the cardinal-order symbols (`>`, `<`, `≥`, or `≤`). They therefore
carry `reviewed-gap` with this review as evidence; no parseable item is exempted.
