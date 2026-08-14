# ✱9 PM migration — lot 04

Scope: ✱9·08, ✱9·6, ✱9·61, ✱9·62, and ✱9·63.

✱9·08 is a printed `Df` and a reducible `SecondOrder` syntax abbreviation. It is classified `pm-definition-v1`; kernel unfolding is its only certificate and no derivation constructor is claimed.

The remaining four entries do not meet the derivation tier:

- ✱9·6 is a theorem, but its conclusion is the structure `SameAssignedType4`, not an inductive PM judgement. Its fields are filled by the unconditional constructor `SameAssignedType.witness`, while the printed ✱9·131 citation is unused. It fails T3 and the citation audit.
- ✱9·61, ✱9·62, and ✱9·63 are printed existence propositions represented as data-producing `def`s. They are not printed definitions, so they do not qualify for `pm-definition-v1`; they also fail T2/T3 for `pm-derivation-v1`. Their printed formation citations are not theorem calls.

All four are therefore explicitly `prepared`/blocked. Their direct dependency graphs remain empty, which accurately exposes—rather than relaxes—the missing printed derivations.
