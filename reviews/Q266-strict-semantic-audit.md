# Q266 strict semantic audit — ✱10·13

✱10·13 is refused. The printed metatheorem derives the simultaneous assertion
`⊢ . φx . ψx` from assertions of two same-typed function values. The metadata
names `PM.FirstEdition.Volume1.Star10.star_10_13`, but that declaration does
not exist. The existing Q266 architecture review also identifies the exact
obstruction: the closed judgement layer has no derivation constructor for
adjoining two arbitrary asserted open values, and cited ✱9·131 has no canonical
declaration. Adding either as an assumption would weaken the formalization.

Thus there is no Lean proof body or theorem-dependency graph to compare. The
printed citations remain preserved, the Lean and normalized graphs are empty,
and the item stays `prepared` with a documented strict refusal.
