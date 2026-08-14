# Q413 strict semantic review — PM II ✱102·22–·24

All three propositions pass strict typed equivalence. In ✱102·22, Lean's
`a : Class A` and `b : Class B` internalize the two printed inclusions in the
universal endpoint types; the explicit self-implications retain those
conditions extensionally. In ✱102·23, `R : Relation A B` similarly internalizes
the domain and converse-domain inclusions, while `OneOne R` and both displayed
domain equalities are retained. ✱102·24 changes only the witness predicate to
the assigned-endpoint spelling `TypedOneOne R`; neither domain equality nor
either direction of the biconditional is lost.

The first-edition scan at leaf 68 and PG78255 agree on all enunciations. Their
printed citations remain recorded as historical evidence. Each Lean theorem
closes by unfolding the typed definitions, so the three direct Lean and
normalized dependency graphs are empty. This is definitional closure rather
than a claim that PM printed no dependencies. Exactly ✱102·22, ·23, and ·24
are promoted to `awaiting-ci`; no later item is covered by this review.
