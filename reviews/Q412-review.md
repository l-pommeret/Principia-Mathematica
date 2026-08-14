# Q412 strict semantic review — PM II ✱102·11, ✱102·13, ✱102·2

First-edition p. 27, Commons leaf 67, is canonical; its derivative SHA-256 is
`38de239bf8da1c3717f2dd804ee3bed32f2a9e131ab28ca659e4997dc0116dd7`.
PG78255 independently witnesses all three enunciations and their printed
citation order.

## Exact items

✱102·11 passes strict typed equivalence. A Lean relation `R : Relation A B`
already has the two endpoint types denoted by PM's `(x,y)` indices. `OneOne R`
is exactly functionality plus injectivity, and `TypedOneOne R` is its assigned-
endpoint spelling. Thus `star_102_11` retains the printed implication without
adding a premise or dropping either one-one condition.

✱102·2 also passes. `a : Class A` and `b : Class B` internalize the printed
conjuncts `γ ∈ tʻα` and `δ ∈ tʻβ`; `TypedSimilar a b` and `Similar a b` use the
same one-one witness with those endpoints. The definitional biconditional
therefore retains both directions of the printed equivalence. These two items
are promoted to `awaiting-ci`.

Their printed citation lists remain in the historical graph. Both Lean proofs
close definitionally and contain no numbered theorem constant, so their direct
Lean and normalized dependency graphs are empty; this is relaxed definitional
closure, not an invented historical edge.

## Refused item

✱102·13 is not promoted. The print gives a one-way theorem from unrestricted
one-one `R` to the one-sided assigned restriction `Rₓ ∈ 1(x)→1`. In contrast,
`star_102_13` states `TypedOneOne R ↔ OneOne R` for an `R : Relation A B`
whose two carrier types are already fixed. It both strengthens the implication
to a biconditional and fails to reconstruct the one-sided operation `Rₓ`.
This mismatch is recorded in the separate homogeneous catalogue
`PM2-star-102-Q412-refused.json`; the item remains `prepared` and blocked.
