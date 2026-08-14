# ✱115 catalogue 03 — strict source/Lean semantic audit

The five next printed loci are ·142, ·143, ·144, ·145, and ·15 on PM II
page 137 (1912 scan leaf 177). They were checked against Gutenberg 78255 and
the scan, then against the complete Lean theorem types.

Only ✱115·143 passes. PM says that the product of the family of singleton
images of the members of α is the singleton of α. The typed theorem builds the
corresponding dependent choice `i ↦ ⟨a i, rfl⟩` and proves by function and
subtype extensionality that every element of that product is this one. Thus
`UniqueValue ... True` is exactly the typed singleton-class assertion.

The other four are refused. ·142 and ·144 reduce class equalities to mere
inhabitation equivalences (and ·144 additionally assumes an actual index).
·145 substitutes classical choice for PM's factor-removal membership iff.
·15 is a reflexive equality and contains neither PM's two families, common
union premise, nor reciprocal inclusion conclusion.

The split is 1/5 awaiting CI and 4/5 refused, with disjoint IDs. The passing
Lean declaration has no named theorem dependency; PM's citation of ✱83·71 is
recorded as a reviewed historical relaxation. Parser coverage remains a
reviewed gap for these class/product formulas.
