# Q327 exact reduction audit

Leaf 233 (p. 211), SHA-256
`cea90e2a2d81f6a554ffd4270e897d4e3bf0c453ae1da140890d6a5ef3fb3c5c`,
collated with PG 78050, witnesses ✱21·01.

`Star21Q327Definition.lean` preserves the two argument positions as an
arbitrary `Left → Right → Prop`; the domains need not coincide. The formal
equivalence subscript `(x,y)` is translated by `∀ x y`, and application of
`f` remains inside the existential scope of the predicative representative
`phi`. Thus neither variable is erased and the definition is not collapsed
to a unary or closed relation.

The theorem is the exact definitional reduction and closes by `rfl`. It adds
no relation-existence, predicativity, reducibility, extensionality, or choice
axiom, and uses no placeholder or unsafe feature.
