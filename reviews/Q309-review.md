# Q309 review — ✱14·272

Leaf 215 (p. 193), SHA-256
`c8e1dc1fee2977f528e063b20efb828d83ca2e055b4dc57aa0ce5f75f84f8c06`,
and PG78050 agree on the extensionality locus.

The formalization uses the established contextual definiens
`DescriptionScope`. From `∀x, φx ↔ ψx`, the local lemma proves that `φ` and
`ψ` characterize exactly the same candidate. The witness and the continuation
proof are then transported in each direction while remaining inside their
existential scope. No description-valued term, choice, classical principle,
or extra function-extensionality axiom is introduced.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star14Q309Kernel.lean`
