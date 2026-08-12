# Q318 exact class-extensionality audit

Leaf 223 (p. 201), SHA-256
`5095961520e5549e6487f7513da6d727d72b694c1616e8a2d4e04ee06a593cd7`,
and PG 78050 collate ✱20·12, ·13, ·14, ·15, and ·151.

`Star20Q318Kernel.lean` keeps classes eliminative. `ClassEq ψ χ` is exactly
the pointwise equivalence of their members; no class-valued term, universe,
or quotient is introduced. A context `f` in ✱20·12 carries the explicit
`Extensional f` condition needed to consume equality of extensions.

The predicative witnesses in ✱20·12 and ✱20·151 come only from formalized
✱12·1. ✱20·13 and ✱20·14 are the two directions of extensionality, and
✱20·15 combines exactly those directions. The proofs are polymorphic and
constructive, with no `Classical`, choice, new axiom, `sorry`, oracle, or
erased reducibility premise.
