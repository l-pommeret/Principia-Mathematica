# Q332 exact Lean audit

Leaf 238 (p. 216), SHA-256
`bf0ff41a2c61faff2e7d55b655b572aa0fbe16a56f915355ab7d34ad40019067`,
witnesses ✱21·11, ✱21·111, ✱21·112, ✱21·12, and ✱21·13.

The Lean module retains each relation as `Left → Right → Prop`, so neither
apparent variable is erased or forced to share a type. Formal equivalence
with subscript `(x,y)` is `∀ x y, … ↔ …`. Function application in
✱21·11/111/112/12 is genuinely at a relation argument, while ✱21·13
concludes equality of the complete binary extensions.

The only logical extensionality step is Lean's kernel-level `propext` followed
by function extensionality. There is no `Classical`, choice, relation axiom,
placeholder, unsafe feature, narrowed unary instance, or semantic stub.
