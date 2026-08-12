# Q340 exact mixed-relation audit

PM I p. 216, scan leaf 238, SHA-256
`bf0ff41a2c61faff2e7d55b655b572aa0fbe16a56f915355ab7d34ad40019067`,
and PG 78050 witness ✱21·705 and ✱21·71. Their printed notices are “Proof
as in ✱20·703” and “Proof as in ✱20·71”.

`Star21Q340Kernel.lean` keeps the two argument sorts of every binary relation
independent. ✱21·705 is instantiated at a class carrier and the complete
binary-relation carrier, so no relation argument is collapsed; its only
formal ingredient is the already checked binary reducibility theorem ✱12·11.
✱21·71 retains the printed quantification over every predicative function of
a relation argument. The reverse implication uses the admissible predicate
`T ↦ R = T`, making the equality conclusion unconditional.

Both proofs are constructive and polymorphic. There is no `Classical`, choice,
new axiom, `sorry`, oracle, or semantic relation constant. Metadata preserves
the printed analogue citations and explicitly records the direct Lean closure
used where those analogue batches are not yet formalized.
