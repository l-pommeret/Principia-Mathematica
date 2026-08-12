# Q333 review — ✱21·14–17

Leaf 239 (p. 217), SHA-256
`618129e7ea48fcf79a18fbffcae9f88e7275d0d6caf702101b287c76b21247f2`,
and PG78050 agree on all five statements.

The formalization uses the typed binary relation carrier introduced at
✱21·02–03. `RelationIdentity` is pointwise formal equivalence; it does not use
Lean function equality. `RelationContext` records the identity-substitution
property needed by the printed context `f{R}`, and `RelationApplication`
retains the representative existentially within that context. In the
documented simple-type embedding, the predicative representative required by
✱21·151, ·16, and ·17 is the same typed binary matrix. No choice, classical
logic, relation-valued incomplete symbol, or function extensionality is used.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star21Q333Kernel.lean`
