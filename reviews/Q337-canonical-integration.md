# Q337 canonical audit — PM I ✱21·58, ·6, ·61, ·62, ·63

The module `Star21Q337Kernel.lean` introduces a typed heterogeneous binary
relation `α → β → Prop`, so relation variables and their two argument types
cannot be confused with unary classes or propositions.

✱21·58 is expanded contextually: it exhibits the unique relation `R` equal
to the displayed extension and proves that the extension equals that witness.
No total description term or choice operator is introduced. ✱21·6 is the
classical quantifier-negation equivalence printed by PM. ✱21·61 is universal
instantiation. ✱21·62 explicitly ranges over extensions of binary predicates
before generalizing to an arbitrary relation. ✱21·63 uses the same classical
case split on the fixed proposition `p` as its unary analogue.

All five targets preserve the binders and connectives on first-edition scan
leaf 237. The two explicitly classical results use Lean's theorem-level
classical reasoning, not a new axiom. There is no `sorry`, `admit`, `unsafe`,
or semantic narrowing. The earlier source review remains intact.
