# Q323 review — PM I ✱20·59–61

Leaf 228 / printed p. 206, SHA-256
`00ebce3fbb811f3b3bc84aeb2e09055c8153f894986e6f0269063a0a256a2612`,
and PG 78050 agree on all three uncited propositions.

`Star20Q323Kernel.lean` reuses the explicitly typed class carrier and
contextual class-description eliminator of ✱20·07–08.  ✱20·6 is the complete
class-quantifier duality theorem and uses `Classical.byContradiction` only for
its printed `¬∀¬ → ∃` direction.  ✱20·61 is unconditional universal
instantiation.  Both quantify over an arbitrary typed class carrier; neither
collapses classes into an untyped universe or assumes reducibility.

✱20·59 remains an exact target rather than a claimed assertion.  Its
`(ια)(fα)` is eliminated through `ClassDescriptionScope`; making it a freely
denoting Lean value would contradict PM's incomplete-symbol discipline.  A
proof needs the still unavailable assertion rules for class descriptions.
The metadata is therefore split: ✱20·6/61 await CI, while ✱20·59 stays
`prepared`.  The module adds no axiom, description choice operator, `sorry`,
`admit`, or unsafe declaration.
