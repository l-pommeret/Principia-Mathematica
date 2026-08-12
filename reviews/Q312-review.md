# Q312 review — exact targets, ramified assertion block retained

First-edition volume I, p. 195 / scan leaf 217 (SHA-256
`3de7db07114e89214c85961210e178d53f4a2de8e5d6080c62f6b4914172e1bc`)
and PG 78050 agree on ✱14·33, ·331, ·332 and ·34.  The earlier
metadata shortened every printed formula after its first scoped member.  It
now preserves each full displayed equivalence.

`Principia/Architecture/Star14Q312Targets.lean` gives all four exact typed
targets.  The proposition variable `p` is an explicit `Formula` at the same
assigned order; moving it beneath a description bracket uses capture-free
weakening.  The module distinguishes implication/equivalence inside a scope
from the corresponding connective outside it and never turns the description
into a `Term`.

Lean 4.30.0 accepts the module, but these definitions are not assertions.
PM's surrounding prose treats `p` as an apparent proposition variable, whose
formal assertion requires the ramified proposition hierarchy and reducibility
principle not present in the current description calculus.  Accordingly all
four items remain `prepared` and architecture-blocked.  No axiom, reducibility
oracle, `Prop` interpretation, assertion constructor, `sorry`, or `admit` is
introduced.
