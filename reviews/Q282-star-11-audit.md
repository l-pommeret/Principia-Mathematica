# Q282 audit — PM I ✱11·39–✱11·41

The five declarations in `Star11Q282Kernel.lean` preserve the displayed
two-variable scope: each PM matrix is a predicate `α → β → Prop`, and every
formal assertion quantifies both arguments. Juxtaposition is represented by
`And`, implication by `→`, equivalence by `↔`, and existence by two nested
`Exists` binders.

The proofs are unconditional. In particular, ✱11·41 does not assume either
argument type is inhabited: each direction transports the witnesses already
present in the relevant existential. No axiom, classical principle,
`sorry`, `admit`, or unsafe escape hatch is used.

Source comparison against first-edition scan leaf 185 confirms that Q282 is
exactly ✱11·39, ✱11·391, ✱11·4, ✱11·401, and ✱11·41. The formal theorem
types cover every displayed connective and binder; the demonstrations'
historical citations remain recorded as `printed_dependencies` in metadata.
