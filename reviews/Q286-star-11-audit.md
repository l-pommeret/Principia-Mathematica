# Q286 audit — PM I ✱11·57–✱11·59

The three declarations in `Star11Q286Kernel.lean` preserve every displayed
binder and connective. Because each printed matrix is unary and is repeated
at both `x` and `y`, both apparent variables have one common Lean argument
type. Juxtaposition is `And`, formal implication is universal implication,
and PM equivalence is `Iff`.

All proofs are constructive and unconditional, including for an empty
argument type: the reverse directions use the same arbitrary argument in
both displayed positions rather than postulating an inhabitant. No axiom,
classical principle, `sorry`, `admit`, semantic stub, or weakened theorem is
introduced. The historical citations remain recorded verbatim as printed
dependencies in metadata.
