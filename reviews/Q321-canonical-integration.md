# Q321 canonical audit — PM I ✱20·35, ✱20·4, ·41, ·42, ·5

`Star20Q321Kernel.lean` covers all five propositions on first-edition scan
leaf 226. Classes are type-relative characteristic predicates; `Cls` contains
exactly predicate extensions of the appropriate element type, so no untyped
universal class is introduced.

✱20·35 is proved in both directions. The reverse direction instantiates the
universal class variable with `fun z => z = x`, giving the constructive
Leibniz argument. ✱20·4 unfolds `Cls`, ✱20·41 provides the displayed predicate
as witness, and ✱20·42 is definitional reduction.

At ✱20·5 the description remains an incomplete symbol. Both sides share the
same existentially unique witness `b`; the left performs membership in the
extension of `ψ`, while the right applies `ψ` to that witness. No description
term or choice operation is introduced.

No declaration uses an axiom, `sorry`, `admit`, `unsafe`, or a classical
principle. The earlier source-only review remains preserved as provenance.
