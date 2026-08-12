# Q319 exact class-extension audit

The five propositions on PM I p. 202 are formalized in
`Star20Q319Kernel.lean`. A class extension is represented explicitly as a
predicate `α → Prop`, and a displayed function of classes as a predicate on
those extensions. This is the documented simple-type collapse; it proves the
complete endpoints in that interpretation without claiming to reconstruct
PM's ramified hierarchy.

✱20·16 uses `ψ` as its predicative witness. ✱20·17 retains that witness and
specializes the universal premise. ✱20·18 is equality elimination. ✱20·19 and
✱20·191 prove both directions of Leibniz identity by instantiating the
quantified class predicate with equality to `ψ`.

All parameters remain polymorphic. There is no inhabitance assumption,
decidable equality, classical principle, placeholder, new axiom, or unsafe
escape. The batch is ready for CI after targeted Lean 4.30.0 compilation.
