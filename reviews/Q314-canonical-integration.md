# Q314 canonical audit — PM I ✱20·01–✱20·02

`Star20Q314Definitions.lean` gives an eliminative encoding of the two printed
definitions. It deliberately introduces no type of class objects. A
`ClassContext α` accepts only a `PredicativeMatrix α`; hence ✱20·01 is exactly
the proposition that there exists a predicative `φ!`, pointwise equivalent to
the arbitrary matrix `ψ`, for which the displayed context holds.

The distinction between `Matrix` and `PredicativeMatrix` is retained in the
Lean types rather than erased by treating every predicate as already
predicative. No reducibility theorem is assumed or proved: `star_20_01` merely
records PM's definiens. Likewise `star_20_02 x φ` reduces definitionally to
`φ.apply x`, exactly matching `x ε (φ!ẑ) .= φ!x`.

Both declarations are definitions, not semantic existence claims. They use no
choice, quotient, set theory, axiom, `sorry`, `admit`, or unsafe escape hatch.
The source text remains witnessed by first-edition scan leaf 219 and PG78050.
