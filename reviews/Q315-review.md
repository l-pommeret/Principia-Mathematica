# Q315 review

Leaf 220 (p. 198), SHA-256 `00e5a8494d0ae3847d5fa3746b33ca015f83c7515d19dd352f44f9ffee4b802d`, plus PG 78050, collates ✱20·03.

`Star20Q315Definition.lean` gives the exact reductional reading. A class of
`α` is represented extensionally as `α → Prop`, while `Cls` has carrier
`Class (Class α)`: the type separation is explicit and no untyped universal
class is introduced. The predicative functions `φ!` are indexed by an
abstract code type `κ` and interpreted by a supplied representation map.
Consequently the definition does not collapse arbitrary propositional
functions into predicative functions. The displayed equality is proved by
strict reduction (`rfl`), with no axiom or placeholder.

Targeted Lean 4.30.0 check:

```text
lake env lean Principia/Architecture/Star20Q315Definition.lean
```
