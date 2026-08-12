# Q316 — ✱20·43 exact integration audit

The canonical witness is first-edition volume I, scan leaf 221, printed page
199 (SHA-256 `4c9f5a7f6390862ba62b7c9bba72a65ced25c2c6ed09e80af94f83f9d3ed18ee`).
The source restates ✱20·18 and ✱20·3 immediately beside ✱20·43; these are its
two historical ingredients.

`TypedClass α := α → Prop` retains PM's type restriction: both classes and
their possible member share one explicit carrier. `Member x a := a x` is the
exact membership reading. The theorem states the displayed class equality if
and only if pointwise membership equivalence, with formal subscript `x`
represented by `∀ x`.

The forward direction is equality elimination. The reverse direction uses
Lean's standard propositional and function extensionality. The module adds no
axiom declaration, choice, inhabitance premise, decidable equality,
placeholder, unsafe escape hatch, or untyped membership relation.
