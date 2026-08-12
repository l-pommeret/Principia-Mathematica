# Q335 review

Leaf 241 (p. 219), SHA-256 `b5b35b1cc45089a30e8970307349350009e4b19d03cf155212a95079c0df9312`, collated with PG 78050.

`Star21Q335Kernel.lean` represents all five formulas with heterogeneous
relations `α → β → Prop`, so the two argument types remain explicit. ✱21·32
and ✱21·42 are strict application/re-abstraction reductions. ✱21·33 is the
full extensional equality equivalence. ✱21·4 keeps a predicative relation
code distinct from its extension; ✱21·41 supplies the local typed code
witness licensed by ✱21·151, without weakening the printed theorem into a
conditional result.

No untyped universal relation, reducibility axiom, choice-created code, or
placeholder is introduced. Targeted Lean 4.30.0 check:

```text
lake env lean Principia/Architecture/Star21Q335Kernel.lean
```
