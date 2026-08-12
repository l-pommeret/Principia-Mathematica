# Q317 exact reduction audit

Leaf 222 (p. 200), SHA-256
`74e5b9dee4e728f97749b6d49c0effa705f35c7738da608bc358a5855c656ff9`,
witnesses the five definitions ✱20·07, ✱20·071, ✱20·072, ✱20·08,
and ✱20·081.

`Star20Q317Definitions.lean` represents a class extensionally by its
characteristic predicate. Universal and existential class quantifiers become
the printed quantifiers over predicative characteristic functions. The class
description remains contextual: `ClassDescriptionScope` is exactly the
existential unique-representative expansion, never a description-valued term.
✱20·08 retains its existential predicative representative and formal
equivalence over `alpha`; ✱20·081 is the literal membership/application
reduction.

All five declarations are definitional equalities checked by `rfl`. They add
no class-existence or reducibility axiom, choice operator, placeholder, unsafe
feature, or theorem about arbitrary representatives.
