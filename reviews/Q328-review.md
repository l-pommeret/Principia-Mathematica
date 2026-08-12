# Q328 exact binary-relation definitions

Leaf 234 (p. 212), SHA-256
`a3d9953b15fa5cbedfada0791e2cc2b64eb6b499e6526d61443c174a1a01a2b2`,
was collated with PG78050.

`Star21Q328Definitions.lean` gives the two complete definitions in the same
explicit simple-type interpretation already used for binary predicative
functions. A relation extension has carrier `α → β → Prop`. Thus ✱21·02 is
definitionally its application to `a,b`, while ✱21·03 is the predicate saying
that an extension equals the extension of some predicative binary function.

Both reductions are separately checked by `Iff.rfl`. This is an explicit
collapse of PM's ramified distinction, not a claim that the original hierarchy
identified functions and their extensions. Argument order and the two possibly
different sorts are retained. No extensionality, classical principle, axiom,
placeholder, or unsafe declaration is used.
