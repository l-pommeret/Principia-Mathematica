# Q322 exact extensional-class audit

Leaf 227 (p. 205), SHA-256
`9c5ce356cfecdac160d92cb3137eb787e445c4f37afdb46b6742dfb3de1da101`,
and PG 78050 witness the five class/description propositions.

`Star20Q322Kernel.lean` represents a class over `ι` only by its membership
predicate `ι → Prop`. The class abstract `ẑ(φz)` is therefore `φ`, and its
identity is predicate equality obtained from the complete displayed formal
equivalence by function and proposition extensionality. A class description
is never a term: `descriptionEquals`, `descriptionExists`, and
`descriptionApplies` retain the complete Russellian contextual propositions.

All five declarations preserve every displayed binder and connective. They
are polymorphic and require no inhabitedness or choice. No new axiom,
`Classical`, `sorry`, `admit`, semantic placeholder, total description
operator, or weakened target is introduced.
