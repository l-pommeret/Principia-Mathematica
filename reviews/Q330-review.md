# Q330 exact relation-definition audit

Leaf 236 (p. 214), SHA-256
`b53401d40fe6689ff7e91331cd88c16d29f900dcae13705cedfd2def034fbeae`,
collated with PG 78050, witnesses ✱21·07, ·071, ·072, ·08, and ·081.

`Star21Q330Definitions.lean` retains a binary relation as a genuinely
two-place predicate with independently typed arguments. ✱21·07 and ·071
quantify over these predicates. ✱21·072 keeps the relation description
contextual as the printed unique-characterization matrix and continuation;
it introduces no choice term. ✱21·08 retains both relation arguments of the
higher matrix and its explicit extensional representative. ✱21·081 is the
exact application reduction at `P,Q`.

These eliminative definitions require no `Classical`, choice, new axiom,
`sorry`, oracle, or collapse from a binary relation to a unary predicate.

## Non-v1 wave-2 gate

The five items were rechecked under the rule that a printed `Df` must be a
genuine unfolding, while a printed proposition would need an object-level PM
judgment derived from T1–T9 or earlier theorems. No archived `Support`
prototype is imported or referenced.

Items ·07, ·071, ·072 and ·08 pass as axiom-free non-v1 definitions. Their
Lean declarations are definitions whose bodies are exactly the typed
universal, existential, contextual-description and higher-relation expansions
printed on p. 214. As definitions they need no assertion derivation.

Item ·081 does not pass. PM defines application of the higher relation abstract
at `P,Q`; Lean instead states only `φ P Q ↔ φ P Q`. This theorem has no
definiendum and cannot serve as a definitional unfolding. It remains blocked
until a named application operation is defined and its reduction is exposed.

All five printed items are uncited definitions, and none of the four accepted
bodies calls a PM derivation theorem. Their printed, Lean and normalized
dependency graphs are therefore empty. The blocked reflexivity theorem also
has an empty call graph, but that absence supplies no missing definition.
