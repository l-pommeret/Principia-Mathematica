# Q282 PM-derivation migration — ✱11·39, ·391, ·4, ·401, ·41

The five diplomatic statements now have exact cumulative `Raw` endpoints in
`Star11Q282Kernel.lean`. They reuse the two-binder encoding established by
Q280 and construct implication, conjunction, equivalence, and existential
disjunction entirely in PM object syntax. The former Lean proofs remain under
`_prop` names solely as modern semantic readings.

No endpoint is a judgement of an inductive PM derivation relation. The printed
chains require higher-arity composition through ✱11·31/·32/·33 or composite
✱10 citations, several of which are themselves target-only after strict audit.
Accordingly target construction and direct Lean reasoning do not justify
`pm-derivation-v1`.

Graphs were rebuilt from zero. `printed_dependencies` reproduces each printed
bracket or demonstration, including unexpanded composite labels. Because no PM
derivation theorem is called by an endpoint definition, `lean_dependencies`
and `normalized_dependencies` are empty for all five items. The old relaxed
closures and stale CI evidence are removed; every item is prepared and blocked.
