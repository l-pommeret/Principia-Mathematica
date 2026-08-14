# ✱33 catalogue 03 strict semantic audit

Scope: exactly the five items ✱33·18, ·21, ·22, ·24, and ·25, compared with
their verbatim transcriptions and the declarations in
`Star33DomainKernel2.lean`.

All five pass strict equivalence. ✱33·18 preserves the printed hypothesis that
domain and converse-domain agree and concludes equality of domain and field.
✱33·21 and ·22 are respectively the domain/converse-domain identity and field
invariance under relational converse. ✱33·24 represents the printed chained
equivalence by the three adjacent biconditionals joining existence of domain,
converse-domain, field, and relation; this retains every displayed link.
✱33·25 proves exactly the printed inclusion from the domain of pointwise
relation intersection to the intersection of the two domains, using the same
witness for both projections.

The declarations close from local definitions and hypotheses without numbered
Lean dependencies; the printed catalogue likewise records no citations. Their
actual Lean and normalized graphs are therefore empty, with no inherited edge.

## T1–T9 structural gate

All five are blocked as primary v1 formalizations. The declarations are
ordinary Lean `Prop` theorems over semantic functions `Domain`,
`ConverseDomain`, `Field`, `Converse`, and `Inter`. None has an object-language
relational AST as endpoint, none is a theorem of an inductive PM judgement,
and none consumes PM inference rules. The `Prop` statements remain valid and
useful secondary lemmas only.

The missing AST structure is substantive: ·18 needs implication between two
relation/class equalities; ·21 and ·22 need converse nested under domain/field;
·24 needs the complete chained equivalence of four existence assertions; and
·25 needs inclusion with relation and class intersection at distinct syntactic
levels. An opaque atom or a primitive constructor for any derived proposition
would fail the non-vacuity and axiom-free gates.

Accordingly all five remain `prepared` with
`blocked-missing-pm-ast-judgement-derivation`. There are no printed citations
to consume in this lot, so all three dependency graphs are exactly empty.
