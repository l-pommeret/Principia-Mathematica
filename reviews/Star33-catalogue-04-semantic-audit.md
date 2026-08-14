# ✱33 catalogue 04 strict semantic audit

Scope: exactly the five items ✱33·26, ·27, ·28, ·29, and ·31, checked against
the diplomatic formulas and their declarations in `Star33DomainKernel3.lean`
and `Star33DomainKernel4.lean`.

Four items are exact. ✱33·26 distributes domain over relational union. ✱33·27
identifies the field with the domain of the union of a relation and its
converse. ✱33·29 retains all three adjacent null-relation equalities for domain,
converse-domain, and field. ✱33·31 retains both directions of the converse-
domain inclusion/existence characterization.

✱33·28 is refused. Print gives the chain
`DʻV = ᗡʻV = CʻV = V`; Lean proves only that the domain and converse-domain of
the universal relation are universal. Its conclusion contains no equality for
the field, so it is a strict omission rather than an equivalent typed scope.
The refused item is split into `PM1-star-33-catalogue-04-refused.json`.

The historical graph records ✱33·29's citations to ✱33·241 and ✱21·2 and
✱33·31's “Proof as in ✱33·3”. Their Lean proofs close directly, so those edges
are documented as printed-but-unused relaxed closure. Promote only ·26, ·27,
·29, and ·31 to `awaiting-ci`.

