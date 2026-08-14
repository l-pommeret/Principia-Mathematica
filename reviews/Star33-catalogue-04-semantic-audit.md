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
✱33·31's “Proof as in ✱33·3”. Their secondary Lean proofs close directly, so
their actual Lean and normalized graphs are empty. Those citations are
documented only as printed-but-unused relaxed closure; they are not inherited
as normalized proof edges.

## T1–T9 cumulative structural gate

No item in this five-locus split is a primary v1 proof. The declarations for
·26, ·27, ·29, and ·31 are ordinary `Prop` theorems over the host-language
relation model. They build no typed relational AST, expose no theorem whose
type is an inductive PM judgement, provide no concrete reading connecting the
printed text to that AST, and consume no PM derivation rules. They remain
correct secondary facts but return to `prepared` with the structural block.

✱33·28 retains its stronger semantic refusal because the host theorem also omits
the printed field equality. It independently fails the same structural gate.
There is no `Df` item in this lot. Creating a primitive constructor for any of
these derived propositions, wrapping the host `Prop`, or importing printed
citations into metadata without real calls would violate the dialogue's
axiom-free T1–T9 contract.
