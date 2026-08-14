# PM II ✱113 catalogue-02 strict semantic audit

The second opening lot covers exactly ✱113·106, ·107, ·11, ·111, and ·112
on first-edition volume II p. 109 (scan leaf 149).  The source formulas were
checked against the scan with Project Gutenberg 78255 as control.  The audit
compares the represented object and complete theorem type, not merely the
resulting truth of a weaker set-theoretic statement.

✱113·106 and ·107 are exact and are the only `awaiting-ci` records.  The first
is precisely ordered-pair introduction into the class product.  The second
constructs a product member from members of both factors, exactly preserving
PM's existence implication; its Lean proof explicitly uses the namesake ·106.

The remaining three namesakes are refused:

- ✱113·11 states two cardinality results about the family of alpha-fibres
  indexed by beta.  Lean only constructs each fibre predicate and provides no
  similarity/cardinality statement.
- ✱113·111 classifies that family as a mutually exclusive class of classes.
  Lean merely wraps the flattened `Product` predicate in a trivial existential
  equality; neither the indexed family nor exclusion is represented.
- ✱113·112 says that, for empty alpha and existent beta, the fibre family is
  the singleton of the empty class.  Lean proves only that the flattened
  product is empty, which discards the essential outer singleton layer.

Exact and refused records are disjoint, and each of the five canonical IDs has
one metadata record and one `PM-VERBATIM` source block.

All five diplomatic readings are deliberate parser gaps.  Each contains the
ordered-couple/fibre operator `↓` or the class-product sign `×`, neither of
which the current deterministic statement grammar accepts.  Their exact
printed readings are preserved and the limitation is recorded as
`reviewed-gap` with this audit as evidence.
