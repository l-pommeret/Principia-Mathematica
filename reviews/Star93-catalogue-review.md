# ✱93 source catalogue review

The fifty-five loci are checked against Project Gutenberg 78050 on printed
pages 609–616 (scan leaves 631–638). The source and Lean declarations form a
duplicate-free 55/55 bijection. The first five-item lot (✱93·01, ·02, ·021,
·03, and ·1) has passed strict item-level semantic audit and is promoted in
place to `awaiting-ci`; the other fifty items remain `prepared` pending
semantic promotion.

The parser accepts 20 formulas; 35 historical inductive-analysis formulas carry `reviewed-gap`.

## Strict semantic audit: catalogue 01

All five diplomatic blocks agree with their catalogue records. `Rel α` keeps
both relation arguments, `dom P` and `cod P` are respectively PM's domain and
converse-domain, and `image` uses the established PM output-first convention.
Consequently `image (converse P) A` is exactly the printed `P̌ʻʻα` reading in
the minimum definition, with no reversal silently removed.

✱93·01 defines `boundary P` as membership in `DʻP − ᗡʻP`, and ✱93·1 is its
exact pointwise expansion. ✱93·02 defines `minimum P A` as membership in
`A ∩ CʻP − P̌ʻʻA`; every conjunct and the negated relational-image clause is
present. ✱93·021 is definitionally `minimum (converse P)`, exactly the printed
definition of `max(P)`. ✱93·03 represents the variable class family abstractly
as `F` and says precisely that a generated class is the minimum of some member
of that family; the abstraction changes no quantifier or equality.

The accepted declaration bodies are definitional (`Iff.rfl`/`rfl`). They call
no numbered proposition, and these source lines print no proof citations, so
the historical, Lean, and normalized dependency graphs are all empty for this
lot. No item is refused. CI evidence remains pending; none of the five is
labelled `kernel-checked` by this audit.
