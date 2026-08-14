# ✱41 catalogue 08 strict semantic audit

The five domain, converse-domain, and field laws ✱41·4–44 were compared with
the explicit definitions in `Star41RestrictionKernel.lean` and
`Star41FinalKernel.lean`. The product is universal intersection, the sum is
existential union, and domain/range/field have their ordinary pointwise typed
meanings.

✱41·4, ·41, and ·42 preserve the printed one-way inclusions for product
relations; Lean does not strengthen these silently to equality. ✱41·43 and
·44 preserve the printed equalities for sums, with both directions proved.
No conclusion is passed as a hypothesis and no quantifier is narrowed. All
five declarations are exact and are promoted to `awaiting-ci`.
