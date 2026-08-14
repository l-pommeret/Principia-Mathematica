# ✱95 catalogue 02 strict semantic audit

The next five loci in printed order are ·131, ·132, ·14, ·21, and ·211
(printed pages 627–628, scan leaves 649–650). Their canonical readings were
checked against Project Gutenberg 78050 and the first-edition facsimile. The
five IDs are new and form a duplicate-free source↔Lean mapping.

The lot is split by verdict so metadata status remains homogeneous. The first
three declarations pass strict equivalence and are `awaiting-ci`: ·131 is one
generator step from the seed, ·132 is closure under that generator, and ·14 is
the strong induction rule whose step retains both generated membership and the
induction hypothesis. The printed proof graph and Lean constructor/eliminator
graph are recorded separately with reviewed historical relaxations.

The other two items remain `prepared` and are explicitly refused. Lean's
`star_95_21` concludes only `∃ n, Equi P Q R M`, leaving `n` unused; it does
not produce power relations `S,T` or the equation `M=S|R|T`. Lean's
`star_95_211` merely returns a relation equal to `M`; it omits PM's
range/domain premise, the power/potent constraints and the factorization.
Neither tautological wrapper is promoted. The parser route remains
`reviewed-gap` for the historical power and relational-factor notation.
