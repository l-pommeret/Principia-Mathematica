# ✱94 catalogue-01 semantic audit

The first five loci are checked against Project Gutenberg 78050 on printed
pages 620–621 (scan leaves 642–643). Their source IDs and displayed formulae
resolve uniquely to the declarations in `Star94Kernel.lean`.

No item is promotable. The kernel defines `Pot a` as the universal predicate,
independently of `a`, and its `Monoid` carrier assumes multiplication is globally
commutative. Consequently ✱94·12 and ·13 choose the input itself as witness and
obtain the displayed equation from global commutativity; this does not encode
PM's power classes or the relational-composition reasoning in the printed
proofs. The same collapse makes ·14 an equality between images of universal
sets, again discharged by global commutativity rather than the two preceding
relational-power propositions.

✱94·2 is even more direct: its conclusion is `True`, so the hypothesis and the
closure assertion carry no mathematical content. Finally, ·201 invokes the
custom field `Monoid.factor : ∀ a b x, ∃ y, x = a * y * b`; that field is the
existential conclusion being sought (up to equality orientation), while `Pot`
again supplies membership for free. It therefore assumes the printed converse
factorization instead of deriving it.

All five remain `prepared` with explicit semantic-block classifications. There
is no `awaiting-ci` split for this lot.
