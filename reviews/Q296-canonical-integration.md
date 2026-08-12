# Q296 canonical audit — PM I ✱14·01

`Principia/Architecture/Star14Q296Kernel.lean` inserts the exact reviewed
declaration `PM.DescriptionSyntax.Formula.star_14_01` against the canonical
`Principia.Syntax.Description` implementation. Its signature is identical to
the isolated Q296 target: `Formula.descriptionScope` is expanded to the
existential conjunction of `CoreFormula.uniquely condition.expand` and
`continuation.expand`.

The theorem body is exactly `by rfl`. It therefore records definitional
reduction only: it does not cite `expand_descriptionScope`, add a semantic
model, turn the description into a term, or introduce any theorem dependency.
The prior interface reports and retry prompt are historical provenance and
remain untouched.

This removes the former one-to-one remap blocker locally. Promotion remains
`awaiting-ci` until the canonical module is checked by an immutable online
run. No axiom, `sorry`, `admit`, `unsafe`, or classical principle occurs.

Dependency promotion simulation extracts `PM.Elementary.conj`, the canonical
syntax realization of ✱3·01 used inside the unfolded contextual definition.
Because ✱14·01 prints no proof citation, this is recorded explicitly as an
added definitional dependency rather than hidden. The simulated item passes;
its status remains `awaiting-ci`.
