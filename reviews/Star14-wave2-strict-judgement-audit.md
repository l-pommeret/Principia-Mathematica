# PM I ✱14 wave 2 strict syntax/judgement audit

This five-item wave applies the Star 2 / T1–T9 boundary without introducing a
`Support` hypothesis, semantic oracle, new axiom, or total description term.

## Accepted reductional definitions

✱14·02, ·03, and ·04 are complete at the reductional syntax level. Each theorem
is an equality in the intrinsically typed `DescriptionSyntax.Formula` API and
has body `rfl`. Their left- and right-hand sides are the complete printed `Df`
expressions; in particular, the catalogue readings for ·03 and ·04 now include
their previously omitted definientia. These items print no theorem citations
and call no Lean theorem, so both dependency graphs are empty.

## Assertions retained as prepared

✱14·18 and ·21 are not PM kernel assertions. `Star14Q297Kernel` defines
`DescriptionExists` and `DescriptionApplies` as Lean `Prop` predicates, and its
two theorems prove ordinary semantic implications. No inductive judgement is
indexed by `DescriptionSyntax.Formula`, and neither theorem returns such a
judgement. These Prop results may remain secondary mathematical evidence but
cannot establish the printed turnstile.

The printed graph was rebuilt directly from the demonstrations:

- ✱14·18 uses ✱10·1, `Fact` (✱3·45), ✱10·11·28, ✱10·35, and
  ✱14·1·11.
- ✱14·21 uses ✱14·1, ✱10·5, and ✱14·11.

The Lean theorem bodies call no PM proof theorem, so their `lean_dependencies`
and `normalized_dependencies` are empty. No relaxed closure is claimed.
