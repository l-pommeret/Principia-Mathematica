# Q292 — ✱13·16–18

The first-edition scan and PG78050 agree on the five propositions at p. 178.
`Star13Q292Targets.lean` represents every endpoint in the intrinsically typed
object syntax: terms share one object sort and identity uses the signature's
equality meaning at one explicit assigned order. Conjunction, implication,
equivalence, and inequality expand only through PM negation and disjunction.

All five entries remain `prepared`. The repository has syntax for identity
but no assertion layer implementing ✱13·01's quantification over predicative
functions or the reducibility route needed by its consequences. Native Lean
equality would prove analogous propositions but would not prove PM's defined-
in-use identity, so it is intentionally not substituted.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star13Q292Targets.lean`
