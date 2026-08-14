# Q292 — ✱13·16–18

The first-edition scan and PG78050 agree on the five propositions at p. 178.
`Star13Q292Targets.lean` represents every endpoint in the intrinsically typed
object syntax: terms share one object sort and identity uses the signature's
equality meaning at one explicit assigned order. Conjunction, implication,
equivalence, and inequality expand only through PM negation and disjunction.

All five entries remain `prepared` at the explicit `pm-syntax-target` level.
The repository has syntax for identity
but no assertion layer implementing ✱13·01's quantification over predicative
functions or the reducibility route needed by its consequences. Native Lean
equality would prove analogous propositions but would not prove PM's defined-
in-use identity, so it is intentionally not substituted. In particular,
`EqualityMeaning` is vocabulary data rather than a theorem derived from
✱13·01, and the negated equality in ·18 is not by itself a certified
definition-normalization step for ✱13·02.

The audit is cumulative: ·16 depends on blocked ·11; ·17 depends on blocked
·1; ·171 and ·172 depend on blocked ·16 and ·17; ·18 depends on blocked ·17.
No target can therefore be promoted without fabricating a citation rule.

The three graphs were rebuilt from source. Compact citations `✱13·16·17` are
split into the two loci ·16 and ·17. The normalized PM graph is empty because
the current code performs no certified definition expansion. The Lean graph
contains only the `CoreFormula.equal`, `CoreFormula.neg`, and
`CoreFormula.disj` syntax constructors. No `Prop` theorem is primary, no
historical relaxation is claimed, and no item is `pm-derivation-v1`.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star13Q292Targets.lean`
