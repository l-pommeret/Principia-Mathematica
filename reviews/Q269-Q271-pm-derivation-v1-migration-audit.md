# Q269–Q271 strict `pm-derivation-v1` migration audit

Scope: ✱10·251, ·252, ·253, ·33, and ·34.  The mandatory standard is
`Principia/FirstEdition/Volume1/Part1/SectionA/Star2.lean`; the T1–T9 gates are
those recorded in `dialogue.md`.

All five declarations resolve in the import closure and are axiom-free.  None
passes the remaining derivation gates.  Every public declaration is a `def`,
not a `theorem` (T2); every result type is a theorem-specific `structure`, not
an inductive object-calculus judgement (T3); and none has a companion
`*_reading` linking its exact printed string to parsed PM syntax (T4).  The
`reading` fields inside these structures are only reflexive equalities of the
form `target = target`, which are not printed-formula readings.

The source citation graph remains recorded independently in metadata.  The
Lean call graph was rebuilt from the public bodies and their one explicit
component helper:

- ·251 calls ·25 and a closed negated-existential normalization;
- ·252 calls no earlier PM proposition; it packages only
  `NormalizesScoped.negSometimes` and a reflexive target equality;
- ·253 calls no earlier PM proposition; it packages only
  `NormalizesScoped.negAlways` and a reflexive target equality;
- ·33 calls `star_10_33_composition`, whose body calls ✱10·1, ✱3·26,
  ✱3·27, and the ✱10·11·21 action.  These prove fields of a component record,
  not the displayed endpoint;
- ·34 calls no earlier PM proposition; its body packages binder extraction,
  negated-universal normalization, and a reflexive target equality.

There is no `Support` wrapper and no target-specific constructor masquerading
as a PM rule.  The normalization evidence is retained as useful secondary
syntax evidence, but does not establish assertion of the displayed formula.

Verdict: all five items are `prepared`, with
`formalization_level = pm-ast-component-certificate-v1`, and blocked on a real
theorem-level PM endpoint judgement plus printed reading.  None receives
`pm-derivation-v1`.
