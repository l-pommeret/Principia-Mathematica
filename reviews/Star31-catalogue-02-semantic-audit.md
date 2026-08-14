# ✱31 catalogue 02 strict semantic audit

Scope: exactly ✱31·131, ·132, ·16, ·17, and ·18.  Their catalogue readings
match the literal PG78050 blocks in `Star31Source.lean` and were checked
against `Star31ConverseKernel.lean` and `Star31ConverseKernel2.lean`.

All five typed reconstructions pass strict equivalence.  ·131 is converse
evaluation.  ·132 retains the full chained characterization: being converse
to `P`, equality with `Cnv P`, and equality with the explicit converse.
·16 is extensional distribution over relation complement.  For ·17 and ·18,
the private contextual predicates spell out exactly the printed scoped
definiens `∀ z, P x z ↔ z = y` and its existential closure; the declarations
do not replace descriptive existence by mere existence of an arbitrary
relation.

Every proof closes from the displayed typed definitions, so its direct Lean
theorem dependency list is empty.  The printed citations remain historical
edges under reviewed `relaxed-closure` records, with no dependency introduced
beyond print.  Exactly these five items are promoted to `awaiting-ci`; CI
evidence remains pending.
