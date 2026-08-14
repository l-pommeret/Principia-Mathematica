# ✱31 catalogue 01 strict semantic audit

Scope: exactly ✱31·01, ·02, ·1, ·101, and ·13.  Their catalogue readings
match the literal PG78050 blocks in `Star31Source.lean`.

No item in this lot is promotable.  ✱31·01 and ·02 are printed definitions,
but the repository has no numbered Lean declaration for either definition;
the unnumbered infrastructure definitions `Cnv`, `converse`, and `IsConverse`
do not by themselves constitute audited implementations of both PM class
abstracts.  Likewise ·1 and ·101 have no corresponding theorem declarations,
so theorem-name proximity elsewhere cannot supply a source↔Lean certificate.

✱31·13 has a named candidate, but it is not equivalent.  PM asserts
contextual existence of the descriptive value `CnvʻP`.  Lean's
`∃ Q, IsConverse Q P` merely exhibits a relation extension satisfying the
converse predicate; it does not encode the incomplete symbol, its description
scope, or its denotation condition.  This is exactly the mismatch already
identified by the strict opening audit.

All five records remain `prepared` and are marked blocked with their explicit
refusal reason.  There is no accepted Lean dependency graph for this lot and
no item is promoted to `awaiting-ci`.
