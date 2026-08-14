# ✱112 catalogue 04 — strict source/Lean semantic audit

The five source statements on PM II p. 101 were compared literally with their
declarations across `Star112OpeningKernel.lean` and
`Star112MiddleKernel.lean`.

All five are refused. At ·17 Lean omits the printed similarity conclusion and
uses equivalence of nonemptiness in place of cardinal similarity. At ·18 it
replaces the stated equality with `SumCard K = SumCard K`. At ·2 it discards
the one-one relation and its domain/range hypotheses and returns an arbitrary
`EqCard` hypothesis. At ·21 the multiplicative axiom and complete existence
equivalence disappear into `P ↔ Q → P ↔ Q`. At ·22 the desired cardinal-sum
equality is taken as an arbitrary equality hypothesis.

The strict promoted set is 0/5. The records remain `prepared` in the single
homogeneous manifest `PM2-STAR112-CATALOGUE-04-REFUSED`; no awaiting-CI lot is
created. No bracketed numbered citations occur in these source blocks and the
Lean declarations cite no numbered propositions, so all three proposition-
dependency graphs remain empty.
