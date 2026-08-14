# ✱112 catalogue 03 — strict source/Lean semantic audit

The five source statements on PM II pp. 100–101 were compared literally with
`star_112_15`, `star_112_151`, `star_112_152`, `star_112_153`, and
`star_112_16` in `Star112OpeningKernel.lean`.

All five are refused. At ·15 Lean removes the exclusive-class hypothesis,
replaces the tagged sum by an untagged union, and models equinumerosity only by
equivalence of nonemptiness. At ·151 the two desired domain equalities are
supplied as arbitrary hypotheses. At ·152 Lean assumes the arbitrary equality
it returns. At ·153 and ·16 the printed relational/function constructions are
absent and an arbitrary `EqCard` hypothesis is merely returned unchanged.

The strict promoted set is 0/5. The records remain `prepared` in the single
homogeneous manifest `PM2-STAR112-CATALOGUE-03-REFUSED`; no awaiting-CI lot is
created. These source blocks contain no bracketed numbered citations, and the
Lean declarations cite no numbered propositions, so the printed, normalized,
and Lean proposition-dependency graphs remain empty.
