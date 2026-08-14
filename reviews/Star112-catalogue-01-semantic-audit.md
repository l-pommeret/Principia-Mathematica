# ✱112 catalogue 01 — strict source/Lean semantic audit

Scope: the three prepared loci now classified in the homogeneous batch
`PM2-STAR112-CATALOGUE-01-REFUSED`, checked against
their literal PM II source blocks on printed pages 99 and 102 and against the
corresponding declarations in `Star112OpeningKernel.lean`. Promotion requires
the Lean proposition to retain every substantive operator and equality in the
printed proposition; a matching name or reflexive surrogate is insufficient.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱112·02 | `star_112_02` | refused | PM defines `ΣNcʻκ` as `NcʻΣʻκ`, i.e. the cardinal number of the sum class introduced at ·01. Lean instead defines `SumCard` from the untagged union `fun x => ∃ A, K A ∧ A x`; its theorem merely unfolds that different definition. The missing tag changes cardinality when classes overlap. |
| ✱112·1 | `star_112_1` | refused | PM identifies the sum class with the union of the membership relation restricted to `κ`. Lean proves only `SumClass K = SumClass K`, so the printed relational expansion is absent. |
| ✱112·101 | `star_112_101` | refused | PM states the chain `ΣNcʻκ = NcʻΣʻκ = Ncʻsʻ∈↧ʻʻκ`. Lean proves only `SumCard K = SumCard K`; neither cardinal-number target nor the expanded sum-class expression occurs. |

Thus the strict promoted set is 0/3 and no awaiting-CI manifest is created.
All three loci remain `prepared` in that single canonical refused manifest;
they cannot count toward source-critical coverage.

The normalized printed dependency graph records ·02 → ·01 and ·101 → ·01,
·02, because those are the definitions whose equality chain is being expanded.
The current Lean declarations cite no numbered proposition. This mismatch is
documented rather than relaxed: the empty Lean graphs reflect the local
reflexive implementations, not historical derivations of the printed results.
