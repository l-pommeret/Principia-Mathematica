# Q329 review — ✱21 summary locus

Leaf 235 (p. 213), SHA-256
`77757ee9fdf28020538573172873f924f0fe82a0b707de1d7209906ab65be6f1`,
and PG78050 agree that the five displayed lines are a summary of ✱21·15,
✱21·31, ✱21·43, ✱21·3, and ✱21·151.

No canonical item, metadata batch, demonstration, or Lean theorem is created
for Q329. Doing so would duplicate the same PM IDs and detach them from their
later detailed proof loci. The diplomatic container therefore uses only
`PM-VERBATIM-SUMMARY` blocks; formalization belongs to the batches containing
the canonical occurrences. This is an intentional source-critical no-op, not
an architecture blocker or an omitted proof.

Targeted check (Lean 4.30.0):

`lake env lean Principia/FirstEdition/Volume1/Star21Source.lean`
