# ✱54 targeted dependency reconciliation

This review records the direct source-term extraction for the nine requested
gates: ·21, ·22, ·26, ·27, ·271, ·41, ·411, ·42, and ·43. It changes no
statement, proof, semantic verdict, formal status, integration status, or CI
evidence.

| Locus | Extracted Lean edge(s) | Normalized edge(s) |
|---|---|---|
| ·21 | none | none |
| ·22 | ·21 | `PM1:✱54·21` |
| ·26 | ·25 | `PM1:✱54·25` |
| ·27 | ·25, ·26 | `PM1:✱54·25`, `PM1:✱54·26` |
| ·271 | ·27 | `PM1:✱54·27` |
| ·41 | ·4 | `PM1:✱54·4` |
| ·411 | ·41 | `PM1:✱54·41` |
| ·42 | ·41 | `PM1:✱54·41` |
| ·43 | ·26 | `PM1:✱54·26` |

For ·27 the extracted closure now agrees exactly with the two printed
citations. Every other non-exact printed/Lean closure is represented by an
item-level `relaxed-closure` record. In particular, ·21 retains PM's ✱51·41
as printed-but-unused; ·22 records local ✱54·21 as added and PM's ✱51·43 as
unused; and the uncited printed propositions record their actual earlier Lean
edge as added-beyond-print.
