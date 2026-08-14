# ✱115 catalogue 01 — strict source/Lean semantic audit

Scope: the first five loci of PM II ✱115 (·01, ·02, ·1, ·101, and
·11), checked against Project Gutenberg 78255 and the 1912 Volume II witness,
printed page 136 (scan leaf 176). Promotion compares the displayed proposition
with the full Lean theorem type; a shared locus number or topic is insufficient.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱115·01 | `star_115_01` | exact, awaiting CI | `ClassProduct F := (i : I) → F i` is the typed dependent-function presentation of PM's class of simultaneous selections, and the theorem states that defining identity without an added premise. |
| ✱115·02 | `star_115_02` | refused | PM requires mutual exclusivity of both κ and its union; `ArithmeticFamily F` instead means that every `F i` is inhabited. |
| ✱115·1 | `star_115_1` | exact, awaiting CI | This is the same product defining identity as ·01, now asserted as a proposition. |
| ✱115·101 | `star_115_101` | refused | PM starts from an arbitrary class and sufficient singleton-intersection/support hypotheses; Lean starts with an already typed product element and proves only `f = f`. |
| ✱115·11 | `star_115_11` | refused | PM states the converse characterization of product membership, whereas Lean supplies only `∀ i, f i = f i` and represents none of its hypotheses or conclusion. |

The promoted set is exactly 2/5. The two exact declarations are definitional
and have empty Lean dependency graphs. PM's ·1 cites ·01, while Lean closes
the identical equation directly by reduction; that historical relaxation is
recorded explicitly. The three refused records stay `prepared` with
`blocked-semantic-mismatch`, and no proposition ID occurs in both manifests.

The deterministic notation parser does not cover PM's `Prod`, diagonal
membership, higher-order class, and subscripted-scope notation. All five
records therefore carry `reviewed-gap` evidence pointing to this audit.
