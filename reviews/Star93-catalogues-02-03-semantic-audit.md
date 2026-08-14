# ✱93 catalogues 02–03 — strict source/Lean semantic audit

Scope: the ten next canonical loci ✱93·101, ·102, ·103, ·104, ·11,
·111, ·112, ·113, ·114, and ·115, on printed pages 609–610
(scan leaves 631–632).  All readings agree with their unique
`PM-VERBATIM` blocks.  The relation uses both arguments, `dom`/`cod` preserve
PM's domain/converse-domain convention, and `image` follows the established
output-first orientation.

| PM locus | verdict | semantic finding |
|---|---|---|
| ✱93·101 | exact, awaiting CI | `boundary P` is extensionally exactly `dom P − cod P`. |
| ✱93·102 | refused | PM prints an unconditional three-way equivalence involving the definite description, singletonhood, and membership. Lean instead assumes `Singleton (boundary P)` and proves only membership iff uniqueness among members; the extra hypothesis and missing equivalence cannot be erased. |
| ✱93·103 | exact, awaiting CI | `field P − cod P` is extensionally the same boundary class; the reverse direction correctly eliminates the impossible codomain-only case. |
| ✱93·104 | refused | PM's `R_*` and `R_po` are weak and proper ancestrals. Lean defines them locally as `Id ∪ R` and `R`, omitting paths of length at least two, so the statement agrees only for a restricted relation class not present in PM. |
| ✱93·11 | exact, awaiting CI | The pointwise minimum expansion preserves all three conjuncts and the converse-image negation. |
| ✱93·111 | exact, awaiting CI | This is the extensional class form of the exact ·11 expansion. |
| ✱93·112 | exact, awaiting CI | Lean proves both printed equalities: boundary equals the minimum of the domain and of the field. |
| ✱93·113 | exact, awaiting CI | The conclusion is exactly inclusion in `A ∩ field P`. |
| ✱93·114 | exact, awaiting CI | `maximum P` is definitionally `minimum (converse P)`. |
| ✱93·115 | exact, awaiting CI | The maximum expansion has the same class and field conjuncts and correctly changes the excluded image from converse `P` to direct `P`. |

The strict split is **8 exact / 2 refused**. Catalogue 02 is physically split
into a three-item awaiting-CI manifest and a two-item refused manifest;
catalogue 03 is a homogeneous five-item awaiting-CI manifest. Every ID occurs
in exactly one metadata file. Exact items are marked `awaiting-ci`, never
`kernel-checked`, and all CI evidence remains explicitly pending.

All ten declarations use only local definitions, local proof structure, or
their explicit non-numbered hypothesis; none calls a numbered Lean theorem.
Their Lean and normalized dependency graphs therefore remain empty.  The
source entries print no dependency brackets, so no dependency relaxation is
claimed.
