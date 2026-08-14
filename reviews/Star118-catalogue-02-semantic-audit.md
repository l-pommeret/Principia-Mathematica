# ✱118 catalogue 02 — strict source/Lean semantic audit

Scope: the next five canonical loci of PM II ✱118 (·201, ·21, ·22,
·23, and ·24), on printed pages 196–198 (scan leaves 236–238).  The
printed readings were checked against their unique `PM-VERBATIM` blocks.  An
abstract operation is acceptable only when its laws prove the source claim;
passing the desired proposition itself as a hypothesis is not a proof.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱118·201 | `star_118_201` | refused | `Normal n (op a b)` unfolds to the equality returned by the theorem.  Thus the consequence corresponding to PM's `smξ` value is assumed, not obtained from existence of cardinal addition. |
| ✱118·21 | `star_118_21` | refused | Lean proves only `Normal n (op a b) → Normal n (op a b)`.  PM instead derives existence of the `smξ` images of both operands from existence of the typed sum. |
| ✱118·22 | `star_118_22` | refused | The entire normality equivalence is the premise `h`; the printed conditions `μ,ν∈NC` and the relevant existence predicates are not reconstructed. |
| ✱118·23 | `star_118_23` | refused | The theorem returns exactly the equality supplied as `h` and omits PM's two NC-membership antecedents. |
| ✱118·24 | `star_118_24` | refused | The theorem returns exactly the equality supplied as `h` and omits the printed antecedent `ν∈NC`. |

The strict promoted set is therefore **0/5**.  These five records remain only
in their canonical catalogue, with `formal_status: prepared` and explicit
semantic refusal statuses.  None is eligible for `awaiting-ci` or
source-critical coverage.

All five theorem bodies have empty Lean theorem-dependency graphs.  That is
consistent with their pass-through form and provides no historical dependency
claim.  No dependency relaxation is asserted; parser gaps are backed by this
item-level review.
