# ✱118 catalogue 01 — strict source/Lean semantic audit

Scope: the first five loci of PM II ✱118 (·01, ·11, ·12, ·13, and
·2), on printed pages 195–196 (scan leaves 235–236).  Their transcriptions
were checked against the canonical `PM-VERBATIM` source block and Project
Gutenberg 78255.  Promotion is strict: a theorem that assumes its conclusion,
or replaces a defining class by reflexivity of an arbitrary operation, is not
an exact reconstruction.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱118·01 | `star_118_01` | refused | PM relates an arbitrary predicate at the uniquely described `μ` and at `σ`; Lean concludes only `f s ↔ f s`, without a description operator or a term corresponding to `μ`.  The unique-value hypothesis is unused. |
| ✱118·11 | `star_118_11` | refused | `Below` is merely an arbitrary relation, and the `down` argument universally assumes the exact downward-normality implication returned by the theorem.  No class inclusion or cardinal-subtraction existence argument is proved. |
| ✱118·12 | `star_118_12` | refused | The same `down` premise assumes the conclusion.  Moreover the printed comparison of cardinal numbers is replaced by unconstrained `Below`, so the source antecedent is not represented. |
| ✱118·13 | `star_118_13` | refused | Arbitrary `Below`/`Normal` parameters replace `μ≤ν` and existence of `smξ`; again `down` is precisely the mathematical content to be established. |
| ✱118·2 | `star_118_2` | refused | PM defines cardinal addition at type `ξ` by a class abstraction over representatives `α,β,η`.  Lean proves only `n (add a b) = n (add a b)` for arbitrary functions, erasing the defining predicate and its existential witnesses. |

Thus the strict promoted set is **0/5**.  All five canonical records remain
`formal_status: prepared` with a refusal status in `catalogue-01`; none is
duplicated into a sidecar, eligible for `awaiting-ci`, or countable toward
source-critical coverage.

The Lean declarations are locally closed and have no theorem-declaration
dependencies, but an empty Lean dependency graph cannot repair these semantic
losses.  No historical-dependency relaxation is claimed.  The notation remains
a deterministic-parser gap, now backed by this item-level review.
