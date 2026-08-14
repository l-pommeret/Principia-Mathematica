# ✱118 catalogues 03–04 — strict source/Lean semantic audit

Scope: the next ten canonical loci of PM II ✱118: ·25, ·3, ·301, ·31,
·32, ·33, ·34, ·341, ·35, and ·351 (printed pages 197–198,
scan leaves 237–238).  Every reading was checked against its unique
`PM-VERBATIM` source block.  Promotion requires preservation of normalizations,
side conditions, and mathematical direction; a pass-through hypothesis is not
an exact proof.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱118·25 | `star_118_25` | refused | Lean applies ordinary associativity beneath an outer `n`.  PM's chain separately inserts normalization of the left and right intermediate cardinal sums, which the Lean conclusion lacks. |
| ✱118·3 | `star_118_3` | refused | Reflexivity of arbitrary `n (mul a b)` erases the class abstraction defining cardinal multiplication and all existential representative conditions. |
| ✱118·301 | `star_118_301` | refused | `Normal n (op a b)` unfolds to the equality concluded; the existence-to-`smξ` content is assumed. |
| ✱118·31 | `star_118_31` | refused | Lean returns product normality unchanged; PM concludes existence of `smξʻʻμ` and requires `ν≠0`. |
| ✱118·32 | `star_118_32` | refused | The complete equivalence is the premise `h`; PM's `NC−ιʻ0` antecedent is absent. |
| ✱118·33 | `star_118_33` | refused | The complete equality is the premise `h`; PM's `NC−ιʻ0` antecedent is absent. |
| ✱118·34 | `star_118_34` | refused | The equality is supplied as `h`, with neither `ν∈NC` nor `μ≠0` represented. |
| ✱118·341 | `star_118_341` | refused | The equality is supplied as `h`, with neither `μ∈NC` nor `ν≠0` represented. |
| ✱118·35 | `star_118_35` | refused | Lean reassociates the raw product to `n (op a (op b c))`; PM instead normalizes the left intermediate product inside the right-hand product and assumes `ϖ≠0`. |
| ✱118·351 | `star_118_351` | refused | Lean reassociates raw products but does not normalize the right intermediate product as printed; `μ≠0` is also absent. |

The promoted set is **0/10**.  All records remain uniquely in their canonical
catalogues with `formal_status: prepared` and explicit semantic refusal
statuses.  None is eligible for `awaiting-ci` or source-critical coverage.

The eight pass-through/reflexive bodies have empty Lean theorem-dependency
graphs.  The two associativity bodies use only their local `assoc` premise,
not an indexed PM theorem.  Hence all recorded Lean and normalized dependency
lists correctly remain empty; no historical dependency relaxation is claimed.
