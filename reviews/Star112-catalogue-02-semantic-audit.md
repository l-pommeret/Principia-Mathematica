# ✱112 catalogue 02 — strict source/Lean semantic audit

Scope: the five loci of the homogeneous batch
`PM2-STAR112-CATALOGUE-02-REFUSED`, compared with the literal PM II source
blocks on printed page 99 and the corresponding declarations in
`Star112OpeningKernel.lean`. A strict promotion must preserve the printed
class/cardinal construction, hypotheses, and conclusion.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱112·103 | `star_112_103` | refused | PM gives an equality of the entire sum class with a relational image. Lean proves only that the tagged sum class is nonempty iff some member class is nonempty. Equality has been weakened to existence. |
| ✱112·11 | `star_112_11` | refused | PM characterizes membership in the cardinal number of the tagged sum class by cardinal similarity. Lean replaces the tagged sum by an untagged union and defines `EqCard` as equivalence of nonemptiness, not existence of a bijection. |
| ✱112·12 | `star_112_12` | refused | PM places the tagged sum class in its cardinal number. Lean instead uses the untagged union, with cardinal equality again weakened to equivalence of nonemptiness. |
| ✱112·13 | `star_112_13` | refused | PM has a specific antecedent about similarity of `λ` with restricted membership and concludes membership of `sʻλ` in `ΣNcʻκ`. Lean is the generic tautology `EqCard A B → EqCard A B`; none of the printed constructions survives. |
| ✱112·14 | `star_112_14` | refused | PM uses the exclusive second-order class condition on `κ` to prove similarity of restricted membership with `κ`. Lean is again `EqCard A B → EqCard A B`, omitting both the antecedent and the stated objects. |

The strict promoted set is therefore 0/5. All five records remain `prepared`
in their single canonical refused manifest, and no awaiting-CI lot is created.

No bracketed numbered citations occur in these five literal source statements,
so their printed and normalized proposition-dependency graphs remain empty.
The Lean declarations likewise cite no numbered proposition. Empty graphs do
not repair the semantic losses above and are not evidence for promotion.
