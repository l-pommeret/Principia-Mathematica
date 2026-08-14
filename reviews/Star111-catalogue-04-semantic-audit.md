# ✱111 catalogue 04 — strict source/Lean semantic audit

Scope: the next five unprocessed loci in canonical order on PM II pp. 89–90,
checked against their `PM-VERBATIM` readings and the declarations in
`Star111Kernel.lean`. A theorem number or a shared word such as similarity is
not evidence of equivalence.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱111·15 | `star_111_15` | refused | PM gives a biconditional characterizing the restricted relation by a similarity between ranges plus membership of `T` in `κ sm λ`. Lean is the identity implication `Similar a b → Similar a b`; it contains neither restriction, ranges, `T`, nor the biconditional. |
| ✱111·16 | `star_111_16` | refused | PM derives two equalities from two printed similarity premises. Lean assumes `a = c` explicitly and returns that assumption, while never deriving the second equality `b = d`; the result is strictly weaker and circular relative to the printed conclusion. |
| ✱111·18 | `star_111_18` | refused | PM states a class-inclusion theorem involving `(α†β)₄ʻβ`. Lean merely extracts a globally bijective function from its own `Similar a b` encoding; it represents neither the target class nor inclusion. |
| ✱111·201 | `star_111_201` | refused | PM equates contextual existence of `Crp(S)ʻβ` with contextual existence of the similarity proposition. Lean only unfolds `Corresponds F b ↔ Similar (F b) b`, eliminating both existence operators rather than formalizing them. |
| ✱111·211 | `star_111_211` | refused | PM derives existence of `Sʻβ` and the domain condition `β∈αʻS` from existence of the correspondence. Lean merely projects `Similar (F b) b` from `Corresponds F b`; neither printed conclusion is present. |

The strict result is 0/5. Consequently this catalogue has only a homogeneous
refused manifest: no empty awaiting-CI manifest is created. All five candidates
remain prepared, contribute zero source-critical coverage, and are disjoint
from every earlier ✱111 catalogue.
