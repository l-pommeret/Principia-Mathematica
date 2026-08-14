# ✱111 catalogues 05–06 — strict source/Lean semantic audit

Scope: the next ten unprocessed canonical loci, split into two consecutive
five-item lots. Each declaration is compared with the complete `PM-VERBATIM`
statement; shared vocabulary and numbering do not establish equivalence.

| locus | Lean declaration | verdict | exact mismatch |
|---|---|---|---|
| ·25 | `star_111_25` | refused | PM concludes that a double image under `Crp(S)` is an exclusive class; Lean only forwards a pointwise `Corresponds` hypothesis to `Similar`. |
| ·31 | `star_111_31` | refused | PM's typed hypotheses yield a similarity involving `DʻR` and `sʻκ`; Lean merely extracts a global bijection from an assumed similarity. |
| ·32 | `star_111_32` | refused | PM concludes `M sm sʻλ` from correspondence/domain data; Lean instead proves generic symmetry of `Similar a b`. |
| ·321 | `star_111_321` | refused | PM derives contextual existence of `κ sm sm λ`; Lean proves only reflexivity `Similar a a`. |
| ·33 | `star_111_33` | refused | PM derives double similarity from multiplicative choice and class hypotheses; Lean assumes double similarity and returns it. |
| ·34 | `star_111_34` | refused | PM, under `Mult ax`, proves symmetry of double similarity; Lean only extracts the bijective map from an already assumed `DoubleSimilar`. |
| ·4 | `star_111_4` | refused | PM gives a three-way equivalence with existence of a witness relation and contextual existence; Lean is the self-equivalence of `DoubleSimilar`. |
| ·401 | `star_111_401` | refused | PM identifies double similarity with a definite-description witness satisfying all defining clauses; Lean only extracts some bijective map. |
| ·402 | `star_111_402` | refused | PM's definite witness is restricted to `sʻλ` and satisfies one-one, range, and image clauses; Lean extracts only membership transport from an assumed double similarity. |
| ·43 | `star_111_43` | refused | PM produces a one-one relation `S` with prescribed domain and converse domain; Lean only extracts the function already stored in `DoubleSimilar`. |

Both results are 0/5. Each lot therefore has one homogeneous refused manifest
and no empty awaiting-CI counterpart. All ten IDs are new to metadata and count
zero toward source-critical coverage.

All ten printed forms fail the current parser independently (class-expression,
`Cls² excl`, `Mult ax`, `sm sm`, restriction, or contextual-description
syntax), so each receives an explicit `reviewed-gap` backed by the existing
✱111 parser review.
