# ✱41 complete source catalogue and first-lot audit

All 45 numbered items of ✱41 are transcribed in printed order from Project Gutenberg 78050 and checked against the 1910 Volume I facsimile, printed pages 331–335. The catalogue uses nine batches of five items and maps every item to its existing homonymous kernel declaration (the defining constants `product` and `sum` for ·01 and ·02).

The first batch (·01, ·02, ·1, ·11, ·12) passes strict semantic audit. The curried Lean `Relation` representation preserves the two PM relation arguments; `product` is pointwise universal quantification over members, `sum` is pointwise existential membership, ·1 and ·11 are their exact membership expansions, and ·12 is exactly inclusion of the product in every member. The five items are promoted in-place to `awaiting-ci`; no sidecar or duplicate record is used. They must not become `kernel-checked` until a successful CI run covers the commit containing this source and its metadata.

The remaining forty items stay `prepared` and `semantic-audit-pending`. The parser route is `reviewed-gap` because the current deterministic PM parser does not cover dotted relational product/sum notation and the associated relation-class operators.
