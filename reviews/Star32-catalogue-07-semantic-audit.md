# ✱32 catalogue 07 strict semantic audit

The five literal source blocks PM1:✱32·31, ·32, ·33, ·34, and ·35 match their catalogue records and were compared individually with the named declarations in `Principia/Architecture/Star32ConsecutiveKernel4.lean`.

Propositions ·32, ·34, and ·35 pass strict typed equivalence: sections distribute pointwise over relation union and complement exactly as printed. Their accepted proof terms are definitional and contain no direct numbered-proposition references. These three records are promoted in place to `awaiting-ci`.

Propositions ·31 and ·33 are refused. In both canonical source blocks, the right-hand side repeats the left section of `R`: respectively `←Rʻx ∩ ←Rʻx` and `←Rʻx ∪ ←Rʻx`. The Lean declarations instead state the mathematically symmetric formulas with `leftSection S x` as the second operand. Those declarations may repair an apparent printed error, but they are not equivalent to the preserved canonical text for arbitrary `R` and `S`. The refused records are split into the homogeneous prepared manifest `PM1-star-32-catalogue-7-refused.json`; CI evidence remains pending for the exact lot.
