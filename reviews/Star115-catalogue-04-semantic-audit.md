# ✱115 catalogue 04 — strict source/Lean semantic audit

This lot covers the next five loci, ·151, ·152, ·153, ·154, and ·16, on PM II
page 137 (scan leaf 177), checked against both canonical witnesses.

All five are refused. PM's ·151 is a relation/class equality, whereas Lean
proves only unique evaluation at one index. PM's ·152 and ·153 are similarities
of entire relation/product classes; Lean respectively constructs a pointwise
mapped function and proves uniqueness of evaluations of one given function.
PM's ·154 is membership of an entire product class in `ΠNcʻκ`; Lean only
deduces product-type inhabitation from a supplied element. PM's ·16 is an
inclusion into a cardinal class under disjointness; Lean only extracts
inhabitation of each factor from a supplied dependent function.

Thus catalogue 04 is homogeneous: 0/5 promoted, 5/5 `prepared` and
`blocked-semantic-mismatch`, with no empty awaiting-CI manifest. The one named
Lean edge is ·153 → Lean ·151; its normalized graph is recorded separately
from PM's printed ·153 → ·152 citation. All parser gaps point to this review.
