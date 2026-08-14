# ✱116 catalogue 16 strict semantic audit

The five loci ·531–·535 were checked source-to-Lean on printed pages 159–160
(scan leaves 199–200). Only ·534 passes strict equivalence. It states the
pointwise-product similarity, and Lean realizes exactly that typed content by
the explicit bijection between a pair of γ-indexed functions and a γ-indexed
function into the product. The construction hypotheses are discharged by that
canonical definition rather than assumed. It is marked `awaiting-ci` only.

The remaining four loci are refused. Entries ·531, ·533, and ·535 preserve
only prose summaries, not their complete displayed PM formulae, so their Lean
counterparts cannot be certified as strictly source-equivalent. Item ·532 is
also a direct mismatch: PM asserts one-one-ness and the converse domain of the
constructed relation, whereas Lean proves a left-inverse equation for the
aggregate function-space equivalence. These items remain `prepared` with
`blocked-semantic-mismatch` and explicit reasons.

The dependency graphs remain distinct. PM ·534 cites the hypotheses of ·532;
Lean ·534 reuses the complete typed similarity at ·53. The normalized closure
therefore records both source and implementation predecessors. Historical
notation remains `reviewed-gap` under the deterministic parser.

For dependency auditing, the strict typed term has only the implementation
edge to ·53. The printed ·532 construction is internalized by the explicit
equivalence, so it is recorded as printed-but-unused rather than as a false
Lean edge.
