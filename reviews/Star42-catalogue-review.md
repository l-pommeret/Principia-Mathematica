# ✱42 source catalogue and strict semantic review

The nine propositions are checked against Project Gutenberg 78050 and the
first-edition scan on printed pages 336–339 (leaves 358–361). Seven formulas
use dotted product/sum operators or direct/converse image arrows not yet
accepted by the Unicode PM grammar. They remain `reviewed-gap`; their
diplomatic notation is preserved and parser coverage is not confused with
semantic equivalence.

## Catalogue 1 (five-item strict-audit front)

The literal source blocks and catalogue records agree for PM1:✱42·1, ·11,
·12, ·13, and ·2. The prose on pp. 336–337 explicitly identifies ·1 and
·11 as the associative laws for class sum and product. Under the file's
typed definitions, the first four Lean declarations preserve the printed
operations extensionally:

- ·1 flattens a class of classes of classes either after mapping class sum or
  by summing the flattened carrier;
- ·11 is the universal-membership/product analogue;
- ·12 and ·13 repeat those two laws pointwise for binary relations.

Those four translations pass strict equivalence and are promoted to
`awaiting-ci`. Their proofs unfold only the local operator definitions; the
printed dependency graph, Lean numbered-proposition dependency graph, and
normalized dependency graph therefore all have no edges.

PM1:✱42·2 is refused. The source displays four genuinely different
field/image constructions,
`CʻṡʻCʻP`, `sʻCʻʻCʻP`, `FʻʻCʻP`, and `F⃗²ʻP`. Lean instead
defines `fieldOfRelationSumCarrier`, `sumOfFieldsOfCarrier`,
`fieldImageOfCarrier`, and `iteratedField₂` as four aliases of the same
invented `fieldTerms` term and proves the chain by `rfl`. No semantic bridge
from any alias to its corresponding PM operator is supplied. Kernel checking
therefore establishes only a definitional tautology, not the printed claim.
Its three dependency graphs also have no numbered-proposition edges, but that
does not repair the semantic mismatch; the item remains `prepared` and
blocked.

Catalogue 2 (·21, ·22, ·3, ·31) remains `prepared`, pending its own
item-level strict audit.
