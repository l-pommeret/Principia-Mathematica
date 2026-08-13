# ✱50 source catalogue review

The fifty-three items are checked against Project Gutenberg 78050 on printed
pages 350–355 (scan leaves 372–377).  Definitions ·01 and ·02 map to the real
Lean constants `I` and `J`; all other IDs resolve uniquely to numbered
declarations. The first batch (·01, ·02, ·1, ·11, ·12) has now passed strict
item-level semantic audit and is `awaiting-ci`; later batches remain
`prepared` pending semantic promotion.

For the audited batch, `Relation α := α → α → Prop` preserves both relation
arguments. `I` is exactly equality, `J` is exactly its pointwise complement,
and ·1, ·11, ·12 are respectively the two pointwise expansions and the
extensional diversity-relation identity. All five proofs are definitional
(`rfl`/`Iff.rfl`), so no mathematical premise is assumed. Their dependency
metadata records the definitions actually unfolded; printed abstraction,
complement, and extensionality citations that elaborate definitionally are
retained explicitly as reviewed indirect/unused steps rather than erased.

The second batch (·13–·17) has also passed strict audit and is `awaiting-ci`.
The assigned type is explicitly inhabited for ·13, matching PM's existential
use of identity. The theorem ·14 represents the descriptive value equation by
an explicit witness `y` plus existence and uniqueness; ·15 universally gives
the same unique fibre. The image definition has PM's argument orientation, so
·16 is exactly `Iʻʻα = α`. Finally ·17 assumes, for every member of `α`, both
the self-pair and uniqueness expressed by `Rʻx = x`, and proves exactly the
image equality. No implication is weakened and no premise is hidden.

Forty-one formulas use relation abstraction/complement, converse, restriction
(`◁/▷`), product (`∥`), or dotted relation operators beyond the current parser
grammar.  Those items carry `reviewed-gap`; no diplomatic reading is weakened
to make the parser accept it.
