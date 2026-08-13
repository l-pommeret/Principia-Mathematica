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

Forty-one formulas use relation abstraction/complement, converse, restriction
(`◁/▷`), product (`∥`), or dotted relation operators beyond the current parser
grammar.  Those items carry `reviewed-gap`; no diplomatic reading is weakened
to make the parser accept it.
