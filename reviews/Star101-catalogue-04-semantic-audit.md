# ✱101 catalogue 04 strict semantic audit

Scope: exactly PM2:✱101·3, ·301, and ·31 from Q407, collated against the
literal source blocks for first-edition p. 22 / scan leaf 62 and compared with
`Star101Kernel.lean`.

All three candidate declarations are refused.

- **✱101·3.**  PM concludes the equality of cardinal objects
  `2 = Ncʻ(ιʻx ∪ ιʻy)`.  Lean proves only `Card2 (pair x y)` after assuming
  `x ≠ y`; it contains neither a cardinal object nor `Nc`.  Without an audited
  interpretation identifying that predicate with the printed cardinal-number
  equality, it is a consequence-level surrogate.
- **✱101·301.**  PM identifies `2` with a class abstract characterized by
  singleton deletion.  Lean's `Card2 a ↔ Card2 a` is reflexive and omits the
  abstraction, existential member, deletion, and membership in `1`.
- **✱101·31.**  PM again states an `Nc` equality for a particular union of
  iterated unit classes.  Lean constructs a pair in the disjoint sum
  `Sum α Unit`.  This witnesses a modern two-element set but neither encodes
  the printed iterated unit classes nor states the cardinal-number equality.

No Q407 item is promoted to `awaiting-ci`.  The canonical catalogue itself
records all refusals, preserving one record per PM ID and empty accepted Lean
dependency graphs.
