# Q344 exact inclusion audit

Q344 contains ✱22·44 and ✱22·441 from PM I p. 221, scan leaf 243; the first
edition scan is collated with PG78050. The earlier review text referred to a
different p. 219 five-item batch and has therefore been corrected rather than
retained as false evidence.

`Star22Q344Kernel.lean` uses the explicit simple-type interpretation of a
class extension as `α → Prop`. Inclusion is exactly the pointwise implication
printed at ✱22·01. ✱22·44 is its fully polymorphic transitivity theorem, and
✱22·441 specializes inclusion at the displayed member `x`.

Both are complete proofs of the canonical endpoints, not target records.
There is no inhabitance assumption, decidability, classical reasoning, new
axiom, placeholder, or unsafe declaration. The batch awaits CI after targeted
Lean 4.30.0 compilation.
