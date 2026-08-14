# ✱101 catalogue 01 strict semantic audit

Scope: exactly PM2:✱101·1, ·11, and ·12 from `PM2-star-101-Q404.json`.
The literal source blocks in `Star100Source.lean` agree with that catalogue and
with first-edition p. 19 / scan leaf 59.  This audit compares those statements
with the similarly numbered declarations in `Star101Kernel.lean`; similarity
of theorem names or provability of a modern surrogate is not treated as
source equivalence.

All three proposed correspondences are refused.

- **✱101·1.**  The source equates the cardinal object `0` with the result of
  applying the cardinal-number operation `Nc` to the null class `Λ`.  Lean's
  `star_101_1 : Card0 empty` unfolds to `empty = empty`.  It contains neither
  a cardinal object nor an `Nc` operation and collapses the substantive
  equality to reflexivity.  It is therefore only a modern consequence of the
  chosen definition, not the printed proposition.
- **✱101·11.**  The source asserts membership of the cardinal object `0` in
  the class `NC` of cardinal numbers.  Lean's `star_101_11` asserts
  `∃ a : Set α, Card0 a`: existence of an underlying class satisfying
  `a = empty`.  No object representing `0`, class representing `NC`, or
  membership relation between them occurs, so the target changes both the
  objects and the predicate.
- **✱101·12.**  The source asserts contextual existence of the cardinal
  object `0`.  Lean's `star_101_12` instead gives unique existence of an
  underlying predicate `a : Set α` satisfying `a = empty`.  This neither
  represents PM's incomplete-symbol existence assertion nor distinguishes a
  cardinal object from its representatives.

The local aliases `Set`, `empty`, `Card0`, and `Unique` in
`Star101Kernel.lean` have no interpretation map to the already audited PM
cardinal-zero infrastructure or to a Volume-II `Nc`/`NC` layer.  Consequently
no strengthening of metadata wording can repair these signature mismatches.
The original three source records remain `prepared`; none is promoted to
`awaiting-ci`.  The refusal sidecar records empty Lean dependency graphs
because no declaration is accepted as a formalization of these items.
