# ✱54 closing catalogue 05 — strict semantic audit

Scope: the five consecutive candidates ✱54·443, ·45, ·451, ·452, and ·46
on PM I page 380 (1910 scan leaf 402), checked against the scan, Gutenberg
78050, and the full Lean theorem types.

The strict split is 4/5 exact and 1/5 refused:

- ✱54·443 is refused. PM quantifies a predicate `φ`, assumes
  `φ(x,y) ≠ φ(y,x)`, and concludes the oriented equality
  `φ(z,w) = φ(x,y)`. The Lean namesake has no `φ` argument and proves only
  that distinct members `z,w` of the pair occur as `(x,y)` or `(y,x)`.
- ✱54·45 is exact: exhaustive elimination of pair membership gives precisely
  the four displayed instances of the universally quantified binary formula.
- ✱54·451 is exact: under both diagonal facts and the printed cross-instance
  equivalence, the universal condition is equivalent to the disjunction of
  the two cross instances.
- ✱54·452 is exact under the same hypotheses, reducing the universal condition
  to the selected cross instance.
- ✱54·46 is exact: any two distinct members of `ιʻx ∪ ιʻy` force
  `x ≠ y`.

The refused singleton manifest and the four-item exact manifest are disjoint.
The Lean dependency chain ·452 → ·451 → ·45 matches the printed chain.
All notation-parser gaps point to this item-level audit.
