# Audit Q263 — PM I, ✱9·6 and ✱9·61–✱9·63

Verdict: **COMPLETE — ✱9·6 and ✱9·61–✱9·63 integrated, awaiting CI**.

The source audit is complete for first edition vol. I, p. 142, scan leaf 164
(SHA-256 `78e2d89c9dabeeade09f4f22793dd4758e06a3397dbe6899faee3e1ff1b5facc`).
These four entries are not further first-order deduction theorems: ✱9·6 is a
same-type assertion, while ✱9·61–✱9·63 assert existence/significance of
elementary functions with one or two argument places and bound matrices.

The new minimal `SameAssignedType` certificate records only that expressions
inhabit one shared assigned carrier.  It adds no equality, semantic universe,
or axiom.  This licenses the exact ✱9·6 quartet for the existing `FirstOrder`
carrier in `Principia/Architecture/Star96SameType.lean`.

`Star961FunctionFormation.lean` adds the minimal intensional function slice:
an elementary function is its capture-safe `Apparent` matrix, with argument
places indexed in its type. ✱9·61 is pointwise disjunction; ✱9·62 closes the
printed `y` place universally and existentially while retaining `x`; ✱9·63
constructs all four independently bound combinations denoted by “etc.” No
semantic Lean function, truth predicate, axiom, or assertion rule is added.

Aristotle reconciliation reports `unknown question ID: Q263`; there is no
project or terminal archive to audit.
