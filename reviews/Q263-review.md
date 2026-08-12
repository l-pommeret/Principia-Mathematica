# Audit Q263 — PM I, ✱9·6 and ✱9·61–✱9·63

Verdict: **PARTIAL — ✱9·6 integrated; ✱9·61–✱9·63 remain blocked**.

The source audit is complete for first edition vol. I, p. 142, scan leaf 164
(SHA-256 `78e2d89c9dabeeade09f4f22793dd4758e06a3397dbe6899faee3e1ff1b5facc`).
These four entries are not further first-order deduction theorems: ✱9·6 is a
same-type assertion, while ✱9·61–✱9·63 assert existence/significance of
elementary functions with one or two argument places and bound matrices.

The new minimal `SameAssignedType` certificate records only that expressions
inhabit one shared assigned carrier.  It adds no equality, semantic universe,
or axiom.  This licenses the exact ✱9·6 quartet for the existing `FirstOrder`
carrier in `Principia/Architecture/Star96SameType.lean`.

The current canonical `Elementary`/`Apparent`/`FirstOrder` syntax represents
propositions and fixed binder reductions, but has no object-language API for
function existence, significance, or the required
higher-arity function types.  Encoding ✱9·61–✱9·63 as equality of current
syntax objects, semantic Lean functions, or `OrderedAssertion` would change
their kind and scope.  No declaration for ✱9·61–✱9·63 is therefore
integrated, and their prepared/architecture-blocked metadata remains accurate.

Aristotle reconciliation reports `unknown question ID: Q263`; there is no
project or terminal archive to audit.
