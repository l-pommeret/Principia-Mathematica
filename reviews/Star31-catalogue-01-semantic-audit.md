# ✱31 catalogue 01 v1 kernel audit

Scope is exactly ·01, ·02, ·1, ·101, and ·13. The acceptance standard is the
✱2 architecture: an exact object-language AST, an assertion or definition
judgement over that AST, and a kernel derivation accounting for the printed
proof. A related Lean `Prop` theorem is secondary evidence only.

No item passes. There is no relation/class-abstract syntax representing ·01
or ·02, hence no definitional judgement. Items ·1 and ·101 likewise lack their
exact quantified ASTs and asserted derivations. For ·13, `star_31_13` proves
only `∃ Q, IsConverse Q P`; it represents neither the descriptive value
`CnvʻP`, its `E!` formula, nor the printed derivation.

The dependency graphs were rebuilt from zero. Printed edges are: none for ·01
and ·02; ·1 → {✱21·3, ✱31·01}; none printed for ·101; and ·13 → {✱14·21,
✱31·12}. Since every candidate fails before the judgement gate, accepted Lean
and normalized graphs are empty. No edge is inferred from name proximity or
from the secondary Prop model.

All five remain `prepared`, explicitly blocked as v1-incomplete, with pending
CI evidence. There is no partial promotion.
