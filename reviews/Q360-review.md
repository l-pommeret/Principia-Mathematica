# Q360 review — ✱24·01–101

PM I p. 231 / leaf 253 is canonical; PG78050 agrees. All three definitions
are represented literally over the typed class operations: `V x` is `x=x`,
`Λ` is its complement, and class existence is inhabited membership.

The two propositions have complete bodies. ✱24·1 uses the explicit
`Nonempty Object` condition expressing PM's nonempty range of possible
arguments and refutes equality at one such argument. ✱24·101 is constructive:
the complement of `¬(x=x)` is extensionally `x=x`. No `Set`, class-valued
incomplete symbol, or additional class axiom is introduced.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star24Q360Kernel.lean`
