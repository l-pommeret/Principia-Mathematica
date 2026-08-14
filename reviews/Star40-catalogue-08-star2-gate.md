# ✱40 catalogue 08 — cumulative T1–T9 object gate

This cumulative gate covers PM1:✱40·45, ·451, ·5, ·51, and ·52. Their
catalogue readings match the literal source blocks.

All five declarations remain predicate/class semantics in the Lean host logic.
The monotonicity implications ·45 and ·451 are substantive `Prop` theorems,
and ·5, ·51, and ·52 are definitional equalities, but none is an inductive
object-language judgment. No item has a concrete non-`Prop` reading or an
axiom-free PM derivation. Accordingly all five are returned to `prepared` and
blocked as `blocked-missing-axiom-free-pm-object-proof`.

A targeted kernel `#print axioms` audit gives a second independent failure for
·45 and ·451: both depend on `propext`, `Classical.choice`, and `Quot.sound`.
Thus they also fail T5. The declarations for ·5, ·51, and ·52 report no axioms,
but still fail T3/T4 because axiom freedom does not turn host equality into a PM
object derivation.

No proof uses `Support`, an axiom, a printed `Df` as a constructor, or a
pass-through premise as a purported object derivation. This negative check
cannot replace T3/T4, which fail at the theorem statement itself.

## Graphs rebuilt from zero

Items ·45, ·451, ·5, and ·52 print no numbered dependency and call no numbered
Lean theorem. Item ·51 prints ✱32·12, ✱40·41, and ✱32·18, but its Lean body is
`rfl` and calls none of them. Its printed graph therefore contains those
three historical edges while both its Lean-call and normalized graphs are
empty.
