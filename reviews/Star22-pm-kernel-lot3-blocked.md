# ✱22 syntax-first audit, lot 3: blocked

Targets: ✱22·37, ·38, ·39, ·391, and ·392.

The exact, non-vacuous AST endpoints now live in `Principia.Syntax.Class`:
classhood of union/complement and the three displayed abstraction equalities.
No derivability rule was added.

The printed proof graph blocks certification. ✱22·37 and ·38 call ✱20·41.
✱22·39 calls ✱22·33, ✱20·3, and ✱20·33. PM marks ✱22·391 and
·392 as similar proofs, so they inherit the preceding abstraction-proof
shape with the corresponding union/complement definitions; they are not `rfl`
proofs merely because the secondary Lean model reduces extensionally.

None of the required ✱20 nodes is currently a typed derivation over this PM
class syntax, and ✱22·33 was already blocked in lot 2. Accordingly all five
items are `prepared`, with their former axiom-free Lean-`Prop` declarations
retained only as `secondary_prop_declaration`. T1–T9 certification is not
claimed.
