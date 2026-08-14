/-!
# PM I, ✱21·01

Exact reduction of application to a binary relation.  A relation is kept as
a genuinely two-place predicate with independent argument types.
-/

namespace PM.Architecture.Star21Q327Definition

abbrev BinaryRelation (Left : Sort u) (Right : Sort v) := Left → Right → Prop

/-- Application of `f` to the relation determined by `psi`, reduced to an
extensionally equal predicative binary representative. -/
def RelationFunctionApplication
    (psi : BinaryRelation Left Right)
    (f : BinaryRelation Left Right → Prop) : Prop :=
  ∃ phi : BinaryRelation Left Right,
    (∀ x y, phi x y ↔ psi x y) ∧ f phi

/-- ✱21·01. f{ẑxẑyψ(x,y)} .=: (∃φ) : φ!(x,y) .≡₍x,y₎. ψ(x,y) : f{φ!(ẑu,ẑv)} Df -/
def star_21_01
    (psi : BinaryRelation Left Right)
    (f : BinaryRelation Left Right → Prop) : Prop :=
  ∃ phi : BinaryRelation Left Right,
    (∀ x y, phi x y ↔ psi x y) ∧ f phi

end PM.Architecture.Star21Q327Definition
