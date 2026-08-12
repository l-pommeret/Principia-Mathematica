/-! # PM I, ✱22·55–✱22·58: exact polymorphic class propositions. -/

namespace PM.Architecture.Star22Q351Kernel

abbrev Class (Object : Sort u) := Object → Prop
def Included (alpha beta : Class Object) : Prop := ∀ x, alpha x → beta x
def Union (alpha beta : Class Object) : Class Object := fun x => alpha x ∨ beta x

theorem class_ext {alpha beta : Class Object}
    (h : ∀ x, alpha x ↔ beta x) : alpha = beta := by
  funext x
  exact propext (h x)

/-- ✱22·55. Equality substitutes in the right-hand class of inclusion. -/
theorem star_22_55 (alpha beta gamma : Class Object) :
    alpha = beta → (Included gamma alpha ↔ Included gamma beta) := by
  rintro rfl
  exact Iff.rfl

/-- ✱22·551. Equality substitutes in the left argument of union. -/
theorem star_22_551 (alpha beta gamma : Class Object) :
    alpha = beta → Union alpha gamma = Union beta gamma := by
  rintro rfl
  rfl

/-- ✱22·56. Class union is idempotent. -/
theorem star_22_56 (alpha : Class Object) : Union alpha alpha = alpha := by
  apply class_ext
  intro x
  constructor
  · exact fun h => h.elim id id
  · exact fun h => Or.inl h

/-- ✱22·57. Class union is commutative. -/
theorem star_22_57 (alpha beta : Class Object) :
    Union alpha beta = Union beta alpha := by
  apply class_ext
  intro x
  exact or_comm

/-- ✱22·58. Both operands are included in their union. -/
theorem star_22_58 (alpha beta : Class Object) :
    Included alpha (Union alpha beta) ∧ Included beta (Union alpha beta) := by
  exact ⟨fun _ => Or.inl, fun _ => Or.inr⟩

end PM.Architecture.Star22Q351Kernel
