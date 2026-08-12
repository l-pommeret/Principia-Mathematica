import Principia.Architecture.Star22Q341Definitions

/-! Exact class-closure and abstraction kernels for PM I, Q347. -/

namespace PM.Architecture.Star22Q347Kernel

open Star22Q341Definitions

/-- In the documented unramified embedding, classhood means having an
extensionally equal predicate representative. -/
def IsClass (α : Class Object) : Prop :=
  ∃ φ : Object → Prop, ∀ x, α x ↔ φ x

/-- PM I ✱22·37. -/
theorem star_22_37 (α β : Class Object) : IsClass (Union α β) := by
  exact ⟨Union α β, fun _ => Iff.rfl⟩

/-- PM I ✱22·38. -/
theorem star_22_38 (α : Class Object) : IsClass (Complement α) := by
  exact ⟨Complement α, fun _ => Iff.rfl⟩

/-- PM I ✱22·39. -/
theorem star_22_39 (φ ψ : Object → Prop) :
    Intersection φ ψ = (fun z => φ z ∧ ψ z) := rfl

/-- PM I ✱22·391. -/
theorem star_22_391 (φ ψ : Object → Prop) :
    Union φ ψ = (fun z => φ z ∨ ψ z) := rfl

/-- PM I ✱22·392. -/
theorem star_22_392 (φ : Object → Prop) :
    Complement φ = (fun z => ¬ φ z) := rfl

end PM.Architecture.Star22Q347Kernel
