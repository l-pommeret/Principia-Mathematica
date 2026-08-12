import Principia.Architecture.Star20Q319Kernel

namespace PM.Architecture.Star20Q326Kernel

open PM.Architecture.Star20Q319Kernel

/-- The class extension of the pointwise law of excluded middle. -/
def ExcludedMiddleExtension (φ : α → Prop) : ClassExtension α :=
  fun x => φ x ∨ ¬ φ x

/-- The comparison extension printed at ✱20·8. -/
def IdentityDecisionExtension (a : α) : ClassExtension α :=
  fun x => x = a ∨ x ≠ a

/-- PM I ✱20·71: Leibniz identity for typed classes. -/
theorem star_20_71 (a b : ClassExtension α) :
    a = b ↔ ∀ g : ClassExtension α → Prop, g a → g b := by
  exact star_20_19 a b

/-- PM I ✱20·8. The displayed premise is retained even though PM's classical
logic proves excluded middle uniformly at every object of the same type. -/
theorem star_20_8 (φ : α → Prop) (a : α) :
    (φ a ∨ ¬ φ a) → ExcludedMiddleExtension φ = IdentityDecisionExtension a := by
  intro _
  funext x
  apply propext
  exact ⟨fun _ => Classical.em (x = a), fun _ => Classical.em (φ x)⟩

/-- PM I ✱20·81: any two pointwise excluded-middle extensions of the same
simple type are identical. -/
theorem star_20_81 (φ ψ : α → Prop) (a : α) :
    (φ a ∨ ¬ φ a) → (ψ a ∨ ¬ ψ a) →
      ExcludedMiddleExtension φ = ExcludedMiddleExtension ψ := by
  intro hφ hψ
  exact (star_20_8 φ a hφ).trans (star_20_8 ψ a hψ).symm

end PM.Architecture.Star20Q326Kernel
