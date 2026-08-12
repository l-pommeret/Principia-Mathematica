import Principia.Architecture.Star12Q289Reducibility

/-! Exact extensional class kernels for PM I, Q318 (✱20·12--✱20·151). -/

namespace PM.Architecture.Star20Q318Kernel

/-- Equality of the extensions `ẑ(ψz)` and `ẑ(χz)`. -/
def ClassEq (ψ χ : α → Prop) : Prop := ∀ x, ψ x ↔ χ x

/-- A class context respects equality of extensions. -/
def Extensional (f : (α → Prop) → Prop) : Prop :=
  ∀ {ψ χ}, ClassEq ψ χ → (f ψ ↔ f χ)

/-- PM I ✱20·12. -/
theorem star_20_12 {α : Sort _} (ψ : α → Prop)
    (f : (α → Prop) → Prop) (hf : Extensional f) :
    ∃ φ : Star12Q289Reducibility.Predicative₁ α,
      (∀ x, φ x ↔ ψ x) ∧ (f ψ ↔ f φ) := by
  obtain ⟨φ, hφ⟩ := Star12Q289Reducibility.star_12_1 ψ
  exact ⟨φ, fun x => (hφ x).symm, hf hφ⟩

/-- PM I ✱20·13. -/
theorem star_20_13 (ψ χ : α → Prop) :
    (∀ x, ψ x ↔ χ x) → ClassEq ψ χ := id

/-- PM I ✱20·14. -/
theorem star_20_14 (ψ χ : α → Prop) :
    ClassEq ψ χ → ∀ x, ψ x ↔ χ x := id

/-- PM I ✱20·15. -/
theorem star_20_15 (ψ χ : α → Prop) :
    (∀ x, ψ x ↔ χ x) ↔ ClassEq ψ χ :=
  ⟨star_20_13 ψ χ, star_20_14 ψ χ⟩

/-- PM I ✱20·151. -/
theorem star_20_151 {α : Sort _} (ψ : α → Prop) :
    ∃ φ : Star12Q289Reducibility.Predicative₁ α, ClassEq ψ φ :=
  Star12Q289Reducibility.star_12_1 ψ

end PM.Architecture.Star20Q318Kernel
