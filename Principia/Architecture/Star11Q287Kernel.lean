/-!
Exact Lean kernels for PM I, Q287 (✱11·6, ✱11·61--✱11·63, ✱11·7).

Every formal implication keeps all variables displayed by PM.  In particular,
the witnesses in ✱11·61 are obtained from its antecedent rather than from an
inhabitedness assumption.
-/

namespace PM.Architecture.Star11Q287Kernel

universe u v

/-- PM I ✱11·6. -/
theorem star_11_6 {α : Type u} {β : Type v}
    (φ : α → β → Prop) (ψ : β → Prop) (χ : α → Prop) :
    (∃ x, (∃ y, φ x y ∧ ψ y) ∧ χ x) ↔
      ∃ y, (∃ x, φ x y ∧ χ x) ∧ ψ y := by
  constructor
  · rintro ⟨x, ⟨y, hφ, hψ⟩, hχ⟩
    exact ⟨y, ⟨x, hφ, hχ⟩, hψ⟩
  · rintro ⟨y, ⟨x, hφ, hχ⟩, hψ⟩
    exact ⟨x, ⟨y, hφ, hψ⟩, hχ⟩

/-- PM I ✱11·61. -/
theorem star_11_61 {α : Type u} {β : Type v}
    (φ : α → Prop) (ψ : α → β → Prop) :
    (∃ y, ∀ x, φ x → ψ x y) →
      ∀ x, φ x → ∃ y, ψ x y := by
  rintro ⟨y, h⟩ x hφ
  exact ⟨y, h x hφ⟩

/-- PM I ✱11·62. -/
theorem star_11_62 {α : Type u} {β : Type v}
    (φ : α → Prop) (ψ χ : α → β → Prop) :
    (∀ x y, φ x ∧ ψ x y → χ x y) ↔
      ∀ x, φ x → ∀ y, ψ x y → χ x y := by
  constructor
  · intro h x hφ y hψ
    exact h x y ⟨hφ, hψ⟩
  · intro h x y hφψ
    exact h x hφψ.1 y hφψ.2

/-- PM I ✱11·63. -/
theorem star_11_63 {α : Type u} {β : Type v}
    (φ ψ : α → β → Prop) :
    (¬ ∃ x y, φ x y) → ∀ x y, φ x y → ψ x y := by
  intro h x y hφ
  exact False.elim (h ⟨x, y, hφ⟩)

/-- PM I ✱11·7.  Both positions have the same type because the printed
formula applies `φ` to both `(x,y)` and `(y,x)`. -/
theorem star_11_7 {α : Type u} (φ : α → α → Prop) :
    (∃ x y, φ x y ∨ φ y x) ↔ ∃ x y, φ x y := by
  constructor
  · rintro ⟨x, y, h | h⟩
    · exact ⟨x, y, h⟩
    · exact ⟨y, x, h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨x, y, Or.inl h⟩

end PM.Architecture.Star11Q287Kernel
