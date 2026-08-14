/-!
Exact Lean kernels for PM I, Q281 (✱11·35--✱11·38).

The two apparent variables are represented by arbitrary Lean types `α` and
`β`; a binary propositional function is therefore a predicate
`φ : α → β → Prop`.  No inhabitation, decidability, or classical axiom is
needed by any theorem in this batch.
-/

namespace PM.Architecture.Star11Q281Kernel

universe u v

/-- PM I ✱11·35. -/
theorem star_11_35_prop {α : Type u} {β : Type v} (φ : α → β → Prop) (p : Prop) :
    (∀ x y, φ x y → p) ↔ ((∃ x y, φ x y) → p) := by
  constructor
  · intro h hφ
    obtain ⟨x, y, hxy⟩ := hφ
    exact h x y hxy
  · intro h x y hxy
    exact h ⟨x, y, hxy⟩

/-- PM I ✱11·36. -/
theorem star_11_36_prop {α : Type u} {β : Type v} (φ : α → β → Prop) (z : α) (w : β) :
    φ z w → ∃ x y, φ x y := by
  intro h
  exact ⟨z, w, h⟩

/-- PM I ✱11·37. -/
theorem star_11_37_prop {α : Type u} {β : Type v} (φ ψ χ : α → β → Prop) :
    (∀ x y, φ x y → ψ x y) →
      (∀ x y, ψ x y → χ x y) →
        ∀ x y, φ x y → χ x y := by
  intro hφψ hψχ x y hφ
  exact hψχ x y (hφψ x y hφ)

/-- PM I ✱11·371. -/
theorem star_11_371_prop {α : Type u} {β : Type v} (φ ψ χ : α → β → Prop) :
    (∀ x y, φ x y ↔ ψ x y) →
      (∀ x y, ψ x y ↔ χ x y) →
        ∀ x y, φ x y ↔ χ x y := by
  intro hφψ hψχ x y
  exact (hφψ x y).trans (hψχ x y)

/-- PM I ✱11·38. -/
theorem star_11_38_prop {α : Type u} {β : Type v} (φ ψ χ : α → β → Prop) :
    (∀ x y, φ x y → ψ x y) →
      ∀ x y, φ x y ∧ χ x y → ψ x y ∧ χ x y := by
  intro h x y hφχ
  exact ⟨h x y hφχ.1, hφχ.2⟩

end PM.Architecture.Star11Q281Kernel
