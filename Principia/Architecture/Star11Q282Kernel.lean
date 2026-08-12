namespace PM.Architecture.Star11Q282Kernel

/-!
# PM I ✱11·39–✱11·41

Kernel-checked readings of the five displayed two-variable propositions.
The two PM apparent variables are represented by independent Lean binders;
juxtaposition is conjunction and the horseshoe is implication.
-/

/-- ✱11·39: two pointwise implications combine under conjunction. -/
theorem star_11_39 {α β : Type} (φ ψ χ θ : α → β → Prop) :
    (∀ x y, φ x y → ψ x y) →
    (∀ x y, χ x y → θ x y) →
    ∀ x y, φ x y ∧ χ x y → ψ x y ∧ θ x y := by
  intro hφ hχ x y h
  exact ⟨hφ x y h.1, hχ x y h.2⟩

/-- ✱11·391: two implications with a common antecedent are equivalent to
one implication into their conjunction. -/
theorem star_11_391 {α β : Type} (φ ψ χ : α → β → Prop) :
    ((∀ x y, φ x y → ψ x y) ∧ (∀ x y, φ x y → χ x y)) ↔
      (∀ x y, φ x y → ψ x y ∧ χ x y) := by
  constructor
  · rintro ⟨hψ, hχ⟩ x y hφ
    exact ⟨hψ x y hφ, hχ x y hφ⟩
  · intro h
    exact ⟨fun x y hφ => (h x y hφ).1,
      fun x y hφ => (h x y hφ).2⟩

/-- ✱11·4: paired pointwise equivalences combine under conjunction. -/
theorem star_11_4 {α β : Type} (φ ψ χ θ : α → β → Prop) :
    (∀ x y, φ x y ↔ ψ x y) →
    (∀ x y, χ x y ↔ θ x y) →
    ∀ x y, (φ x y ∧ χ x y) ↔ (ψ x y ∧ θ x y) := by
  intro hφ hχ x y
  exact and_congr (hφ x y) (hχ x y)

/-- ✱11·401: pointwise equivalence is preserved by conjunction with a
fixed pointwise factor. -/
theorem star_11_401 {α β : Type} (φ ψ χ : α → β → Prop) :
    (∀ x y, φ x y ↔ ψ x y) →
    ∀ x y, (φ x y ∧ χ x y) ↔ (ψ x y ∧ χ x y) := by
  intro h x y
  exact and_congr (h x y) Iff.rfl

/-- ✱11·41: existential quantification distributes over disjunction in both
directions for the displayed pair of apparent variables. -/
theorem star_11_41 {α β : Type} (φ ψ : α → β → Prop) :
    ((∃ x y, φ x y) ∨ (∃ x y, ψ x y)) ↔
      (∃ x y, φ x y ∨ ψ x y) := by
  constructor
  · rintro (⟨x, y, h⟩ | ⟨x, y, h⟩)
    · exact ⟨x, y, Or.inl h⟩
    · exact ⟨x, y, Or.inr h⟩
  · rintro ⟨x, y, h | h⟩
    · exact Or.inl ⟨x, y, h⟩
    · exact Or.inr ⟨x, y, h⟩

end PM.Architecture.Star11Q282Kernel
