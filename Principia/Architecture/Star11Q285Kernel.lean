/-!
# PM I, ✱11·521–✱11·56

Exact polymorphic readings of the five printed propositions.  The two
`Nonempty` assumptions in ✱11·56 expose PM's convention that every type has
possible arguments; they are necessary to recover each separately quantified
conjunct from the binary universal assertion.
-/

namespace PM.Architecture.Star11Q285Kernel

/-- ✱11·521. Absence of a binary counterexample is universal implication. -/
theorem star_11_521 {α β : Sort _} (φ ψ : α → β → Prop) :
    (¬ ∃ x y, φ x y ∧ ¬ ψ x y) ↔ ∀ x y, φ x y → ψ x y := by
  classical
  constructor
  · intro h x y hφ
    exact Classical.byContradiction fun hψ => h ⟨x, y, hφ, hψ⟩
  · intro h
    rintro ⟨x, y, hφ, hψ⟩
    exact hψ (h x y hφ)

/-- ✱11·53. Separation of the two apparent variables in an implication. -/
theorem star_11_53 {α β : Sort _} (φ : α → Prop) (ψ : β → Prop) :
    (∀ x y, φ x → ψ y) ↔ ((∃ x, φ x) → ∀ y, ψ y) := by
  constructor
  · intro h hex y
    obtain ⟨x, hφ⟩ := hex
    exact h x y hφ
  · intro h x y hφ
    exact h ⟨x, hφ⟩ y

/-- ✱11·54. A separated binary existential conjunction factors. -/
theorem star_11_54 {α β : Sort _} (φ : α → Prop) (ψ : β → Prop) :
    (∃ x y, φ x ∧ ψ y) ↔ ((∃ x, φ x) ∧ ∃ y, ψ y) := by
  constructor
  · rintro ⟨x, y, hφ, hψ⟩
    exact ⟨⟨x, hφ⟩, ⟨y, hψ⟩⟩
  · rintro ⟨⟨x, hφ⟩, ⟨y, hψ⟩⟩
    exact ⟨x, y, hφ, hψ⟩

/-- ✱11·55. A binary existential with a unary conjunct is nested
existential quantification. -/
theorem star_11_55 {α β : Sort _} (φ : α → Prop) (ψ : α → β → Prop) :
    (∃ x y, φ x ∧ ψ x y) ↔ ∃ x, φ x ∧ ∃ y, ψ x y := by
  constructor
  · rintro ⟨x, y, hφ, hψ⟩
    exact ⟨x, hφ, y, hψ⟩
  · rintro ⟨x, hφ, y, hψ⟩
    exact ⟨x, y, hφ, hψ⟩

/-- ✱11·56. Two separate universal assertions are equivalent to their
binary universal conjunction. -/
theorem star_11_56 {α β : Sort _} [Nonempty α] [Nonempty β]
    (φ : α → Prop) (ψ : β → Prop) :
    ((∀ x, φ x) ∧ ∀ y, ψ y) ↔ ∀ x y, φ x ∧ ψ y := by
  constructor
  · rintro ⟨hφ, hψ⟩ x y
    exact ⟨hφ x, hψ y⟩
  · intro h
    exact
      ⟨fun x => (h x (Classical.choice inferInstance)).1,
       fun y => (h (Classical.choice inferInstance) y).2⟩

end PM.Architecture.Star11Q285Kernel
