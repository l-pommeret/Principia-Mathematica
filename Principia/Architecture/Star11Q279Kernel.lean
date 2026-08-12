import Principia.Architecture.Star11Q275Definitions

namespace PM.Architecture.Star11Q279Kernel

/-- PM I ✱11·25: negation of a binary existential is equivalent to pointwise
negation.  The two binders occur in the exact order fixed by ✱11·03. -/
theorem star_11_25 (φ : α → β → Prop) :
    (¬ ∃ x y, φ x y) ↔ ∀ x y, ¬ φ x y := by
  constructor
  · intro h x y hxy
    exact h ⟨x, y, hxy⟩
  · intro h hex
    obtain ⟨x, y, hxy⟩ := hex
    exact h x y hxy

/-- PM I ✱11·26: an existential witness uniform in `y` supplies a possibly
different existential witness at each `y`. -/
theorem star_11_26 (φ : α → β → Prop) :
    (∃ x, ∀ y, φ x y) → ∀ y, ∃ x, φ x y := by
  rintro ⟨x, hx⟩ y
  exact ⟨x, hx y⟩

/-- PM I ✱11·27, first displayed equivalence: expand the binary existential
of ✱11·03 while leaving the final apparent variable explicit. -/
theorem star_11_27_left (φ : α → β → γ → Prop) :
    (∃ x y, ∃ z, φ x y z) ↔ ∃ x, ∃ y z, φ x y z := by
  rfl

/-- PM I ✱11·27, second displayed equivalence: the right-hand expression is
the ternary existential abbreviation of ✱11·04. -/
theorem star_11_27 (φ : α → β → γ → Prop) :
    (∃ x, ∃ y z, φ x y z) ↔ ∃ x y z, φ x y z := by
  rfl

/-- PM I ✱11·3: a proposition independent of the two apparent variables may
be moved underneath their universal binders. -/
theorem star_11_3 (p : Prop) (φ : α → β → Prop) :
    (p → ∀ x y, φ x y) ↔ ∀ x y, p → φ x y := by
  constructor
  · intro h x y hp
    exact h hp x y
  · intro h hp x y
    exact h x y hp

/-- PM I ✱11·31: conjunction of two binary universal propositions is
equivalent to the universal pointwise conjunction. -/
theorem star_11_31 (φ ψ : α → β → Prop) :
    ((∀ x y, φ x y) ∧ (∀ x y, ψ x y)) ↔ ∀ x y, φ x y ∧ ψ x y := by
  constructor
  · rintro ⟨hφ, hψ⟩ x y
    exact ⟨hφ x y, hψ x y⟩
  · intro h
    exact ⟨fun x y => (h x y).1, fun x y => (h x y).2⟩

end PM.Architecture.Star11Q279Kernel
