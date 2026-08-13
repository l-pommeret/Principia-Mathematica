namespace PM.Architecture.Star9Star10MissingKernel

/-! Exact propositional readings of the two previously uncovered results.
The arbitrary Lean type is the assigned range of the apparent variable. -/

/-- PM I ✱9·34: `⊢ : (x).φx ⊃ : p ∨ (x).φx`. -/
theorem star_9_34 {X : Type} (p : Prop) (φ : X → Prop) :
    (∀ x, φ x) → p ∨ ∀ x, φ x := by
  intro h
  exact Or.inr h

/-- PM I ✱10·14: two universal assertions imply the conjunction of
their instances at the same arbitrary argument. -/
theorem star_10_14 {X : Type} (φ ψ : X → Prop) (y : X) :
    (∀ x, φ x) → (∀ x, ψ x) → φ y ∧ ψ y := by
  intro hφ hψ
  exact ⟨hφ y, hψ y⟩

end PM.Architecture.Star9Star10MissingKernel
