/-!
# PM I ✱13·21 and ✱13·22

The two displayed binary identity-elimination propositions, represented with
Lean equality and explicit universal/existential binders.
-/

namespace PM.Architecture.Star13Q295IdentityKernel

/-- ✱13·21. Formal implication from the two identity hypotheses is equivalent
to the value of the binary propositional function at those identities. -/
theorem star_13_21 {α β : Sort _} (x : α) (y : β)
    (φ : α → β → Prop) :
    (∀ z w, z = x ∧ w = y → φ z w) ↔ φ x y := by
  constructor
  · intro h
    exact h x y ⟨rfl, rfl⟩
  · intro h z w hzw
    rcases hzw with ⟨rfl, rfl⟩
    exact h

/-- ✱13·22. Existentially conjoining the two identities selects exactly the
displayed value of the binary propositional function. -/
theorem star_13_22 {α β : Sort _} (x : α) (y : β)
    (φ : α → β → Prop) :
    (∃ z w, z = x ∧ w = y ∧ φ z w) ↔ φ x y := by
  constructor
  · rintro ⟨z, w, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩

end PM.Architecture.Star13Q295IdentityKernel
