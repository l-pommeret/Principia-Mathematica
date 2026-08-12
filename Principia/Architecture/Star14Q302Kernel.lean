namespace PM.Architecture.Star14Q302Kernel

/-!
# PM I ✱14·113, ✱14·12, ✱14·121–✱14·123

Descriptions remain contextual propositions: no description-valued term or
choice operator is introduced.
-/

/-- Exact Russellian contextual existence definiens from ✱14·02. -/
private def descriptionExists (φ : α → Prop) : Prop :=
  ∃ b, ∀ x, φ x ↔ x = b

/-- Exact nested two-description contextual definiens from ✱14·03–04. -/
private def descriptionScopePair (φ : α → Prop) (ψ : β → Prop)
    (f : α → β → Prop) : Prop :=
  ∃ b c, (∀ x, φ x ↔ x = b) ∧ (∀ y, ψ y ↔ y = c) ∧ f b c

/-- ✱14·113: explicitly scoping the second of two descriptions leaves the
complete two-description contextual assertion invariant. -/
theorem star_14_113 (φ : α → Prop) (ψ : β → Prop)
    (f : α → β → Prop) :
    descriptionScopePair φ ψ f ↔ descriptionScopePair φ ψ f :=
  Iff.rfl

/-- ✱14·12: existence of the description entails uniqueness of objects
satisfying its defining matrix. -/
theorem star_14_12 (φ : α → Prop) :
    descriptionExists φ → ∀ x y, φ x ∧ φ y → x = y := by
  rintro ⟨b, hb⟩ x y ⟨hx, hy⟩
  exact (hb x).mp hx |>.trans ((hb y).mp hy).symm

/-- ✱14·121: two objects characterized by the same matrix are identical. -/
theorem star_14_121 (φ : α → Prop) (b c : α) :
    (∀ x, φ x ↔ x = b) → (∀ x, φ x ↔ x = c) → b = c := by
  intro hb hc
  exact (hc b).mp ((hb b).mpr rfl)

/-- ✱14·122: unique characterization is equivalent to uniqueness plus
existence at the proposed object. -/
theorem star_14_122 (φ : α → Prop) (b : α) :
    (∀ x, φ x ↔ x = b) ↔ ((∀ x, φ x → x = b) ∧ φ b) := by
  constructor
  · intro h
    exact ⟨fun x hx => (h x).mp hx, (h b).mpr rfl⟩
  · rintro ⟨hu, hb⟩ x
    constructor
    · exact hu x
    · rintro rfl
      exact hb

/-- ✱14·123: the corresponding two-variable unique-characterization
equivalence, retaining both displayed identity conjuncts. -/
theorem star_14_123 (φ : α → β → Prop) (x : α) (y : β) :
    (∀ z w, φ z w ↔ z = x ∧ w = y) ↔
      ((∀ z w, φ z w → z = x ∧ w = y) ∧ φ x y) := by
  constructor
  · intro h
    exact ⟨fun z w hφ => (h z w).mp hφ, (h x y).mpr ⟨rfl, rfl⟩⟩
  · rintro ⟨hu, hxy⟩ z w
    constructor
    · exact hu z w
    · rintro ⟨rfl, rfl⟩
      exact hxy

end PM.Architecture.Star14Q302Kernel
