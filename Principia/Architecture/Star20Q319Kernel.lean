namespace PM.Architecture.Star20Q319Kernel

universe u

/-- The explicit simple-type reading of a PM class extension. -/
abbrev ClassExtension (α : Type u) := α → Prop

/-- PM I ✱20·16. -/
theorem star_20_16 (f : ClassExtension α → Prop) (ψ : ClassExtension α) :
    ∃ φ : ClassExtension α, (∀ x, φ x ↔ ψ x) ∧ (f ψ ↔ f φ) := by
  exact ⟨ψ, fun _ => Iff.rfl, Iff.rfl⟩

/-- PM I ✱20·17, retaining the ✱20·16 witness explicitly. -/
theorem star_20_17 (f : ClassExtension α → Prop) (ψ : ClassExtension α) :
    (∀ φ : ClassExtension α, f φ) → f ψ := by
  intro h
  obtain ⟨φ, _, hEquiv⟩ := star_20_16 f ψ
  exact hEquiv.mpr (h φ)

/-- PM I ✱20·18. -/
theorem star_20_18 (f : ClassExtension α → Prop)
    (φ ψ : ClassExtension α) : φ = ψ → (f φ ↔ f ψ) := by
  intro h
  cases h
  exact Iff.rfl

/-- PM I ✱20·19: Leibniz identity, implication form. -/
theorem star_20_19 (ψ χ : ClassExtension α) :
    ψ = χ ↔ ∀ f : ClassExtension α → Prop, f ψ → f χ := by
  constructor
  · intro h f hψ
    cases h
    exact hψ
  · intro h
    have : χ = ψ := h (fun extension => extension = ψ) rfl
    exact this.symm

/-- PM I ✱20·191: Leibniz identity, equivalence form. -/
theorem star_20_191 (ψ χ : ClassExtension α) :
    ψ = χ ↔ ∀ f : ClassExtension α → Prop, (f ψ ↔ f χ) := by
  constructor
  · intro h f
    cases h
    exact Iff.rfl
  · intro h
    have : χ = ψ := (h (fun extension => extension = ψ)).mp rfl
    exact this.symm

end PM.Architecture.Star20Q319Kernel
