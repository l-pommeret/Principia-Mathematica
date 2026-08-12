namespace PM.Architecture.Star20Q322Kernel

/-!
# PM I ✱20·54–✱20·58

A PM class over `ι` is represented extensionally by its membership predicate
`ι → Prop`. Class descriptions remain Russellian contextual propositions;
they are never converted into choice-selected class terms.
-/

private def classCondition (φ : ι → Prop) (α : ι → Prop) : Prop :=
  ∀ x, α x ↔ φ x

private def descriptionEquals (target : κ) (condition : κ → Prop) : Prop :=
  ∀ candidate, condition candidate ↔ candidate = target

private def descriptionExists (condition : κ → Prop) : Prop :=
  ∃ target, descriptionEquals target condition

private def descriptionApplies (condition continuation : κ → Prop) : Prop :=
  ∃ target, descriptionEquals target condition ∧ continuation target

/-- ✱20·54: existential substitution of an identical class. -/
theorem star_20_54 (φ : κ → Prop) (α : κ) :
    (∃ β, β = α ∧ φ β) ↔ φ α := by
  constructor
  · rintro ⟨_β, rfl, hφ⟩
    exact hφ
  · intro hφ
    exact ⟨α, rfl, hφ⟩

/-- ✱20·55: the extension of `φ` is exactly the contextual description of
the class whose membership is formally equivalent to `φ`. -/
theorem star_20_55 (φ : ι → Prop) :
    descriptionEquals φ (classCondition φ) := by
  intro α
  constructor
  · intro h
    funext x
    exact propext (h x)
  · rintro rfl
    exact fun _ => Iff.rfl

/-- ✱20·56: that contextual class description exists. -/
theorem star_20_56 (φ : ι → Prop) :
    descriptionExists (classCondition φ) := by
  exact ⟨φ, star_20_55 φ⟩

/-- ✱20·57: identity with a contextual class description permits
substitution in an arbitrary class propositional function. -/
theorem star_20_57 (φ : ι → Prop) (f g : (ι → Prop) → Prop) :
    descriptionEquals φ f →
      (g φ ↔ descriptionApplies f g) := by
  intro h
  constructor
  · intro hg
    exact ⟨φ, h, hg⟩
  · rintro ⟨α, hα, hg⟩
    have haφ : α = φ := (h α).mp ((hα α).mpr rfl)
    exact haφ ▸ hg

/-- ✱20·58: every class is the contextual description of the class identical
with it. -/
theorem star_20_58 (φ : ι → Prop) :
    descriptionEquals φ (fun α => α = φ) := by
  exact fun _ => Iff.rfl

end PM.Architecture.Star20Q322Kernel
