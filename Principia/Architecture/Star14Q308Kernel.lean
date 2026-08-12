namespace PM.Architecture.Star14Q308Kernel

/-!
# PM I ✱14·242, ✱14·25–✱14·271

Exact contextual-description readings. A description is never reified as a
term: application and identity retain their complete Russellian scopes.
-/

private def characterizes (φ : α → Prop) (b : α) : Prop :=
  ∀ x, φ x ↔ x = b

private def descriptionExists (φ : α → Prop) : Prop :=
  ∃ b, characterizes φ b

private def descriptionApplies (φ ψ : α → Prop) : Prop :=
  ∃ b, characterizes φ b ∧ ψ b

private def descriptionsEqual (φ ψ : α → Prop) : Prop :=
  ∃ b, characterizes φ b ∧ characterizes ψ b

/-- ✱14·242: a displayed unique characterization permits substitution of
its object for the contextual description, in both directions. -/
theorem star_14_242 (φ ψ : α → Prop) (b : α) :
    characterizes φ b → (ψ b ↔ descriptionApplies φ ψ) := by
  intro hb
  constructor
  · intro hψ
    exact ⟨b, hb, hψ⟩
  · rintro ⟨c, hc, hψ⟩
    have hcb : c = b := (hb c).mp ((hc c).mpr rfl)
    exact hcb ▸ hψ

/-- ✱14·25: when the description exists, implication from its defining
matrix is equivalent to contextual evaluation. -/
theorem star_14_25 (φ ψ : α → Prop) :
    descriptionExists φ →
      ((∀ x, φ x → ψ x) ↔ descriptionApplies φ ψ) := by
  rintro ⟨b, hb⟩
  constructor
  · intro h
    exact ⟨b, hb, h b ((hb b).mpr rfl)⟩
  · rintro ⟨c, hc, hψ⟩ x hx
    have hxc : x = c := (hc x).mp hx
    exact hxc ▸ hψ

/-- ✱14·26: when the description exists, an existential conjunction with
its defining matrix is equivalent to contextual evaluation. -/
theorem star_14_26 (φ ψ : α → Prop) :
    descriptionExists φ →
      ((∃ x, φ x ∧ ψ x) ↔ descriptionApplies φ ψ) := by
  rintro ⟨b, hb⟩
  constructor
  · rintro ⟨x, hx, hψ⟩
    have hxb : x = b := (hb x).mp hx
    exact ⟨b, hb, hxb ▸ hψ⟩
  · rintro ⟨c, hc, hψ⟩
    exact ⟨c, (hc c).mpr rfl, hψ⟩

/-- ✱14·27: provided the first description exists, pointwise equivalence of
the matrices is equivalent to contextual identity of their descriptions. -/
theorem star_14_27 (φ ψ : α → Prop) :
    descriptionExists φ →
      ((∀ x, φ x ↔ ψ x) ↔ descriptionsEqual φ ψ) := by
  rintro ⟨b, hb⟩
  constructor
  · intro h
    refine ⟨b, hb, fun x => ?_⟩
    exact (h x).symm.trans (hb x)
  · rintro ⟨c, hcφ, hcψ⟩ x
    exact (hcφ x).trans (hcψ x).symm

/-- ✱14·271: pointwise equivalent matrices have equivalent contextual
description-existence assertions. -/
theorem star_14_271 (φ ψ : α → Prop) :
    (∀ x, φ x ↔ ψ x) →
      (descriptionExists φ ↔ descriptionExists ψ) := by
  intro h
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun x => (h x).symm.trans (hb x)⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, fun x => (h x).trans (hb x)⟩

end PM.Architecture.Star14Q308Kernel
