import Principia.Architecture.Star14Q299Kernel

namespace PM.Architecture.Star14Q311Kernel

open PM.Architecture.Star14Q299Kernel

/-- PM I ✱14·3. An explicitly equivalence-respecting propositional function
commutes with contextual description scope whenever the description exists. -/
theorem star_14_3 (f : Prop → Prop) (φ χ : α → Prop)
    (congruent : ∀ p q, (p ↔ q) → (f p ↔ f q)) :
    DescriptionExists φ →
      (f (DescriptionScope φ χ) ↔ DescriptionScope φ (fun b => f (χ b))) := by
  rintro ⟨b, hb⟩
  have scope_iff : DescriptionScope φ χ ↔ χ b := by
    constructor
    · rintro ⟨c, hc, hχ⟩
      have hcb : c = b := (hb c).mp ((hc c).mpr rfl)
      simpa [hcb] using hχ
    · intro hχ
      exact ⟨b, hb, hχ⟩
  have lifted := congruent (DescriptionScope φ χ) (χ b) scope_iff
  constructor
  · intro hf
    exact ⟨b, hb, lifted.mp hf⟩
  · rintro ⟨c, hc, hf⟩
    have hcb : c = b := (hb c).mp ((hc c).mpr rfl)
    exact lifted.mpr (by simpa [hcb] using hf)

/-- PM I ✱14·31. Under existence, disjunction with an independent
proposition commutes with contextual description scope. -/
theorem star_14_31 (p : Prop) (φ χ : α → Prop) :
    DescriptionExists φ →
      (DescriptionScope φ (fun b => p ∨ χ b) ↔ p ∨ DescriptionScope φ χ) := by
  rintro hex
  constructor
  · rintro ⟨b, hb, hp | hχ⟩
    · exact Or.inl hp
    · exact Or.inr ⟨b, hb, hχ⟩
  · rintro (hp | ⟨b, hb, hχ⟩)
    · obtain ⟨b, hb⟩ := hex
      exact ⟨b, hb, Or.inl hp⟩
    · exact ⟨b, hb, Or.inr hχ⟩

/-- PM I ✱14·32. Description existence is equivalent to contextual negation
agreeing with the negation of contextual assertion. -/
theorem star_14_32 (φ χ : α → Prop) :
    DescriptionExists φ ↔
      (DescriptionScope φ (fun b => ¬ χ b) ↔ ¬ DescriptionScope φ χ) := by
  constructor
  · rintro ⟨b, hb⟩
    constructor
    · rintro ⟨c, hc, hnχ⟩ ⟨d, hd, hχ⟩
      have hcb : c = b := (hb c).mp ((hc c).mpr rfl)
      have hdb : d = b := (hb d).mp ((hd d).mpr rfl)
      cases hcb
      cases hdb
      exact hnχ hχ
    · intro hnot
      exact ⟨b, hb, fun hχ => hnot ⟨b, hb, hχ⟩⟩
  · intro h
    exact Classical.byContradiction fun hno =>
      have noScope (ψ : α → Prop) : ¬ DescriptionScope φ ψ := by
        rintro ⟨b, hb, _⟩
        exact hno ⟨b, hb⟩
      noScope (fun b => ¬ χ b) (h.mpr (noScope χ))

end PM.Architecture.Star14Q311Kernel
