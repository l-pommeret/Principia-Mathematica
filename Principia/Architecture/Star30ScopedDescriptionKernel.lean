/-!
# PM I, ✱30·12–✱30·19

Ten consecutive propositions about a relation's associated descriptive
function.  `Scope R y φ` is Russell's contextual occurrence ` [Rʻy].φ(Rʻy)`;
no description-valued term is introduced.
-/

namespace PM.Architecture.Star30ScopedDescriptionKernel

def Characterizes (R : α → β → Prop) (y : β) (b : α) : Prop :=
  ∀ x, R x y ↔ x = b

def ExistsAt (R : α → β → Prop) (y : β) : Prop :=
  ∃ b, Characterizes R y b

def Scope (R : α → β → Prop) (y : β) (φ : α → Prop) : Prop :=
  ∃ b, Characterizes R y b ∧ φ b

private theorem characterizer_unique
    {R : α → β → Prop} {y : β} {a b : α}
    (ha : Characterizes R y a) (hb : Characterizes R y b) : a = b := by
  exact (hb a).mp ((ha a).mpr rfl)

/-- ✱30·12. Under existence, a constant disjunct moves through the
description scope. -/
theorem star_30_12 (R : α → β → Prop) (y : β) (p : Prop) (φ : α → Prop) :
    ExistsAt R y → (Scope R y (fun x => p ∨ φ x) ↔ p ∨ Scope R y φ) := by
  rintro ⟨a, ha⟩
  constructor
  · rintro ⟨b, hb, hp | hφ⟩
    · exact Or.inl hp
    · exact Or.inr ⟨b, hb, hφ⟩
  · rintro (hp | ⟨b, hb, hφ⟩)
    · exact ⟨a, ha, Or.inl hp⟩
    · exact ⟨b, hb, Or.inr hφ⟩

/-- ✱30·13. Under existence, negation moves through description scope. -/
theorem star_30_13 (R : α → β → Prop) (y : β) (φ : α → Prop) :
    ExistsAt R y → (Scope R y (fun x => ¬ φ x) ↔ ¬ Scope R y φ) := by
  rintro ⟨a, ha⟩
  constructor
  · rintro ⟨b, hb, hn⟩ ⟨c, hc, hp⟩
    have : b = c := characterizer_unique hb hc
    exact hn (this ▸ hp)
  · intro hn
    refine ⟨a, ha, fun hp => hn ⟨a, ha, hp⟩⟩

/-- ✱30·14. Under existence, a constant conjunct moves through scope. -/
theorem star_30_14 (R : α → β → Prop) (y : β) (p : Prop) (φ : α → Prop) :
    ExistsAt R y → (Scope R y (fun x => p ∧ φ x) ↔ p ∧ Scope R y φ) := by
  intro _
  constructor
  · rintro ⟨b, hb, hp, hφ⟩
    exact ⟨hp, b, hb, hφ⟩
  · rintro ⟨hp, b, hb, hφ⟩
    exact ⟨b, hb, hp, hφ⟩

/-- ✱30·141. Under existence, implication to a constant consequent moves
outside the description scope. -/
theorem star_30_141 (R : α → β → Prop) (y : β) (p : Prop) (φ : α → Prop) :
    ExistsAt R y → (Scope R y (fun x => φ x → p) ↔ (Scope R y φ → p)) := by
  rintro ⟨a, ha⟩
  constructor
  · rintro ⟨b, hb, h⟩ ⟨c, hc, hφ⟩
    exact h (characterizer_unique hb hc ▸ hφ)
  · intro h
    exact ⟨a, ha, fun hφ => h ⟨a, ha, hφ⟩⟩

/-- ✱30·142. Under existence, equivalence with a constant proposition
moves through description scope. -/
theorem star_30_142 (R : α → β → Prop) (y : β) (p : Prop) (φ : α → Prop) :
    ExistsAt R y → (Scope R y (fun x => p ↔ φ x) ↔ (p ↔ Scope R y φ)) := by
  rintro ⟨a, ha⟩
  constructor
  · rintro ⟨b, hb, h⟩
    constructor
    · exact fun hp => ⟨b, hb, h.mp hp⟩
    · rintro ⟨c, hc, hφ⟩
      exact h.mpr (characterizer_unique hb hc ▸ hφ)
  · intro h
    refine ⟨a, ha, ⟨?_, fun hφ => h.mpr ⟨a, ha, hφ⟩⟩⟩
    intro hp
    obtain ⟨b, hb, hφ⟩ := h.mp hp
    exact characterizer_unique hb ha ▸ hφ

/-- ✱30·15. A constant conjunct may always be placed inside the scope. -/
theorem star_30_15 (R : α → β → Prop) (y : β) (p : Prop) (φ : α → Prop) :
    p ∧ Scope R y φ ↔ Scope R y (fun x => p ∧ φ x) := by
  constructor
  · rintro ⟨hp, b, hb, hφ⟩
    exact ⟨b, hb, hp, hφ⟩
  · rintro ⟨b, hb, hp, hφ⟩
    exact ⟨hp, b, hb, hφ⟩

/-- ✱30·16. Two independent description scopes commute. -/
theorem star_30_16 (R : α → β → Prop) (S : γ → δ → Prop)
    (y : β) (z : δ) (f : α → γ → Prop) :
    Scope R y (fun a => Scope S z (fun b => f a b)) ↔
      Scope S z (fun b => Scope R y (fun a => f a b)) := by
  constructor
  · rintro ⟨a, ha, ⟨b, hb, hf⟩⟩
    exact ⟨b, hb, a, ha, hf⟩
  · rintro ⟨b, hb, ⟨a, ha, hf⟩⟩
    exact ⟨a, ha, b, hb, hf⟩

/-- ✱30·17. The double description scope has its explicit two-witness
expansion. -/
theorem star_30_17 (R : α → β → Prop) (S : γ → δ → Prop)
    (y : β) (z : δ) (f : α → γ → Prop) :
    Scope R y (fun a => Scope S z (fun b => f a b)) ↔
      ∃ a b, Characterizes R y a ∧ Characterizes S z b ∧ f a b := by
  constructor
  · rintro ⟨a, ha, ⟨b, hb, hf⟩⟩
    exact ⟨a, b, ha, hb, hf⟩
  · rintro ⟨a, b, ha, hb, hf⟩
    exact ⟨a, ha, b, hb, hf⟩

/-- ✱30·18. A universally true matrix holds of an existent descriptive
function value. -/
theorem star_30_18 (R : α → β → Prop) (y : β) (φ : α → Prop) :
    ExistsAt R y → (∀ z, φ z) → Scope R y φ := by
  rintro ⟨b, hb⟩ hφ
  exact ⟨b, hb, hφ b⟩

/-- ✱30·19. Identity of the descriptive value with `b` permits exact
substitution in an arbitrary matrix. -/
theorem star_30_19 (R : α → β → Prop) (y : β) (b : α) (φ : α → Prop) :
    Characterizes R y b → (Scope R y φ ↔ φ b) := by
  intro hb
  constructor
  · rintro ⟨a, ha, hφ⟩
    exact characterizer_unique ha hb ▸ hφ
  · exact fun hφ => ⟨b, hb, hφ⟩

end PM.Architecture.Star30ScopedDescriptionKernel
