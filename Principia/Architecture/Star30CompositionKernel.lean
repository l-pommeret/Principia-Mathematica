import Principia.Architecture.Star30ExistenceKernel

/-! # PM I, ✱30·36–✱30·52: the final nine propositions of ✱30. -/

namespace PM.Architecture.Star30CompositionKernel

open PM.Architecture.Star30ScopedDescriptionKernel

def ValueEqual (R S : α → β → Prop) (y : β) : Prop :=
  ∃ a b, Characterizes R y a ∧ Characterizes S y b ∧ a = b

def ComposeScope (P : α → β → Prop) (Q : β → γ → Prop)
    (z : γ) (φ : α → Prop) : Prop :=
  Scope Q z (fun c => Scope P c φ)

def ComposeExists (P : α → β → Prop) (Q : β → γ → Prop)
    (z : γ) : Prop :=
  ∃ b c, Characterizes P c b ∧ Characterizes Q z c

/-- ✱30·36. Equal relations with an existent value have identical
associated values. -/
theorem star_30_36 (R S : α → β → Prop) (y : β) :
    ExistsAt R y → R = S → ValueEqual R S y := by
  rintro ⟨a, ha⟩ rfl
  exact ⟨a, a, ha, ha, rfl⟩

/-- ✱30·37. Equal arguments give identical values of an existent
descriptive function. -/
theorem star_30_37 (R : α → β → Prop) (y z : β) :
    ExistsAt R y → y = z → ValueEqual R R z := by
  rintro ⟨a, ha⟩ rfl
  exact ⟨a, a, ha, ha, rfl⟩

/-- ✱30·4. If the associated value exists, identity with `a` is
equivalent to `a` bearing the relation to `y`. -/
theorem star_30_4 (R : α → β → Prop) (y : β) (a : α) :
    ExistsAt R y → (Characterizes R y a ↔ R a y) := by
  rintro ⟨b, hb⟩
  constructor
  · exact fun ha => (ha a).mpr rfl
  · intro hay
    have hab : a = b := (hb a).mp hay
    exact hab ▸ hb

/-- ✱30·41. Pointwise identity of associated values is equivalent to
everywhere existence together with equality of the relations. -/
theorem star_30_41 (R S : α → β → Prop) :
    (∀ y, ValueEqual R S y) ↔ ((∀ y, ExistsAt R y) ∧ R = S) := by
  constructor
  · intro h
    refine ⟨fun y => ?_, ?_⟩
    · obtain ⟨a, b, ha, hb, hab⟩ := h y
      exact ⟨a, ha⟩
    · funext x y
      apply propext
      obtain ⟨a, b, ha, hb, hab⟩ := h y
      subst b
      exact (ha x).trans (hb x).symm
  · rintro ⟨hex, rfl⟩ y
    obtain ⟨a, ha⟩ := hex y
    exact ⟨a, a, ha, ha, rfl⟩

/-- ✱30·42. When `R` exists everywhere, pointwise value identity is
equivalent simply to equality of relations. -/
theorem star_30_42 (R S : α → β → Prop) (hex : ∀ y, ExistsAt R y) :
    (∀ y, ValueEqual R S y) ↔ R = S := by
  constructor
  · exact fun h => (star_30_41 R S).mp h |>.2
  · rintro rfl y
    obtain ⟨a, ha⟩ := hex y
    exact ⟨a, a, ha, ha, rfl⟩

/-- ✱30·5. Existence of a composed descriptive value entails existence
of the inner descriptive value. -/
theorem star_30_5 (P : α → β → Prop) (Q : β → γ → Prop) (z : γ) :
    ComposeExists P Q z → ExistsAt Q z := by
  rintro ⟨b, c, hp, hq⟩
  exact ⟨c, hq⟩

/-- ✱30·501. Exact two-witness expansion of a proposition about the
composed descriptive value. -/
theorem star_30_501 (P : α → β → Prop) (Q : β → γ → Prop)
    (z : γ) (φ : α → Prop) :
    ComposeScope P Q z φ ↔
      ∃ b c, Characterizes Q z c ∧ Characterizes P c b ∧ φ b := by
  constructor
  · rintro ⟨c, hq, b, hp, hφ⟩
    exact ⟨b, c, hq, hp, hφ⟩
  · rintro ⟨b, c, hq, hp, hφ⟩
    exact ⟨c, hq, b, hp, hφ⟩

/-- ✱30·51. Identity with a composed value is equivalent to a middle
value linking the two component identities. -/
theorem star_30_51 (P : α → β → Prop) (Q : β → γ → Prop)
    (z : γ) (b : α) :
    ComposeScope P Q z (fun a => a = b) ↔
      ∃ c, Characterizes P c b ∧ Characterizes Q z c := by
  constructor
  · rintro ⟨c, hq, a, hp, hab⟩
    subst a
    exact ⟨c, hp, hq⟩
  · rintro ⟨c, hp, hq⟩
    exact ⟨c, hq, b, hp, rfl⟩

/-- ✱30·52. Existence of a composed value is exactly existence of linked
outer and inner values. -/
theorem star_30_52 (P : α → β → Prop) (Q : β → γ → Prop) (z : γ) :
    ComposeExists P Q z ↔
      ∃ b c, Characterizes P c b ∧ Characterizes Q z c := Iff.rfl

end PM.Architecture.Star30CompositionKernel
