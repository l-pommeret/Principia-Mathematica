import Principia.Architecture.Star30ScopedDescriptionKernel

/-! # PM I, ✱30·2–✱30·35: ten consecutive descriptive-function laws. -/

namespace PM.Architecture.Star30ExistenceKernel

open PM.Architecture.Star30ScopedDescriptionKernel

private theorem characterizer_unique
    {R : α → β → Prop} {y : β} {a b : α}
    (ha : Characterizes R y a) (hb : Characterizes R y b) : a = b := by
  exact (hb a).mp ((ha a).mpr rfl)

/-- ✱30·2. Existence of the associated descriptive function is exactly
existence of a term uniquely related to its argument. -/
theorem star_30_2 (R : α → β → Prop) (y : β) :
    ExistsAt R y ↔ ∃ b, Characterizes R y b := Iff.rfl

/-- ✱30·21. Expanded existence-and-uniqueness form of ✱30·2. -/
theorem star_30_21 (R : α → β → Prop) (y : β) :
    ExistsAt R y ↔
      ((∃ x, R x y) ∧ ∀ x z, R x y → R z y → x = z) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b, (hb b).mpr rfl⟩, ?_⟩
    intro x z hx hz
    exact ((hb x).mp hx).trans ((hb z).mp hz).symm
  · rintro ⟨⟨b, hb⟩, hu⟩
    refine ⟨b, fun x => ⟨fun hx => hu x b hx hb, ?_⟩⟩
    rintro rfl
    exact hb

/-- Contextual equality of `Rʻy` with the description determined by its own
matrix, the right side printed at ✱30·22. -/
def SelfDescriptionIdentity (R : α → β → Prop) (y : β) : Prop :=
  Scope R y (Characterizes R y)

/-- ✱30·22. The associated value exists iff it is identical with the
description of the terms related to `y`. -/
theorem star_30_22 (R : α → β → Prop) (y : β) :
    ExistsAt R y ↔ SelfDescriptionIdentity R y := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, hb⟩
  · rintro ⟨b, hb, _⟩
    exact ⟨b, hb⟩

/-- ✱30·3. Identity with the associated value is exactly formal
equivalence between the relation matrix and identity with that term. -/
theorem star_30_3 (R : α → β → Prop) (y : β) (b : α) :
    Characterizes R y b ↔ ∀ x, (R x y ↔ x = b) := Iff.rfl

/-- ✱30·31. The identity condition separates into relation of the value
and uniqueness of every related term. -/
theorem star_30_31 (R : α → β → Prop) (y : β) (b : α) :
    Characterizes R y b ↔ (R b y ∧ ∀ x, R x y → x = b) := by
  constructor
  · intro h
    exact ⟨(h b).mpr rfl, fun x hx => (h x).mp hx⟩
  · rintro ⟨hb, hu⟩ x
    exact ⟨hu x, fun h => h ▸ hb⟩

/-- ✱30·32. Existence is equivalent to the relation holding of its
contextually scoped associated value. -/
theorem star_30_32 (R : α → β → Prop) (y : β) :
    ExistsAt R y ↔ Scope R y (fun x => R x y) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, (hb b).mpr rfl⟩
  · rintro ⟨b, hb, _⟩
    exact ⟨b, hb⟩

/-- ✱30·33. Under existence, assertion at the associated value is
equivalent both to an existential conjunction and to universal implication. -/
theorem star_30_33 (R : α → β → Prop) (y : β) (φ : α → Prop) :
    ExistsAt R y →
      ((Scope R y φ ↔ ∃ x, R x y ∧ φ x) ∧
       ((∃ x, R x y ∧ φ x) ↔ ∀ x, R x y → φ x)) := by
  rintro ⟨b, hb⟩
  constructor
  · constructor
    · rintro ⟨a, ha, hφ⟩
      exact ⟨a, (ha a).mpr rfl, hφ⟩
    · rintro ⟨a, ha, hφ⟩
      have hab : a = b := (hb a).mp ha
      exact ⟨b, hb, hab ▸ hφ⟩
  · constructor
    · rintro ⟨a, ha, hφ⟩ x hx
      have hxa : x = a := ((hb x).mp hx).trans ((hb a).mp ha).symm
      exact hxa ▸ hφ
    · intro h
      exact ⟨b, (hb b).mpr rfl, h b ((hb b).mpr rfl)⟩

/-- ✱30·34. Formally equivalent relation matrices have equivalent
existence conditions. -/
theorem star_30_34 (R S : α → β → Prop) (y : β)
    (h : ∀ x, R x y ↔ S x y) : ExistsAt R y ↔ ExistsAt S y := by
  constructor <;> rintro ⟨b, hb⟩ <;> refine ⟨b, fun x => ?_⟩
  · exact (h x).symm.trans (hb x)
  · exact (h x).trans (hb x)

/-- ✱30·341. Under formal equivalence and existence, the two associated
descriptive values are identical, expressed contextually. -/
theorem star_30_341 (R S : α → β → Prop) (y : β)
    (h : ∀ x, R x y ↔ S x y) :
    ExistsAt R y →
      ∃ a b, Characterizes R y a ∧ Characterizes S y b ∧ a = b := by
  rintro ⟨a, ha⟩
  have hs : Characterizes S y a := fun x => (h x).symm.trans (ha x)
  exact ⟨a, a, ha, hs, rfl⟩

/-- ✱30·35. Equal relations have equivalent associated-value existence. -/
theorem star_30_35 (R S : α → β → Prop) (y : β) :
    R = S → (ExistsAt R y ↔ ExistsAt S y) := by
  rintro rfl
  exact Iff.rfl

end PM.Architecture.Star30ExistenceKernel
