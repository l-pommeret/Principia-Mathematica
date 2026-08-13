import Principia.Architecture.Star34QProofBlock

/-! # PM I, ✱34·28–33: eight consecutive relation theorems. -/

namespace PM.Architecture.Star34QProofBlock2

open PM.Architecture.Star34QProofBlock

def NonemptyRelation (R : Relation α β) : Prop := ∃ x y, R x y
def EmptyRelation (R : Relation α β) : Prop := ∀ x y, ¬ R x y
def domain (R : Relation α β) (x : α) : Prop := ∃ y, R x y
def converseDomain (R : Relation α β) (y : β) : Prop := ∃ x, R x y
def field (R : Relation α α) (x : α) : Prop := domain R x ∨ converseDomain R x

/-- ✱34·28. Equality transports the right factor of composition. -/
theorem star_34_28 (R R' : Relation β γ) (P : Relation α β) :
    R = R' → compose P R = compose P R' := by
  rintro rfl
  rfl

/-- ✱34·29. Equality transports the middle factor of a triple product. -/
theorem star_34_29 (R R' : Relation β γ) (P : Relation α β)
    (Q : Relation γ δ) :
    R = R' → compose (compose P R) Q = compose (compose P R') Q := by
  rintro rfl
  rfl

/-- ✱34·3. A composite exists iff the converse domain of its left factor
meets the domain of its right factor. -/
theorem star_34_3 (P : Relation α β) (Q : Relation β γ) :
    NonemptyRelation (compose P Q) ↔
      ∃ y, converseDomain P y ∧ domain Q y := by
  constructor
  · rintro ⟨x, z, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hxy⟩, ⟨z, hyz⟩⟩
  · rintro ⟨y, ⟨x, hxy⟩, ⟨z, hyz⟩⟩
    exact ⟨x, z, y, hxy, hyz⟩

/-- ✱34·301. The meeting class is empty iff the composite is empty. -/
theorem star_34_301 (P : Relation α β) (Q : Relation β γ) :
    (∀ y, ¬ (converseDomain P y ∧ domain Q y)) ↔
      EmptyRelation (compose P Q) := by
  constructor
  · intro disjoint x z
    rintro ⟨y, hxy, hyz⟩
    exact disjoint y ⟨⟨x, hxy⟩, ⟨z, hyz⟩⟩
  · intro empty y
    rintro ⟨⟨x, hxy⟩, ⟨z, hyz⟩⟩
    exact empty x z ⟨y, hxy, hyz⟩

/-- ✱34·302. Disjoint fields force both orders of composition to be empty. -/
theorem star_34_302 (P Q : Relation α α)
    (disjoint : ∀ x, ¬ (field P x ∧ field Q x)) :
    EmptyRelation (compose P Q) ∧ EmptyRelation (compose Q P) := by
  constructor
  · intro x z
    rintro ⟨y, hxy, hyz⟩
    exact disjoint y ⟨Or.inr ⟨x, hxy⟩, Or.inl ⟨z, hyz⟩⟩
  · intro x z
    rintro ⟨y, hxy, hyz⟩
    exact disjoint y ⟨Or.inl ⟨z, hyz⟩, Or.inr ⟨x, hxy⟩⟩

/-- ✱34·31. Existence of a composite implies existence of both factors. -/
theorem star_34_31 (P : Relation α β) (Q : Relation β γ) :
    NonemptyRelation (compose P Q) →
      NonemptyRelation P ∧ NonemptyRelation Q := by
  rintro ⟨x, z, y, hxy, hyz⟩
  exact ⟨⟨x, y, hxy⟩, ⟨y, z, hyz⟩⟩

/-- ✱34·32. An empty factor makes the composite empty. -/
theorem star_34_32 (P : Relation α β) (Q : Relation β γ) :
    EmptyRelation P ∨ EmptyRelation Q → EmptyRelation (compose P Q) := by
  rintro (emptyP | emptyQ) x z ⟨y, hxy, hyz⟩
  · exact emptyP x y hxy
  · exact emptyQ y z hyz

/-- ✱34·33. `x ∈ DʻR` iff `x (R | R˘) x`. -/
theorem star_34_33 (R : Relation α β) (x : α) :
    domain R x ↔ compose R (converse R) x x := by
  constructor
  · rintro ⟨y, hxy⟩
    exact ⟨y, hxy, hxy⟩
  · rintro ⟨y, hxy, _⟩
    exact ⟨y, hxy⟩

end PM.Architecture.Star34QProofBlock2
