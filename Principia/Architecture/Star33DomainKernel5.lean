import Principia.Architecture.Star33DomainKernel4

namespace PM.Architecture.Star33DomainKernel5

open PM.Architecture.Star33DomainKernel
open PM.Architecture.Star33DomainKernel2
open PM.Architecture.Star33DomainKernel4

def SectionAtSecond (R : Relation α β) (y : β) : Class α := fun x => R x y
def SectionAtFirst (R : Relation α β) (x : α) : Class β := fun y => R x y
def ExistsClass (a : Class α) : Prop := ∃ x, a x
def UniqueSectionAtSecond (R : Relation α β) (y : β) : Prop :=
  ∃ x, R x y ∧ ∀ z, R z y → z = x
def UniqueSectionAtFirst (R : Relation α β) (x : α) : Prop :=
  ∃ y, R x y ∧ ∀ z, R x z → z = y

private theorem relation_ext {R S : Relation α β}
    (h : ∀ x y, R x y ↔ S x y) : R = S := by
  funext x y
  exact propext (h x y)

/-- PM I ✱33·4. -/
theorem star_33_4 (R : Relation α β) :
    Domain R = (fun x => ExistsClass (SectionAtFirst R x)) := rfl

/-- PM I ✱33·41. -/
theorem star_33_41 (R : Relation α β) :
    ConverseDomain R = (fun y => ExistsClass (SectionAtSecond R y)) := rfl

/-- PM I ✱33·42. -/
theorem star_33_42 (R : Relation α α) :
    Field R = (fun x =>
      ExistsClass (Union (SectionAtSecond R x) (SectionAtFirst R x))) := by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl h => obtain ⟨y, h⟩ := h; exact ⟨y, Or.inr h⟩
    | inr h => obtain ⟨y, h⟩ := h; exact ⟨y, Or.inl h⟩
  · rintro ⟨y, h⟩
    exact h.elim (fun hyx => Or.inr ⟨y, hyx⟩) (fun hxy => Or.inl ⟨y, hxy⟩)

/-- PM I ✱33·43. The contextual value `Rʻy` is retained as its unique
witness instead of being created by choice. -/
theorem star_33_43 (R : Relation α α) (y : α) :
    UniqueSectionAtSecond R y →
      ∃ x, ConverseDomain R y ∧ R x y ∧ Domain R x := by
  rintro ⟨x, hxy, _⟩
  exact ⟨x, ⟨x, hxy⟩, hxy, ⟨y, hxy⟩⟩

/-- PM I ✱33·431. -/
theorem star_33_431 (R : Relation α α) :
    (∀ y, UniqueSectionAtSecond R y) →
      ∀ b : Class α, Included b (ConverseDomain R) := by
  intro h b y _
  obtain ⟨x, hxy, _⟩ := h y
  exact ⟨x, hxy⟩

/-- PM I ✱33·432. -/
theorem star_33_432 (R : Relation α α) :
    (∀ y, UniqueSectionAtSecond R y) →
      ConverseDomain R = UniversalClass := by
  intro h
  funext y
  apply propext
  exact ⟨fun _ => by trivial, fun _ => by
    obtain ⟨x, hxy, _⟩ := h y
    exact ⟨x, hxy⟩⟩

/-- PM I ✱33·44, the converse contextual-value counterpart of ✱33·43. -/
theorem star_33_44 (R : Relation α α) (x : α) :
    UniqueSectionAtFirst R x →
      ∃ y, Domain R x ∧ R x y ∧ ConverseDomain R y := by
  rintro ⟨y, hxy, _⟩
  exact ⟨y, ⟨y, hxy⟩, hxy, ⟨x, hxy⟩⟩

/-- PM I ✱33·45. -/
theorem star_33_45 (R S : Relation α β) :
    (∀ y, (ConverseDomain R y ∨ ConverseDomain S y) →
      SectionAtSecond R y = SectionAtSecond S y) → R = S := by
  intro h
  apply relation_ext
  intro x y
  constructor
  · intro hR
    have hs := congrFun (h y (Or.inl ⟨x, hR⟩)) x
    exact hs.mp hR
  · intro hS
    have hs := congrFun (h y (Or.inr ⟨x, hS⟩)) x
    exact hs.mpr hS

/-- PM I ✱33·46. -/
theorem star_33_46 (R S : Relation α β) :
    (∀ x, (Domain R x ∨ Domain S x) →
      SectionAtFirst R x = SectionAtFirst S x) → R = S := by
  intro h
  apply relation_ext
  intro x y
  constructor
  · intro hR
    exact (congrFun (h x (Or.inl ⟨y, hR⟩)) y).mp hR
  · intro hS
    exact (congrFun (h x (Or.inr ⟨y, hS⟩)) y).mpr hS

/-- PM I ✱33·47. -/
theorem star_33_47 (R S : Relation α β) :
    (∀ y, (ConverseDomain R y ∨ ConverseDomain S y) →
      SectionAtSecond R y = SectionAtSecond S y) → R = S :=
  star_33_45 R S

end PM.Architecture.Star33DomainKernel5
