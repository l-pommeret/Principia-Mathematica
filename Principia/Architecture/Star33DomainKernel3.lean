import Principia.Architecture.Star33DomainKernel2

namespace PM.Architecture.Star33DomainKernel3

open PM.Architecture.Star33DomainKernel
open PM.Architecture.Star33DomainKernel2

def RelUnion (R S : Relation α β) : Relation α β := fun x y => R x y ∨ S x y
def RelIncluded (R S : Relation α β) : Prop := ∀ x y, R x y → S x y

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x
  exact propext (h x)

/-- PM I ✱33·26. -/
theorem star_33_26 (R S : Relation α β) :
    Domain (RelUnion R S) = Union (Domain R) (Domain S) := by
  apply class_ext
  intro x
  constructor
  · rintro ⟨y, h⟩
    exact h.elim (fun hR => Or.inl ⟨y, hR⟩) (fun hS => Or.inr ⟨y, hS⟩)
  · rintro (⟨y, hR⟩ | ⟨y, hS⟩)
    · exact ⟨y, Or.inl hR⟩
    · exact ⟨y, Or.inr hS⟩

/-- PM I ✱33·261. -/
theorem star_33_261 (R S : Relation α β) :
    ConverseDomain (RelUnion R S) =
      Union (ConverseDomain R) (ConverseDomain S) := by
  apply class_ext
  intro y
  constructor
  · rintro ⟨x, h⟩
    exact h.elim (fun hR => Or.inl ⟨x, hR⟩) (fun hS => Or.inr ⟨x, hS⟩)
  · rintro (⟨x, hR⟩ | ⟨x, hS⟩)
    · exact ⟨x, Or.inl hR⟩
    · exact ⟨x, Or.inr hS⟩

/-- PM I ✱33·262. -/
theorem star_33_262 (R S : Relation α α) :
    Field (RelUnion R S) = Union (Field R) (Field S) := by
  apply class_ext
  intro x
  constructor
  · intro h
    cases h with
    | inl h =>
        obtain ⟨y, h⟩ := h
        exact h.elim (fun hR => Or.inl (Or.inl ⟨y, hR⟩))
          (fun hS => Or.inr (Or.inl ⟨y, hS⟩))
    | inr h =>
        obtain ⟨y, h⟩ := h
        exact h.elim (fun hR => Or.inl (Or.inr ⟨y, hR⟩))
          (fun hS => Or.inr (Or.inr ⟨y, hS⟩))
  · intro h
    cases h with
    | inl h =>
        exact h.elim (fun ⟨y, hR⟩ => Or.inl ⟨y, Or.inl hR⟩)
          (fun ⟨y, hR⟩ => Or.inr ⟨y, Or.inl hR⟩)
    | inr h =>
        exact h.elim (fun ⟨y, hS⟩ => Or.inl ⟨y, Or.inr hS⟩)
          (fun ⟨y, hS⟩ => Or.inr ⟨y, Or.inr hS⟩)

/-- PM I ✱33·263. -/
theorem star_33_263 (R S : Relation α β) :
    RelIncluded R S → Included (Domain R) (Domain S) := by
  rintro h x ⟨y, hR⟩
  exact ⟨y, h x y hR⟩

/-- PM I ✱33·264. -/
theorem star_33_264 (R S : Relation α β) :
    RelIncluded R S → Included (ConverseDomain R) (ConverseDomain S) := by
  rintro h y ⟨x, hR⟩
  exact ⟨x, h x y hR⟩

/-- PM I ✱33·265. -/
theorem star_33_265 (R S : Relation α α) :
    RelIncluded R S → Included (Field R) (Field S) := by
  intro h x hx
  cases hx with
  | inl hx => obtain ⟨y, hR⟩ := hx; exact Or.inl ⟨y, h x y hR⟩
  | inr hx => obtain ⟨y, hR⟩ := hx; exact Or.inr ⟨y, h y x hR⟩

/-- PM I ✱33·27. -/
theorem star_33_27 (R : Relation α α) :
    Field R = Domain (RelUnion R (Converse R)) := by
  apply class_ext
  intro x
  constructor
  · intro h
    cases h with
    | inl h => obtain ⟨y, h⟩ := h; exact ⟨y, Or.inl h⟩
    | inr h => obtain ⟨y, h⟩ := h; exact ⟨y, Or.inr h⟩
  · rintro ⟨y, h⟩
    exact h.elim (fun hR => Or.inl ⟨y, hR⟩) (fun hR => Or.inr ⟨y, hR⟩)

/-- PM I ✱33·271. -/
theorem star_33_271 (R : Relation α α) :
    Field R = ConverseDomain (RelUnion R (Converse R)) := by
  apply class_ext
  intro x
  constructor
  · intro h
    cases h with
    | inl h => obtain ⟨y, h⟩ := h; exact ⟨y, Or.inr h⟩
    | inr h => obtain ⟨y, h⟩ := h; exact ⟨y, Or.inl h⟩
  · rintro ⟨y, h⟩
    exact h.elim (fun hR => Or.inr ⟨y, hR⟩) (fun hR => Or.inl ⟨y, hR⟩)

/-- PM I ✱33·272, represented as the three adjacent equalities in its
printed equality chain. -/
theorem star_33_272 (R : Relation α α) :
    Domain (RelUnion R (Converse R)) = ConverseDomain (RelUnion R (Converse R)) ∧
    ConverseDomain (RelUnion R (Converse R)) = Field (RelUnion R (Converse R)) ∧
    Field (RelUnion R (Converse R)) = Field R := by
  have hD : Domain (RelUnion R (Converse R)) = Field R := (star_33_27 R).symm
  have hC : ConverseDomain (RelUnion R (Converse R)) = Field R := (star_33_271 R).symm
  have hF : Field (RelUnion R (Converse R)) = Field R := by
    rw [star_33_262, star_33_22]
    apply class_ext
    intro x
    exact ⟨fun h => h.elim id id, Or.inl⟩
  exact ⟨hD.trans hC.symm, hC.trans hF.symm, hF⟩

end PM.Architecture.Star33DomainKernel3
