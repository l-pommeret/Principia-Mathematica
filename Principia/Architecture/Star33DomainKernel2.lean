import Principia.Architecture.Star33DomainKernel

namespace PM.Architecture.Star33DomainKernel2

open PM.Architecture.Star33DomainKernel

def Converse (R : Relation α β) : Relation β α := fun y x => R x y
def Inter (R S : Relation α β) : Relation α β := fun x y => R x y ∧ S x y
def NullClass : Class α := fun _ => False
def NullRelation : Relation α β := fun _ _ => False
def ClassExists (a : Class α) : Prop := ∃ x, a x
def RelationExists (R : Relation α β) : Prop := ∃ x y, R x y

/-- PM I ✱33·17. -/
theorem star_33_17 (R : Relation α α) (x y : α) :
    R x y → Field R x ∧ Field R y := by
  intro h
  exact ⟨Or.inl ⟨y, h⟩, Or.inr ⟨x, h⟩⟩

/-- PM I ✱33·18. -/
theorem star_33_18 (R : Relation α α) :
    Domain R = ConverseDomain R → Domain R = Field R := by
  intro h
  funext x
  apply propext
  constructor
  · intro hd
    exact Or.inl hd
  · intro hf
    cases hf with
    | inl hd => exact hd
    | inr hc =>
        rw [h]
        exact hc

/-- PM I ✱33·181. -/
theorem star_33_181 (R : Relation α α) :
    Included (ConverseDomain R) (Domain R) ↔ Domain R = Field R := by
  constructor
  · intro h
    rw [star_33_16]
    funext x
    exact propext ⟨Or.inl,
      (fun hx => hx.elim (fun hd => hd) (fun hc => h x hc))⟩
  · intro h x hx
    rw [h]
    exact Or.inr hx

/-- PM I ✱33·182. -/
theorem star_33_182 (R : Relation α α) :
    Included (Domain R) (ConverseDomain R) ↔ ConverseDomain R = Field R := by
  constructor
  · intro h
    rw [star_33_16]
    funext x
    exact propext ⟨Or.inr,
      (fun hx => hx.elim (fun hd => h x hd) (fun hc => hc))⟩
  · intro h x hx
    rw [h]
    exact Or.inl hx

/-- PM I ✱33·2. -/
theorem star_33_2 (R : Relation α β) :
    ConverseDomain R = Domain (Converse R) := rfl

/-- PM I ✱33·21. -/
theorem star_33_21 (R : Relation α β) :
    Domain R = ConverseDomain (Converse R) := rfl

/-- PM I ✱33·22. -/
theorem star_33_22 (R : Relation α α) :
    Field R = Field (Converse R) := by
  funext x
  exact propext ⟨
    (fun h => h.elim (fun hx => Or.inr hx) (fun hx => Or.inl hx)),
    (fun h => h.elim (fun hx => Or.inr hx) (fun hx => Or.inl hx))⟩

/-- PM I ✱33·24. -/
theorem star_33_24 (R : Relation α α) :
    (ClassExists (Domain R) ↔ ClassExists (ConverseDomain R)) ∧
    (ClassExists (ConverseDomain R) ↔ ClassExists (Field R)) ∧
    (ClassExists (Field R) ↔ RelationExists R) := by
  constructor
  · exact ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩,
      fun ⟨y, x, h⟩ => ⟨x, y, h⟩⟩
  constructor
  · constructor
    · rintro ⟨y, x, h⟩
      exact ⟨y, Or.inr ⟨x, h⟩⟩
    · rintro ⟨z, h⟩
      cases h with
      | inl h => obtain ⟨y, h⟩ := h; exact ⟨y, z, h⟩
      | inr h => exact ⟨z, h⟩
  · constructor
    · rintro ⟨z, h⟩
      cases h with
      | inl h => obtain ⟨y, h⟩ := h; exact ⟨z, y, h⟩
      | inr h => obtain ⟨x, h⟩ := h; exact ⟨x, z, h⟩
    · rintro ⟨x, y, h⟩
      exact ⟨x, Or.inl ⟨y, h⟩⟩

/-- PM I ✱33·241. -/
theorem star_33_241 (R : Relation α α) :
    (Domain R = NullClass ↔ ConverseDomain R = NullClass) ∧
    (ConverseDomain R = NullClass ↔ Field R = NullClass) ∧
    (Field R = NullClass ↔ R = NullRelation) := by
  have domain_empty : Domain R = NullClass ↔ ∀ x y, ¬ R x y := by
    constructor
    · intro h x y hxy
      exact (congrFun h x).mp ⟨y, hxy⟩
    · intro h
      funext x; apply propext
      exact ⟨fun ⟨y, hxy⟩ => h x y hxy, False.elim⟩
  have converse_empty : ConverseDomain R = NullClass ↔ ∀ x y, ¬ R x y := by
    constructor
    · intro h x y hxy
      exact (congrFun h y).mp ⟨x, hxy⟩
    · intro h
      funext y; apply propext
      exact ⟨fun ⟨x, hxy⟩ => h x y hxy, False.elim⟩
  have field_empty : Field R = NullClass ↔ ∀ x y, ¬ R x y := by
    constructor
    · intro h x y hxy
      exact (congrFun h x).mp (Or.inl ⟨y, hxy⟩)
    · intro h
      funext x; apply propext
      exact ⟨fun hx => hx.elim (fun ⟨y, hxy⟩ => h x y hxy)
        (fun ⟨y, hyx⟩ => h y x hyx), False.elim⟩
  have relation_empty : R = NullRelation ↔ ∀ x y, ¬ R x y := by
    constructor
    · intro h x y hxy
      exact (congrFun (congrFun h x) y).mp hxy
    · intro h
      funext x y; apply propext
      exact ⟨h x y, False.elim⟩
  exact ⟨domain_empty.trans converse_empty.symm,
    converse_empty.trans field_empty.symm,
    field_empty.trans relation_empty.symm⟩

/-- PM I ✱33·25. -/
theorem star_33_25 (R S : Relation α β) :
    Included (Domain (Inter R S))
      (fun x => Domain R x ∧ Domain S x) := by
  rintro x ⟨y, hR, hS⟩
  exact ⟨⟨y, hR⟩, ⟨y, hS⟩⟩

/-- PM I ✱33·251. -/
theorem star_33_251 (R S : Relation α β) :
    Included (ConverseDomain (Inter R S))
      (fun y => ConverseDomain R y ∧ ConverseDomain S y) := by
  rintro y ⟨x, hR, hS⟩
  exact ⟨⟨x, hR⟩, ⟨x, hS⟩⟩

/-- PM I ✱33·252. -/
theorem star_33_252 (R S : Relation α α) :
    Included (Field (Inter R S)) (fun x => Field R x ∧ Field S x) := by
  intro x h
  cases h with
  | inl h =>
      obtain ⟨y, hR, hS⟩ := h
      exact ⟨Or.inl ⟨y, hR⟩, Or.inl ⟨y, hS⟩⟩
  | inr h =>
      obtain ⟨y, hR, hS⟩ := h
      exact ⟨Or.inr ⟨y, hR⟩, Or.inr ⟨y, hS⟩⟩

end PM.Architecture.Star33DomainKernel2
