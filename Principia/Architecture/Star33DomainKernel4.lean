import Principia.Architecture.Star33DomainKernel3

namespace PM.Architecture.Star33DomainKernel4

open PM.Architecture.Star33DomainKernel
open PM.Architecture.Star33DomainKernel2

def UniversalClass : Class α := fun _ => True
def UniversalRelation : Relation α β := fun _ _ => True

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x
  exact propext (h x)

/-- PM I ✱33·28. Possible arguments of both relation places are explicitly
nonempty, as required for the universal relation to have universal domains. -/
theorem star_33_28 [Nonempty α] [Nonempty β] :
    Domain (UniversalRelation : Relation α β) = UniversalClass ∧
    ConverseDomain (UniversalRelation : Relation α β) = UniversalClass := by
  constructor
  · apply class_ext
    intro x
    exact ⟨fun _ => True.intro, fun _ => ⟨Classical.choice inferInstance, True.intro⟩⟩
  · apply class_ext
    intro y
    exact ⟨fun _ => True.intro, fun _ => ⟨Classical.choice inferInstance, True.intro⟩⟩

/-- PM I ✱33·29, represented by the three adjacent equalities in the printed
domain/converse-domain/field/null-relation chain. -/
theorem star_33_29 :
    Domain (NullRelation : Relation α α) = NullClass ∧
    ConverseDomain (NullRelation : Relation α α) = NullClass ∧
    Field (NullRelation : Relation α α) = NullClass := by
  constructor
  · apply class_ext
    intro x
    exact ⟨fun ⟨_, h⟩ => h, False.elim⟩
  constructor
  · apply class_ext
    intro x
    exact ⟨fun ⟨_, h⟩ => h, False.elim⟩
  · apply class_ext
    intro x
    exact ⟨fun h => h.elim (fun ⟨_, h⟩ => h) (fun ⟨_, h⟩ => h), False.elim⟩

/-- PM I ✱33·3. -/
theorem star_33_3 (a : Class α) (R : Relation α β) :
    Included a (Domain R) ↔ ∀ x, a x → ∃ y, R x y := Iff.rfl

/-- PM I ✱33·31. -/
theorem star_33_31 (b : Class β) (R : Relation α β) :
    Included b (ConverseDomain R) ↔ ∀ y, b y → ∃ x, R x y := Iff.rfl

/-- PM I ✱33·32. -/
theorem star_33_32 (R S : Relation α β) :
    (fun x => Domain R x ∧ Domain S x) = NullClass →
      Inter R S = NullRelation := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨hR, hS⟩
    exact (congrFun h x).mp ⟨⟨y, hR⟩, ⟨y, hS⟩⟩
  · exact False.elim

/-- PM I ✱33·33. -/
theorem star_33_33 (R S : Relation α β) :
    (fun y => ConverseDomain R y ∧ ConverseDomain S y) = NullClass →
      Inter R S = NullRelation := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨hR, hS⟩
    exact (congrFun h y).mp ⟨⟨x, hR⟩, ⟨x, hS⟩⟩
  · exact False.elim

/-- PM I ✱33·34. -/
theorem star_33_34 (R S : Relation α α) :
    (fun x => Field R x ∧ Field S x) = NullClass →
      Inter R S = NullRelation := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨hR, hS⟩
    exact (congrFun h x).mp ⟨Or.inl ⟨y, hR⟩, Or.inl ⟨y, hS⟩⟩
  · exact False.elim

/-- PM I ✱33·35. -/
theorem star_33_35 (R : Relation α β) (a : Class α) :
    Included (Domain R) a ↔ ∀ x y, R x y → a x := by
  constructor
  · intro h x y hR
    exact h x ⟨y, hR⟩
  · rintro h x ⟨y, hR⟩
    exact h x y hR

/-- PM I ✱33·351. -/
theorem star_33_351 (R : Relation α β) (b : Class β) :
    Included (ConverseDomain R) b ↔ ∀ x y, R x y → b y := by
  constructor
  · intro h x y hR
    exact h y ⟨x, hR⟩
  · rintro h y ⟨x, hR⟩
    exact h x y hR

/-- PM I ✱33·352. -/
theorem star_33_352 (R : Relation α α) (a : Class α) :
    Included (Field R) a ↔ ∀ x y, R x y → a x ∧ a y := by
  constructor
  · intro h x y hR
    exact ⟨h x (Or.inl ⟨y, hR⟩), h y (Or.inr ⟨x, hR⟩)⟩
  · intro h x hx
    cases hx with
    | inl hx => obtain ⟨y, hR⟩ := hx; exact (h x y hR).1
    | inr hx => obtain ⟨y, hR⟩ := hx; exact (h y x hR).2

end PM.Architecture.Star33DomainKernel4
