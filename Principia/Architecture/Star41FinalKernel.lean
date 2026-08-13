/-! PM I ✱41·43–6: the final seven propositions of ✱41. -/

namespace PM.Architecture.Star41FinalKernel

abbrev Class (α : Sort _) := α → Prop
abbrev Relation (α : Sort _) (β : Sort _) := α → β → Prop
abbrev RelationClass (α : Sort _) (β : Sort _) := Relation α β → Prop

def subrel (R S : Relation α β) : Prop := ∀ x y, R x y → S x y
def sumRelations (collection : RelationClass α β) : Relation α β :=
  fun x y => ∃ R, collection R ∧ R x y
def productRelations (collection : RelationClass α β) : Relation α β :=
  fun x y => ∀ R, collection R → R x y
def sumClasses (collection : Class (Class α)) : Class α :=
  fun x => ∃ a, collection a ∧ a x
def domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def range (R : Relation α β) : Class β := fun y => ∃ x, R x y
def field (R : Relation α α) : Class α :=
  fun x => domain R x ∨ range R x
def domainValues (collection : RelationClass α β) : Class (Class α) :=
  fun a => ∃ R, collection R ∧ a = domain R
def rangeValues (collection : RelationClass α β) : Class (Class β) :=
  fun a => ∃ R, collection R ∧ a = range R
def fieldValues (collection : RelationClass α α) : Class (Class α) :=
  fun a => ∃ R, collection R ∧ a = field R
def leftRestrict (a : Class α) (R : Relation α β) : Relation α β :=
  fun x y => a x ∧ R x y
def relUnion (R S : Relation α β) : Relation α β :=
  fun x y => R x y ∨ S x y
def compose (R : Relation α β) (S : Relation β γ) : Relation α γ :=
  fun x z => ∃ y, R x y ∧ S y z
def compositionValues (left : RelationClass α β)
    (right : RelationClass β γ) : RelationClass α γ :=
  fun T => ∃ R S, left R ∧ right S ∧ T = compose R S
def sumOver (indices : Class ι) (family : ι → Relation α β) : Relation α β :=
  fun x y => ∃ i, indices i ∧ family i x y

/-- ✱41·43. The domain of a relational sum is the class sum of the domains
of its member relations. -/
theorem star_41_43 (collection : RelationClass α β) :
    domain (sumRelations collection) = sumClasses (domainValues collection) := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, R, hR, hxy⟩
    exact ⟨domain R, ⟨R, hR, rfl⟩, y, hxy⟩
  · rintro ⟨_, ⟨R, hR, rfl⟩, y, hxy⟩
    exact ⟨y, R, hR, hxy⟩

/-- ✱41·44. The converse-domain of a relational sum is the class sum of the
converse-domains of its member relations. -/
theorem star_41_44 (collection : RelationClass α β) :
    range (sumRelations collection) = sumClasses (rangeValues collection) := by
  funext y
  apply propext
  constructor
  · rintro ⟨x, R, hR, hxy⟩
    exact ⟨range R, ⟨R, hR, rfl⟩, x, hxy⟩
  · rintro ⟨_, ⟨R, hR, rfl⟩, x, hxy⟩
    exact ⟨x, R, hR, hxy⟩

/-- ✱41·45. The field of a relational sum is the class sum of the fields of
its member relations. -/
theorem star_41_45 (collection : RelationClass α α) :
    field (sumRelations collection) = sumClasses (fieldValues collection) := by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl h =>
        obtain ⟨y, R, hR, hxy⟩ := h
        exact ⟨field R, ⟨R, hR, rfl⟩, Or.inl ⟨y, hxy⟩⟩
    | inr h =>
        obtain ⟨y, R, hR, hyx⟩ := h
        exact ⟨field R, ⟨R, hR, rfl⟩, Or.inr ⟨y, hyx⟩⟩
  · rintro ⟨_, ⟨R, hR, rfl⟩, hx⟩
    exact hx.elim
      (fun ⟨y, hxy⟩ => Or.inl ⟨y, R, hR, hxy⟩)
      (fun ⟨y, hyx⟩ => Or.inr ⟨y, R, hR, hyx⟩)

/-- ✱41·5. The relative product of two relational products lies below the
product of all pairwise relative products. -/
theorem star_41_5 (left : RelationClass α β) (right : RelationClass β γ) :
    subrel (compose (productRelations left) (productRelations right))
      (productRelations (compositionValues left right)) := by
  rintro x z ⟨y, hleft, hright⟩ T
  rintro ⟨R, S, hR, hS, rfl⟩
  exact ⟨y, hleft R hR, hright S hS⟩

/-- ✱41·51. The relative product of two relational sums is exactly the sum
of all pairwise relative products. -/
theorem star_41_51 (left : RelationClass α β) (right : RelationClass β γ) :
    compose (sumRelations left) (sumRelations right) =
      sumRelations (compositionValues left right) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨R, hR, hxy⟩, S, hS, hyz⟩
    exact ⟨compose R S, ⟨R, S, hR, hS, rfl⟩, y, hxy, hyz⟩
  · rintro ⟨_, ⟨R, S, hR, hS, rfl⟩, y, hxy, hyz⟩
    exact ⟨y, ⟨R, hR, hxy⟩, ⟨S, hS, hyz⟩⟩

/-- ✱41·52. A left restriction of a relational sum lies below `Q` exactly
when every correspondingly restricted member relation does. -/
theorem star_41_52 (a : Class α) (collection : RelationClass α β)
    (Q : Relation α β) :
    subrel (leftRestrict a (sumRelations collection)) Q ↔
      ∀ P, collection P → subrel (leftRestrict a P) Q := by
  constructor
  · exact fun h P hP x y hxy => h x y ⟨hxy.1, P, hP, hxy.2⟩
  · rintro h x y ⟨ha, P, hP, hxy⟩
    exact h P hP x y ⟨ha, hxy⟩

/-- ✱41·6. Pointwise binary union of an indexed family commutes with its
relational sum over the indicated class of indices. -/
theorem star_41_6 (indices : Class ι)
    (P Q R : ι → Relation α β)
    (h : ∀ i, indices i → P i = relUnion (Q i) (R i)) :
    sumOver indices P = relUnion (sumOver indices Q) (sumOver indices R) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨i, hi, hP⟩
    rw [h i hi] at hP
    exact hP.elim
      (fun hQ => Or.inl ⟨i, hi, hQ⟩)
      (fun hR => Or.inr ⟨i, hi, hR⟩)
  · intro hs
    rcases hs with ⟨i, hi, hQ⟩ | ⟨i, hi, hR⟩
    · exact ⟨i, hi, (congrFun (congrFun (h i hi) x) y).mpr (Or.inl hQ)⟩
    · exact ⟨i, hi, (congrFun (congrFun (h i hi) x) y).mpr (Or.inr hR)⟩

end PM.Architecture.Star41FinalKernel
