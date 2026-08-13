/-! PM I ✱41·24–33: eight consecutive relation-class propositions. -/

namespace PM.Architecture.Star41ConverseKernel

abbrev Relation (α : Sort _) (β : Sort _) := α → β → Prop
abbrev RelationClass (α : Sort _) (β : Sort _) := Relation α β → Prop
abbrev RelationClassClass (α : Sort _) (β : Sort _) :=
  RelationClass α β → Prop

def subrel (R S : Relation α β) : Prop := ∀ x y, R x y → S x y
def product (collection : RelationClass α β) : Relation α β :=
  fun x y => ∀ R, collection R → R x y
def sum (collection : RelationClass α β) : Relation α β :=
  fun x y => ∃ R, collection R ∧ R x y
def relInter (R S : Relation α β) : Relation α β :=
  fun x y => R x y ∧ S x y
def emptyRelation : Relation α β := fun _ _ => False
def converse (R : Relation α β) : Relation β α := fun y x => R x y
def hasMember (R : Relation α β) : Prop := ∃ x y, R x y
def containsPair (x : α) (y : β) : RelationClass α β := fun R => R x y
def classInter (collection larger : RelationClass α β) : RelationClass α β :=
  fun R => collection R ∧ larger R

def mapRelations (collection : RelationClass α β) : RelationClass β α :=
  fun S => ∃ R, collection R ∧ S = converse R
def productValues (families : RelationClassClass α β) : RelationClass α β :=
  fun R => ∃ collection, families collection ∧ R = product collection
def sumValues (families : RelationClassClass α β) : RelationClass α β :=
  fun R => ∃ collection, families collection ∧ R = sum collection
def mapFamilies (families : RelationClassClass α β) : RelationClassClass β α :=
  fun transformed => ∃ collection, families collection ∧
    transformed = mapRelations collection

/-- ✱41·24. A lower bound of a nonempty relation class lies below its sum. -/
theorem star_41_24 (collection : RelationClass α β) (S : Relation α β) :
    (∃ R, collection R) →
      (∀ R, collection R → subrel S R) → subrel S (sum collection) := by
  rintro ⟨R, hR⟩ h x y hxy
  exact ⟨R, hR, h R hR x y hxy⟩

/-- ✱41·25. A pair belongs to the sum exactly when the class of relations
containing that pair meets the original relation class. -/
theorem star_41_25 (collection : RelationClass α β) (x : α) (y : β) :
    sum collection x y ↔
      ∃ R, classInter collection (containsPair x y) R := by
  rfl

/-- ✱41·26. The relational sum has a member exactly when some member relation
of the class has a member. -/
theorem star_41_26 (collection : RelationClass α β) :
    hasMember (sum collection) ↔
      ∃ R, collection R ∧ hasMember R := by
  constructor
  · rintro ⟨x, y, R, hR, hxy⟩
    exact ⟨R, hR, x, y, hxy⟩
  · rintro ⟨R, hR, x, y, hxy⟩
    exact ⟨x, y, R, hR, hxy⟩

/-- ✱41·27. A relation is disjoint from a sum exactly when it is disjoint
from every member of the relation class. -/
theorem star_41_27 (P : Relation α β) (collection : RelationClass α β) :
    relInter P (sum collection) = emptyRelation ↔
      ∀ R, collection R → relInter P R = emptyRelation := by
  constructor
  · intro h R hR
    funext x y
    apply propext
    constructor
    · intro hxy
      have hs : sum collection x y := ⟨R, hR, hxy.2⟩
      exact congrFun (congrFun h x) y ▸ ⟨hxy.1, hs⟩
    · exact False.elim
  · intro h
    funext x y
    apply propext
    constructor
    · rintro ⟨hP, R, hR, hxy⟩
      have hempty : relInter P R x y := ⟨hP, hxy⟩
      exact congrFun (congrFun (h R hR) x) y ▸ hempty
    · exact False.elim

/-- ✱41·3. Converse commutes with relational product after mapping every
member relation to its converse. -/
theorem star_41_3 (collection : RelationClass α β) :
    converse (product collection) = product (mapRelations collection) := by
  funext y x
  apply propext
  constructor
  · intro h S
    rintro ⟨R, hR, rfl⟩
    exact h R hR
  · intro h R hR
    exact h (converse R) ⟨R, hR, rfl⟩

/-- ✱41·31. Converse commutes with relational sum. -/
theorem star_41_31 (collection : RelationClass α β) :
    converse (sum collection) = sum (mapRelations collection) := by
  funext y x
  apply propext
  constructor
  · rintro ⟨R, hR, hxy⟩
    exact ⟨converse R, ⟨R, hR, rfl⟩, hxy⟩
  · rintro ⟨S, ⟨R, hR, rfl⟩, hxy⟩
    exact ⟨R, hR, hxy⟩

/-- ✱41·32. Mapping converse over all product values equals taking all
products after mapping converse over the underlying families. -/
theorem star_41_32 (families : RelationClassClass α β) :
    mapRelations (productValues families) =
      productValues (mapFamilies families) := by
  funext S
  apply propext
  constructor
  · rintro ⟨R, ⟨collection, hc, rfl⟩, rfl⟩
    exact ⟨mapRelations collection, ⟨collection, hc, rfl⟩,
      star_41_3 collection⟩
  · rintro ⟨mapped, ⟨collection, hc, rfl⟩, rfl⟩
    exact ⟨product collection, ⟨collection, hc, rfl⟩,
      (star_41_3 collection).symm⟩

/-- ✱41·33. The corresponding mapping law for relational sums. -/
theorem star_41_33 (families : RelationClassClass α β) :
    mapRelations (sumValues families) =
      sumValues (mapFamilies families) := by
  funext S
  apply propext
  constructor
  · rintro ⟨R, ⟨collection, hc, rfl⟩, rfl⟩
    exact ⟨mapRelations collection, ⟨collection, hc, rfl⟩,
      star_41_31 collection⟩
  · rintro ⟨mapped, ⟨collection, hc, rfl⟩, rfl⟩
    exact ⟨sum collection, ⟨collection, hc, rfl⟩,
      (star_41_31 collection).symm⟩

end PM.Architecture.Star41ConverseKernel
