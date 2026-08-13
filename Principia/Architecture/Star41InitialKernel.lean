/-!
# PM I ✱41·1–161

The first ten consecutive derived propositions of ✱41. Relations and classes
of relations retain both object carriers explicitly.
-/

namespace PM.Architecture.Star41InitialKernel

abbrev Relation (α : Sort _) (β : Sort _) := α → β → Prop
abbrev RelationClass (α : Sort _) (β : Sort _) := Relation α β → Prop

def subrel (R S : Relation α β) : Prop := ∀ x y, R x y → S x y
def relationalProduct (collection : RelationClass α β) : Relation α β :=
  fun x y => ∀ R, collection R → R x y
def sum (collection : RelationClass α β) : Relation α β :=
  fun x y => ∃ R, collection R ∧ R x y
def subclass (collection larger : RelationClass α β) : Prop :=
  ∀ R, collection R → larger R

/-- ✱41·01. Canonical wrapper for relational product. -/
theorem star_41_01 (collection : RelationClass α β) :
    relationalProduct collection = fun x y => ∀ R, collection R → R x y := rfl

/-- ✱41·02. Canonical wrapper for relational sum. -/
theorem star_41_02 (collection : RelationClass α β) :
    sum collection = fun x y => ∃ R, collection R ∧ R x y := rfl

/-- ✱41·1. Membership in the relational product. -/
theorem star_41_1 (collection : RelationClass α β) (x : α) (y : β) :
    relationalProduct collection x y ↔ ∀ R, collection R → R x y := by
  rfl

/-- ✱41·11. Membership in the relational sum. -/
theorem star_41_11 (collection : RelationClass α β) (x : α) (y : β) :
    sum collection x y ↔ ∃ R, collection R ∧ R x y := by
  rfl

/-- ✱41·12. The product of a relation class is contained in every member. -/
theorem star_41_12 (collection : RelationClass α β) (R : Relation α β) :
    collection R → subrel (relationalProduct collection) R := by
  exact fun hR x y h => h R hR

/-- ✱41·13. Every member is contained in the sum of its relation class. -/
theorem star_41_13 (collection : RelationClass α β) (R : Relation α β) :
    collection R → subrel R (sum collection) := by
  exact fun hR x y hxy => ⟨R, hR, hxy⟩

/-- ✱41·14. Pointwise detachment from product membership. -/
theorem star_41_14 (collection : RelationClass α β) (R : Relation α β)
    (x : α) (y : β) :
    collection R ∧ relationalProduct collection x y → R x y := by
  exact fun h => h.2 R h.1

/-- ✱41·141. Pointwise introduction into sum membership. -/
theorem star_41_141 (collection : RelationClass α β) (R : Relation α β)
    (x : α) (y : β) :
    collection R ∧ R x y → sum collection x y := by
  exact fun h => ⟨R, h.1, h.2⟩

/-- ✱41·15. A relation lies below the product exactly when it lies below
every member of the class. -/
theorem star_41_15 (collection : RelationClass α β) (S : Relation α β) :
    subrel S (relationalProduct collection) ↔ ∀ R, collection R → subrel S R := by
  constructor
  · exact fun h R hR x y hxy => h x y hxy R hR
  · exact fun h x y hxy R hR => h R hR x y hxy

/-- ✱41·151. The sum lies below a relation exactly when every member does. -/
theorem star_41_151 (collection : RelationClass α β) (S : Relation α β) :
    subrel (sum collection) S ↔ ∀ R, collection R → subrel R S := by
  constructor
  · exact fun h R hR x y hxy => h x y ⟨R, hR, hxy⟩
  · rintro h x y ⟨R, hR, hxy⟩
    exact h R hR x y hxy

/-- ✱41·16. Product is antitone in its relation-class argument. -/
theorem star_41_16 (collection larger : RelationClass α β) :
    subclass collection larger → subrel (relationalProduct larger) (relationalProduct collection) := by
  exact fun h R_x R_y hprod R hR => hprod R (h R hR)

/-- ✱41·161. Sum is monotone in its relation-class argument. -/
theorem star_41_161 (collection larger : RelationClass α β) :
    subclass collection larger → subrel (sum collection) (sum larger) := by
  rintro h x y ⟨R, hR, hxy⟩
  exact ⟨R, h R hR, hxy⟩

end PM.Architecture.Star41InitialKernel
