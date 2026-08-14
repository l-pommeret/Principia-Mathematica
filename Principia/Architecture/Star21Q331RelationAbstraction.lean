/-!
# PM I ✱21·082, ✱21·083, and ✱21·1

Typed binary relations and classes of such relations are represented by their
membership predicates. The two definition-in-use expansions remain explicit;
no global relation-class choice object is introduced.
-/

namespace PM.Architecture.Star21Q331RelationAbstraction

abbrev TypedRelation (α : Sort _) (β : Sort _) := α → β → Prop
abbrev RelationClass (α : Sort _) (β : Sort _) :=
  TypedRelation α β → Prop

/-- Relation-class abstraction: `φ!ẑR`. -/
def AbstractRelationClass
    (φ : TypedRelation α β → Prop) : RelationClass α β := φ

/-- The definition-in-use on the left of ✱21·082. -/
def RelationClassApplication
    (f : RelationClass α β → Prop) (ψ : TypedRelation α β → Prop) : Prop :=
  ∃ φ : TypedRelation α β → Prop,
    (∀ R, ψ R ↔ φ R) ∧ f (AbstractRelationClass φ)

/-- ✱21·082. `f{ẑR(ψR)} .=: (∃φ) : ψR .≡ᴿ. φ!R : f(φ!ẑR) Df`. -/
def star_21_082
    (f : RelationClass α β → Prop) (ψ : TypedRelation α β → Prop) :
    Prop :=
  ∃ φ : TypedRelation α β → Prop,
    (∀ R, ψ R ↔ φ R) ∧ f (AbstractRelationClass φ)

/-- ✱21·083. `R ε φ!ẑR .= . φ!R Df`. -/
def star_21_083
    (R : TypedRelation α β) (φ : TypedRelation α β → Prop) :
    Prop := φ R

/-- The ✱21·01 relation-abstraction definition used by ✱21·1. -/
def RelationAbstractionApplication
    (f : TypedRelation α β → Prop) (ψ : α → β → Prop) : Prop :=
  ∃ φ : α → β → Prop, (∀ x y, φ x y ↔ ψ x y) ∧ f φ

/-- ✱21·1. The displayed relation abstraction is equivalent to the complete
existential predicative-function expansion of ✱21·01. -/
theorem star_21_1
    (f : TypedRelation α β → Prop) (ψ : α → β → Prop) :
    RelationAbstractionApplication f ψ ↔
      ∃ φ : α → β → Prop, (∀ x y, φ x y ↔ ψ x y) ∧ f φ := by
  rfl

end PM.Architecture.Star21Q331RelationAbstraction
