import Principia.Architecture.Star33DomainKernel5

namespace PM.Architecture.Star33DomainKernel6

open PM.Architecture.Star33DomainKernel
open PM.Architecture.Star33DomainKernel2
open PM.Architecture.Star33DomainKernel4
open PM.Architecture.Star33DomainKernel5

/-- The PM relation `F` between an object and a homogeneous relation. -/
def FieldRelation (x : α) (R : Relation α α) : Prop := Field R x

/-- The class-valued function `C` sending a relation to its field. -/
def FieldOperator (R : Relation α α) : Class α := Field R

/-- Converse fibres of the three class-valued operators D, ᗡ, and C. -/
def InverseDomainFiber (a : Class α) (R : Relation α β) : Prop :=
  a = Domain R
def InverseConverseDomainFiber (b : Class β) (R : Relation α β) : Prop :=
  b = ConverseDomain R
def InverseFieldFiber (a : Class α) (R : Relation α α) : Prop :=
  a = Field R

private theorem relation_ext {R S : Relation α β}
    (h : ∀ x y, R x y ↔ S x y) : R = S := by
  funext x y
  exact propext (h x y)

/-- PM I ✱33·48. -/
theorem star_33_48 (R S : Relation α β) :
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

/-- PM I ✱33·5: `C = F→`, extensionally at each relation argument. -/
theorem star_33_5 :
    (FieldOperator : Relation α α → Class α) =
      (fun R x => FieldRelation x R) := rfl

/-- PM I ✱33·51. -/
theorem star_33_51 (R : Relation α α) (x : α) :
    Field R x ↔ FieldRelation x R := Iff.rfl

/-- PM I ✱33·6. -/
theorem star_33_6 (a : Class α) (R : Relation α β) :
    InverseDomainFiber a R ↔ a = Domain R := Iff.rfl

/-- PM I ✱33·61. The Gutenberg transcription drops the repeated `= α` on
the right; this is the exact converse-domain analogue of ✱33·6. -/
theorem star_33_61 (b : Class β) (R : Relation α β) :
    InverseConverseDomainFiber b R ↔ b = ConverseDomain R := Iff.rfl

/-- PM I ✱33·62. The exact field analogue of ✱33·6. -/
theorem star_33_62 (a : Class α) (R : Relation α α) :
    InverseFieldFiber a R ↔ a = Field R := Iff.rfl

end PM.Architecture.Star33DomainKernel6
