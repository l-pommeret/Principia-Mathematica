import Principia.Architecture.Star34QProofBlock3

/-! # PM I, ✱34·41–54: eight consecutive relation theorems. -/

namespace PM.Architecture.Star34QProofBlock4

open PM.Architecture.Star34QProofBlock
open PM.Architecture.Star34QProofBlock2

def UniqueValue (R : Relation α β) (x : α) (y : β) : Prop :=
  R x y ∧ ∀ z, R x z → z = y

/-- ✱34·41. Successive unique relational values give the corresponding
unique value of the composite. -/
theorem star_34_41 (P : Relation β γ) (Q : Relation α β)
    (z : α) (c : β) (b : γ) :
    UniqueValue Q z c →
      (∀ y, Q z y → UniqueValue P y b) →
      UniqueValue (compose Q P) z b := by
  rintro ⟨hzc, uniqueQ⟩ valuesP
  constructor
  · exact ⟨c, hzc, (valuesP c hzc).1⟩
  · rintro b' ⟨c', hzc', hc'b'⟩
    have hc' : c' = c := uniqueQ c' hzc'
    subst c'
    exact (valuesP c hzc).2 b' hc'b'

/-- ✱34·42. Pointwise agreement with a composite determines the relation. -/
theorem star_34_42 (R : Relation α γ) (P : Relation α β)
    (Q : Relation β γ) :
    (∀ x z, R x z ↔ compose P Q x z) → R = compose P Q := by
  intro agreement
  funext x z
  exact propext (agreement x z)

/-- ✱34·5. Membership in the relational square. -/
theorem star_34_5 (R : Relation α α) (x y : α) :
    compose R R x y ↔ ∃ z, R x z ∧ R z y := by
  exact Iff.rfl

/-- ✱34·51. Membership in the relational cube. -/
theorem star_34_51 (R : Relation α α) (x y : α) :
    compose (compose R R) R x y ↔
      ∃ z w, R x z ∧ R z w ∧ R w y := by
  constructor
  · rintro ⟨w, ⟨z, hxz, hzw⟩, hwy⟩
    exact ⟨z, w, hxz, hzw, hwy⟩
  · rintro ⟨z, w, hxz, hzw, hwy⟩
    exact ⟨w, ⟨z, hxz, hzw⟩, hwy⟩

/-- ✱34·52. `R³ = R | R²`. -/
theorem star_34_52 (R : Relation α α) :
    compose (compose R R) R = compose R (compose R R) := by
  exact star_34_21 R R R

/-- ✱34·53. The square exists iff the domain and converse domain meet. -/
theorem star_34_53 (R : Relation α α) :
    NonemptyRelation (compose R R) ↔
      ∃ x, domain R x ∧ converseDomain R x := by
  rw [star_34_3]
  constructor
  · rintro ⟨x, hRange, hDomain⟩
    exact ⟨x, hDomain, hRange⟩
  · rintro ⟨x, hDomain, hRange⟩
    exact ⟨x, hRange, hDomain⟩

/-- ✱34·531. Disjoint domain and converse domain characterize an empty
relational square. -/
theorem star_34_531 (R : Relation α α) :
    (∀ x, ¬ (domain R x ∧ converseDomain R x)) ↔
      EmptyRelation (compose R R) := by
  constructor
  · intro disjoint x z
    rintro ⟨y, hxy, hyz⟩
    exact disjoint y ⟨⟨z, hyz⟩, ⟨x, hxy⟩⟩
  · intro empty x
    rintro ⟨⟨z, hxz⟩, ⟨y, hyx⟩⟩
    exact empty y z ⟨x, hyx, hxz⟩

/-- ✱34·54. Every reflexive edge gives a reflexive edge in the square. -/
theorem star_34_54 (R : Relation α α) (x : α) :
    R x x → compose R R x x := by
  intro hxx
  exact ⟨x, hxx, hxx⟩

end PM.Architecture.Star34QProofBlock4
