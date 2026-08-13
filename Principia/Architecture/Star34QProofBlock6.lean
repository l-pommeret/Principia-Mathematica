import Principia.Architecture.Star34QProofBlock5

/-! # PM I, ✱34·703–85: eight consecutive relation theorems. -/

namespace PM.Architecture.Star34QProofBlock6

open PM.Architecture.Star34QProofBlock
open PM.Architecture.Star34QProofBlock2

def Symmetric (R : Relation α α) : Prop := ∀ x y, R x y → R y x
def Transitive (R : Relation α α) : Prop :=
  ∀ x y z, R x y → R y z → R x z

def predecessors (R : Relation α α) (x : α) : α → Prop := fun z => R z x

private theorem square_eq (R : Relation α α) (hs : Symmetric R)
    (ht : Transitive R) : compose R R = R := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ht x y z hxy hyz
  · intro hxz
    exact ⟨x, ht x z x hxz (hs x z hxz), hxz⟩

/-- ✱34·703. The field of `S˘ | S` is the converse domain of `S`. -/
theorem star_34_703 (S : Relation α β) (y : β) :
    field (compose (converse S) S) y ↔ converseDomain S y := by
  constructor
  · rintro (⟨z, x, hxy, _⟩ | ⟨z, x, _, hxy⟩)
    · exact ⟨x, hxy⟩
    · exact ⟨x, hxy⟩
  · rintro ⟨x, hxy⟩
    exact Or.inl ⟨y, x, hxy, hxy⟩

/-- ✱34·8. A symmetric transitive relation equals both its square and its
product with its converse. -/
theorem star_34_8 (R : Relation α α) (hs : Symmetric R) (ht : Transitive R) :
    R = compose R R ∧ compose R R = compose R (converse R) := by
  have hsq : compose R R = R := square_eq R hs ht
  constructor
  · exact hsq.symm
  · rw [hsq]
    funext x y
    apply propext
    constructor
    · intro hxy
      exact ⟨x, ht x y x hxy (hs x y hxy), hs x y hxy⟩
    · rintro ⟨z, hxz, hyz⟩
      exact ht x z y hxz (hs y z hyz)

/-- ✱34·81. Symmetry and transitivity are equivalently symmetry together
with idempotence under relational composition. -/
theorem star_34_81 (R : Relation α α) :
    (Symmetric R ∧ Transitive R) ↔
      (Symmetric R ∧ compose R R = R) := by
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨hs, square_eq R hs ht⟩
  · rintro ⟨hs, hsq⟩
    refine ⟨hs, ?_⟩
    intro x y z hxy hyz
    rw [← hsq]
    exact ⟨y, hxy, hyz⟩

/-- ✱34·82. In a symmetric transitive relation, field membership is
equivalent to self-relatedness. -/
theorem star_34_82 (R : Relation α α) (hs : Symmetric R)
    (ht : Transitive R) (x : α) : domain R x ↔ R x x := by
  constructor
  · rintro ⟨y, hxy⟩
    exact ht x y x hxy (hs x y hxy)
  · intro hxx
    exact ⟨x, hxx⟩

/-- ✱34·83. Related points have the same predecessor class. -/
theorem star_34_83 (R : Relation α α) (hs : Symmetric R)
    (ht : Transitive R) {x y : α} (hxy : R x y) :
    predecessors R x = predecessors R y := by
  funext z
  apply propext
  constructor
  · intro hzx
    exact ht z x y hzx hxy
  · intro hzy
    exact ht z y x hzy (hs x y hxy)

/-- ✱34·84. Equal predecessor classes and membership of the second point
in the domain imply relatedness. -/
theorem star_34_84 (R : Relation α α) (hs : Symmetric R)
    (ht : Transitive R) {x y : α} (hy : domain R y)
    (hclasses : predecessors R x = predecessors R y) : R x y := by
  have hyy : R y y := (star_34_82 R hs ht y).mp hy
  have hyx : R y x := by
    have : predecessors R y y := hyy
    rw [← hclasses] at this
    exact this
  exact hs y x hyx

/-- ✱34·841. Equal predecessor classes and membership of the first point
in the domain imply relatedness. -/
theorem star_34_841 (R : Relation α α) (hs : Symmetric R)
    (ht : Transitive R) {x y : α} (hx : domain R x)
    (hclasses : predecessors R x = predecessors R y) : R x y := by
  have hxx : predecessors R x x := (star_34_82 R hs ht x).mp hx
  rw [hclasses] at hxx
  exact hxx

/-- ✱34·85. Relatedness is equivalent to domain membership together with
equality of predecessor classes. -/
theorem star_34_85 (R : Relation α α) (hs : Symmetric R)
    (ht : Transitive R) (x y : α) :
    R x y ↔ domain R x ∧ predecessors R x = predecessors R y := by
  constructor
  · intro hxy
    exact ⟨⟨y, hxy⟩, star_34_83 R hs ht hxy⟩
  · rintro ⟨hx, hclasses⟩
    exact star_34_841 R hs ht hx hclasses

end PM.Architecture.Star34QProofBlock6
