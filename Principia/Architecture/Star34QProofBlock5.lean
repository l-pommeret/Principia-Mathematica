import Principia.Architecture.Star34QProofBlock4

/-! # PM I, ✱34·55–702: eight consecutive relation theorems. -/

namespace PM.Architecture.Star34QProofBlock5

open PM.Architecture.Star34QProofBlock
open PM.Architecture.Star34QProofBlock2

/-- ✱34·55. Inclusion of the square is exactly the displayed three-variable
closure condition. -/
theorem star_34_55 (R S : Relation α α) :
    included (compose R R) S ↔
      ∀ x y z, R x y → R y z → S x z := by
  constructor
  · intro h x y z hxy hyz
    exact h x z ⟨y, hxy, hyz⟩
  · intro h x z
    rintro ⟨y, hxy, hyz⟩
    exact h x y z hxy hyz

/-- ✱34·56. Domain, converse domain, and field of the square are contained
in those of the original relation. -/
theorem star_34_56 (R : Relation α α) :
    (∀ x, domain (compose R R) x → domain R x) ∧
    (∀ x, converseDomain (compose R R) x → converseDomain R x) ∧
    (∀ x, field (compose R R) x → field R x) := by
  constructor
  · rintro x ⟨z, y, hxy, _⟩
    exact ⟨y, hxy⟩
  constructor
  · rintro x ⟨z, y, _, hyx⟩
    exact ⟨y, hyx⟩
  · intro x
    rintro (⟨z, y, hxy, _⟩ | ⟨z, y, _, hyx⟩)
    · exact Or.inl ⟨y, hxy⟩
    · exact Or.inr ⟨y, hyx⟩

/-- ✱34·6. The square of an intersection is included in the intersection
of the squares. -/
theorem star_34_6 (R S : Relation α α) :
    included (compose (intersection R S) (intersection R S))
      (intersection (compose R R) (compose S S)) := by
  rintro x z ⟨y, ⟨hxyR, hxyS⟩, hyzR, hyzS⟩
  exact ⟨⟨y, hxyR, hyzR⟩, ⟨y, hxyS, hyzS⟩⟩

/-- ✱34·62. The square of a union is the union of all four composites. -/
theorem star_34_62 (R S : Relation α α) :
    compose (union R S) (union R S) =
      union (union (union (compose R R) (compose R S)) (compose S R))
        (compose S S) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxyR | hxyS, hyzR | hyzS⟩
    · exact Or.inl (Or.inl (Or.inl ⟨y, hxyR, hyzR⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨y, hxyR, hyzS⟩))
    · exact Or.inl (Or.inr ⟨y, hxyS, hyzR⟩)
    · exact Or.inr ⟨y, hxyS, hyzS⟩
  · rintro (((⟨y, hxyR, hyzR⟩ | ⟨y, hxyR, hyzS⟩) |
      ⟨y, hxyS, hyzR⟩) | ⟨y, hxyS, hyzS⟩)
    · exact ⟨y, Or.inl hxyR, Or.inl hyzR⟩
    · exact ⟨y, Or.inl hxyR, Or.inr hyzS⟩
    · exact ⟨y, Or.inr hxyS, Or.inl hyzR⟩
    · exact ⟨y, Or.inr hxyS, Or.inr hyzS⟩

/-- ✱34·63. Converse commutes with relational squaring. -/
theorem star_34_63 (R : Relation α α) :
    converse (compose R R) = compose (converse R) (converse R) := by
  exact star_34_2 R R

/-- ✱34·7. `S | S˘` is symmetric. -/
theorem star_34_7 (S : Relation α β) :
    converse (compose S (converse S)) = compose S (converse S) := by
  rw [star_34_2]
  rfl

/-- ✱34·701. `S˘ | S` is symmetric. -/
theorem star_34_701 (S : Relation α β) :
    converse (compose (converse S) S) = compose (converse S) S := by
  rw [star_34_2]
  rfl

/-- ✱34·702. The field of `S | S˘` is exactly the domain of `S`. -/
theorem star_34_702 (S : Relation α β) (x : α) :
    field (compose S (converse S)) x ↔ domain S x := by
  constructor
  · rintro (⟨z, y, hxy, _⟩ | ⟨z, y, _, hxy⟩)
    · exact ⟨y, hxy⟩
    · exact ⟨y, hxy⟩
  · rintro ⟨y, hxy⟩
    exact Or.inl ⟨x, y, hxy, hxy⟩

end PM.Architecture.Star34QProofBlock5
