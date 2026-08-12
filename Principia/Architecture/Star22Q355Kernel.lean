namespace PM.Architecture.Star22Q355Kernel

/-- A PM class at the homogeneous element type `α`. -/
abbrev Class (α : Sort u) := α → Prop

/-- PM inclusion `A ⊂ B`. -/
def Included (A B : Class α) : Prop :=
  ∀ x, A x → B x

/-- PM intersection `A ∩ B`. -/
def intersection (A B : Class α) : Class α :=
  fun x => A x ∧ B x

/-- PM union `A ∪ B`. -/
def union (A B : Class α) : Class α :=
  fun x => A x ∨ B x

/-- PM complement `−A`. -/
def complement (A : Class α) : Class α :=
  fun x => ¬ A x

/-- PM I ✱22·71 defines the unparenthesized triple union by left
association. -/
def tripleUnion (A B C : Class α) : Class α :=
  union (union A B) C

/-- Exact definitional equation PM I ✱22·71. -/
theorem star_22_71 (A B C : Class α) :
    tripleUnion A B C = union (union A B) C := by
  rfl

/-- Exact theorem PM I ✱22·72. -/
theorem star_22_72 (A B C D : Class α) :
    Included A C → Included B D → Included (union A B) (union C D) := by
  intro leftInclusion rightInclusion x member
  cases member with
  | inl memberA => exact Or.inl (leftInclusion x memberA)
  | inr memberB => exact Or.inr (rightInclusion x memberB)

/-- Exact theorem PM I ✱22·73. -/
theorem star_22_73 (A B C D : Class α) :
    A = C → B = D → union A B = union C D := by
  rintro rfl rfl
  rfl

/-- Exact theorem PM I ✱22·74. -/
theorem star_22_74 (A B C : Class α) :
    (Included (intersection A B) C ∧ Included (intersection A C) B) ↔
      intersection A B = intersection A C := by
  constructor
  · rintro ⟨leftToRight, rightToLeft⟩
    funext x
    apply propext
    constructor
    · intro member
      exact ⟨member.1, leftToRight x member⟩
    · intro member
      exact ⟨member.1, rightToLeft x member⟩
  · intro equality
    constructor
    · intro x member
      exact ((congrFun equality x).mp member).2
    · intro x member
      exact ((congrFun equality x).mpr member).2

/-- Exact theorem PM I ✱22·8. -/
theorem star_22_8 (A : Class α) :
    complement (complement A) = A := by
  classical
  funext x
  apply propext
  constructor
  · intro doubleNegation
    by_cases member : A x
    · exact member
    · exact False.elim (doubleNegation member)
  · intro member notMember
    exact notMember member

end PM.Architecture.Star22Q355Kernel
