namespace PM.Architecture.Star22Q349Kernel

/-- A PM class at the homogeneous element type `α`. -/
abbrev Class (α : Sort u) := α → Prop

/-- PM class inclusion `α ⊂ β`. -/
def Included (A B : Class α) : Prop :=
  ∀ x, A x → B x

/-- PM class intersection `α ∩ β`. -/
def intersection (A B : Class α) : Class α :=
  fun x => A x ∧ B x

/-- Exact theorem PM I ✱22·46. -/
theorem star_22_46 (x : α) (A B : Class α) :
    A x → Included A B → B x := by
  intro member inclusion
  exact inclusion x member

/-- Exact theorem PM I ✱22·47. -/
theorem star_22_47 (A B C : Class α) :
    Included A C → Included (intersection A B) C := by
  intro inclusion x member
  exact inclusion x member.1

/-- Exact theorem PM I ✱22·48. -/
theorem star_22_48 (A B C : Class α) :
    Included A B → Included (intersection A C) (intersection B C) := by
  intro inclusion x member
  exact ⟨inclusion x member.1, member.2⟩

/-- Exact theorem PM I ✱22·481. -/
theorem star_22_481 (A B C : Class α) :
    A = B → intersection A C = intersection B C := by
  rintro rfl
  rfl

/-- Exact theorem PM I ✱22·49. -/
theorem star_22_49 (A B C D : Class α) :
    Included A B → Included C D →
      Included (intersection A C) (intersection B D) := by
  intro leftInclusion rightInclusion x member
  exact ⟨leftInclusion x member.1, rightInclusion x member.2⟩

end PM.Architecture.Star22Q349Kernel
