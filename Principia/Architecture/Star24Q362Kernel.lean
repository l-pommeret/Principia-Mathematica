namespace PM.Architecture.Star24Q362Kernel

/-- A PM class over a homogeneous element type. -/
abbrev Class (α : Sort u) := α → Prop

/-- PM inclusion `A ⊂ B`. -/
def Included (A B : Class α) : Prop :=
  ∀ x, A x → B x

/-- The null class `Λ`. -/
def nullClass (α : Sort u) : Class α :=
  fun _ => False

/-- The universal class `V`, relative to the element type `α`. -/
def universalClass (α : Sort u) : Class α :=
  fun _ => True

/-- Exact theorem PM I ✱24·12. -/
theorem star_24_12 :
    ∀ A : Class α, Included (nullClass α) A := by
  intro A x member
  exact False.elim member

/-- Exact theorem PM I ✱24·13. -/
theorem star_24_13 (A : Class α) :
    A = nullClass α ↔ Included A (nullClass α) := by
  constructor
  · rintro rfl
    exact star_24_12 (α := α) (nullClass α)
  · intro inclusion
    funext x
    apply propext
    constructor
    · intro member
      exact inclusion x member
    · intro impossible
      exact False.elim impossible

/-- Exact theorem PM I ✱24·14. -/
theorem star_24_14 (A : Class α) :
    (∀ x, A x) ↔ A = universalClass α := by
  constructor
  · intro universal
    funext x
    apply propext
    exact ⟨fun _ => True.intro, fun _ => universal x⟩
  · rintro rfl x
    exact True.intro

/-- Exact theorem PM I ✱24·141. -/
theorem star_24_141 (A : Class α) :
    Included (universalClass α) A ↔ universalClass α = A := by
  constructor
  · intro inclusion
    funext x
    apply propext
    exact ⟨fun _ => inclusion x True.intro, fun _ => True.intro⟩
  · rintro rfl x member
    exact member

/-- Exact theorem PM I ✱24·15. -/
theorem star_24_15 (A : Class α) :
    (∀ x, ¬ A x) ↔ A = nullClass α := by
  constructor
  · intro empty
    funext x
    apply propext
    constructor
    · intro member
      exact False.elim (empty x member)
    · intro impossible
      exact False.elim impossible
  · rintro rfl x member
    exact member

end PM.Architecture.Star24Q362Kernel
