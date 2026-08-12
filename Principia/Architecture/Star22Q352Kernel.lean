import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star22Q352Kernel

open PM.Architecture.Star22Q341Definitions

/-- PM I ✱22·59: membership in a union is disjunctive membership. -/
theorem star_22_59 (x : Object) (alpha beta : Class Object) :
    Union alpha beta x ↔ alpha x ∨ beta x :=
  Iff.rfl

/-- PM I ✱22·6: membership in `α ∪ β` is equivalent to belonging to every
common superclass of `α` and `β`. -/
theorem star_22_6 (x : Object) (alpha beta : Class Object) :
    Union alpha beta x ↔
      ∀ gamma : Class Object, Included alpha gamma → Included beta gamma → gamma x := by
  constructor
  · intro hx gamma hAlpha hBeta
    cases hx with
    | inl h => exact hAlpha x h
    | inr h => exact hBeta x h
  · intro h
    exact h (Union alpha beta) (fun _ ha => Or.inl ha) (fun _ hb => Or.inr hb)

/-- PM I ✱22·61: inclusion is preserved when the containing class is enlarged
by union. -/
theorem star_22_61 (alpha beta gamma : Class Object) :
    Included alpha beta → Included alpha (Union beta gamma) := by
  intro h x hx
  exact Or.inl (h x hx)

/-- PM I ✱22·62: `α ⊂ β` iff adjoining `α` to `β` changes nothing. -/
theorem star_22_62 (alpha beta : Class Object) :
    Included alpha beta ↔ Union alpha beta = beta := by
  constructor
  · intro h
    funext x
    apply propext
    constructor
    · intro hx
      cases hx with
      | inl ha => exact h x ha
      | inr hb => exact hb
    · exact Or.inr
  · intro h x hx
    have : Union alpha beta x := Or.inl hx
    simpa [h] using this

/-- PM I ✱22·621: `α ⊂ β` iff intersecting `α` with `β` leaves `α`. -/
theorem star_22_621 (alpha beta : Class Object) :
    Included alpha beta ↔ Intersection alpha beta = alpha := by
  constructor
  · intro h
    funext x
    apply propext
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, h x hx⟩
  · intro h x hx
    have : Intersection alpha beta x := by
      simpa [h] using hx
    exact this.2

end PM.Architecture.Star22Q352Kernel
