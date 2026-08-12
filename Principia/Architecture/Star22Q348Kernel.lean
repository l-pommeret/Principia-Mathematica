import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star22Q348Kernel

open PM.Architecture.Star22Q341Definitions

/-- ✱22·4: mutual inclusion is pointwise equivalence of membership. -/
theorem star_22_4 (alpha beta : Class Object) :
    (Included alpha beta ∧ Included beta alpha) ↔
      (∀ x, alpha x ↔ beta x) := by
  constructor
  · rintro ⟨hab, hba⟩ x
    exact ⟨hab x, hba x⟩
  · intro h
    exact ⟨fun x => (h x).mp, fun x => (h x).mpr⟩

/-- ✱22·41: mutual inclusion is equality of classes. -/
theorem star_22_41 (alpha beta : Class Object) :
    (Included alpha beta ∧ Included beta alpha) ↔ alpha = beta := by
  constructor
  · intro h
    funext x
    exact propext ((star_22_4 alpha beta).mp h x)
  · rintro rfl
    exact ⟨fun _ h => h, fun _ h => h⟩

/-- ✱22·42: inclusion is reflexive. -/
theorem star_22_42 (alpha : Class Object) : Included alpha alpha := by
  intro _ h
  exact h

/-- ✱22·43: an intersection is included in its first factor. -/
theorem star_22_43 (alpha beta : Class Object) :
    Included (Intersection alpha beta) alpha := by
  intro _ h
  exact h.1

/-- ✱22·45: inclusion in both factors is equivalent to inclusion in their
intersection. -/
theorem star_22_45 (alpha beta gamma : Class Object) :
    (Included alpha beta ∧ Included alpha gamma) ↔
      Included alpha (Intersection beta gamma) := by
  constructor
  · rintro ⟨hab, hac⟩ x hx
    exact ⟨hab x hx, hac x hx⟩
  · intro h
    exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩

end PM.Architecture.Star22Q348Kernel
