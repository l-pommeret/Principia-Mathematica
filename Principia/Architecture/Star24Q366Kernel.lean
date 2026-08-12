import Principia.Architecture.Star22Q341Definitions
import Principia.Architecture.Star24Q360Kernel

namespace PM.Architecture.Star24Q366Kernel

open PM.Architecture.Star22Q341Definitions
open PM.Architecture.Star24Q360Kernel

/-- ✱24·33: a union whose first class is universal is universal. -/
theorem star_24_33 (alpha beta : Class Object) :
    alpha = Universal Object → Union alpha beta = Universal Object := by
  rintro rfl
  funext x
  apply propext
  exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩

/-- ✱24·34: an intersection whose first class is null is null. -/
theorem star_24_34 (alpha beta : Class Object) :
    alpha = Null Object → Intersection alpha beta = Null Object := by
  rintro rfl
  funext x
  apply propext
  constructor
  · exact And.left
  · intro hnull
    exact False.elim (hnull rfl)

/-- ✱24·35: intersection with the universal class on the left changes
nothing. -/
theorem star_24_35 (alpha beta : Class Object) :
    alpha = Universal Object → Intersection alpha beta = beta := by
  rintro rfl
  funext x
  apply propext
  exact ⟨And.right, fun hb => ⟨rfl, hb⟩⟩

/-- ✱24·36: union with the null class on the left changes nothing. -/
theorem star_24_36 (alpha beta : Class Object) :
    alpha = Null Object → Union alpha beta = beta := by
  rintro rfl
  funext x
  apply propext
  constructor
  · rintro (hnull | hb)
    · exact False.elim (hnull rfl)
    · exact hb
  · exact Or.inr

/-- ✱24·37: two classes have null intersection exactly when every member of
the first differs from every member of the second. -/
theorem star_24_37 (alpha beta : Class Object) :
    Intersection alpha beta = Null Object ↔
      ∀ x y, alpha x → beta y → x ≠ y := by
  constructor
  · intro h x y hx hy hxy
    subst y
    have hnull : Null Object x := by
      rw [← h]
      exact ⟨hx, hy⟩
    exact hnull rfl
  · intro h
    funext x
    apply propext
    constructor
    · rintro ⟨hx, hy⟩
      exact False.elim (h x x hx hy rfl)
    · intro hnull
      exact False.elim (hnull rfl)

end PM.Architecture.Star24Q366Kernel
