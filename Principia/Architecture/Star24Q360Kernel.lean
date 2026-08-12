import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star24Q360Kernel

open PM.Architecture.Star22Q341Definitions

/-- PM I ✱24·01: the universal class is the extension of self-identity. -/
def Universal (Object : Sort u) : Class Object :=
  fun x => x = x

/-- PM I ✱24·02: the null class is the complement of the universal class. -/
def Null (Object : Sort u) : Class Object :=
  Complement (Universal Object)

/-- PM I ✱24·03: a class exists exactly when it has a member. -/
def ClassExists (alpha : Class Object) : Prop :=
  ∃ x, alpha x

theorem star_24_01 (Object : Sort u) :
    Universal Object = fun x => x = x := by
  rfl

theorem star_24_02 (Object : Sort u) :
    Null Object = Complement (Universal Object) := by
  rfl

theorem star_24_03 (alpha : Class Object) :
    ClassExists alpha ↔ ∃ x, alpha x := by
  rfl

/-- PM I ✱24·1. As in PM's quantified universe, the displayed object type
has at least one possible argument; at that witness the two classes differ. -/
theorem star_24_1 (Object : Sort u) [Nonempty Object] :
    Null Object ≠ Universal Object := by
  let witness : Nonempty Object := inferInstance
  cases witness with
  | intro x =>
  intro equality
  have hnull : Null Object x := by
    rw [equality]
    rfl
  exact hnull rfl

/-- PM I ✱24·101: the complement of the null class is universal. -/
theorem star_24_101 (Object : Sort u) :
    Universal Object = Complement (Null Object) := by
  funext x
  apply propext
  constructor
  · intro _ hnull
    exact hnull rfl
  · intro _
    rfl

end PM.Architecture.Star24Q360Kernel
