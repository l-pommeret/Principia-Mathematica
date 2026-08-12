import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star22Q345Kernel

open PM.Architecture.Star22Q341Definitions

/-- PM I ✱22·1: inclusion unfolds to pointwise formal implication. -/
theorem star_22_1 (a b : Class α) :
    Included a b = (∀ x, a x → b x) :=
  star_22_01 a b

/-- PM I ✱22·2: intersection is the extension of conjunction. -/
theorem star_22_2 (a b : Class α) :
    Intersection a b = (fun x => a x ∧ b x) :=
  star_22_02 a b

/-- PM I ✱22·3: union is the extension of disjunction. -/
theorem star_22_3 (a b : Class α) :
    Union a b = (fun x => a x ∨ b x) :=
  star_22_03 a b

/-- PM I ✱22·31: complement is the extension of non-membership. -/
theorem star_22_31 (a : Class α) :
    Complement a = (fun x => ¬ a x) :=
  star_22_04 a

/-- PM I ✱22·32: difference is the extension of membership in the first
class together with non-membership in the second. -/
theorem star_22_32 (a b : Class α) :
    Difference a b = (fun x => a x ∧ ¬ b x) := by
  rfl

end PM.Architecture.Star22Q345Kernel
