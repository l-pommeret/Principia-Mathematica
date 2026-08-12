import Principia.Architecture.Star20Q315Definition
import Principia.Architecture.Star22Q341Definitions

/-!
# PM I, ✱22·33–36

Exact membership reductions and class-existence consequences of the typed,
extensional definitions at ✱22·02–04.
-/

namespace PM.Architecture.Star22Q346Kernel

open PM.Architecture.Star22Q341Definitions

/-- PM I ✱22·33: membership in an intersection. -/
theorem star_22_33 (x : Object) (alpha beta : Class Object) :
    Intersection alpha beta x ↔ alpha x ∧ beta x := by
  exact Iff.rfl

/-- PM I ✱22·34: membership in a union. -/
theorem star_22_34 (x : Object) (alpha beta : Class Object) :
    Union alpha beta x ↔ alpha x ∨ beta x := by
  exact Iff.rfl

/-- PM I ✱22·35: membership in a complement is non-membership. -/
theorem star_22_35 (x : Object) (alpha : Class Object) :
    Complement alpha x ↔ ¬ alpha x := by
  exact Iff.rfl

/-- PM I ✱22·351.  PM's possible-argument types are nonempty; exposing that
convention is necessary, since on an empty type a class equals its complement. -/
theorem star_22_351 [Nonempty Object] (alpha : Class Object) :
    Complement alpha ≠ alpha := by
  intro equality
  let x : Object := Classical.choice (inferInstance : Nonempty Object)
  have pointwise : (¬ alpha x) = alpha x := congrFun equality x
  rcases Classical.em (alpha x) with holds | fails
  · exact (Eq.mp pointwise.symm holds) holds
  · exact fails (Eq.mp pointwise fails)

/-- PM I ✱22·36.  Under the typed extensional presentation, characteristic
functions themselves are the predicative codes witnessing membership in
`Cls`; intersection supplies such a code definitionally. -/
theorem star_22_36 (alpha beta : Class Object) :
    PM.Architecture.Star20Q315Definition.Cls
      (fun candidate : Class Object => candidate)
      (Intersection alpha beta) := by
  exact ⟨Intersection alpha beta, rfl⟩

end PM.Architecture.Star22Q346Kernel
