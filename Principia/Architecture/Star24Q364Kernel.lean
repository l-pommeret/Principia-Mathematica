import Principia.Architecture.Star22Q341Definitions
import Principia.Architecture.Star24Q362Kernel

/-!
# PM I ✱24·26, ✱24·27, ✱24·3

Exact extensional class proofs for first-edition page 232.  The universal and
null classes come from the preceding ✱24 architecture; intersection, union,
and difference retain their ✱22 definitions.
-/

namespace PM.Architecture.Star24Q364Kernel

/-- PM I ✱24·26: intersection with the universal class is the class itself. -/
theorem star_24_26
    (alpha : PM.Architecture.Star22Q341Definitions.Class Object) :
    PM.Architecture.Star22Q341Definitions.Intersection alpha
      (PM.Architecture.Star24Q362Kernel.universalClass Object) = alpha := by
  funext x
  apply propext
  constructor
  · rintro ⟨ha, _⟩
    exact ha
  · intro ha
    exact ⟨ha, True.intro⟩

/-- PM I ✱24·27: union with the universal class is universal. -/
theorem star_24_27
    (alpha : PM.Architecture.Star22Q341Definitions.Class Object) :
    PM.Architecture.Star22Q341Definitions.Union alpha
      (PM.Architecture.Star24Q362Kernel.universalClass Object) =
        PM.Architecture.Star24Q362Kernel.universalClass Object := by
  funext x
  apply propext
  constructor
  · intro _
    exact True.intro
  · intro _
    exact Or.inr True.intro

/-- PM I ✱24·3: inclusion is equivalent to an empty class difference.
The reverse implication is the sole classical step: emptiness of
`alpha ∩ ¬ beta` supplies double-negation elimination for membership in
`beta`, as in PM's classical propositional basis. -/
theorem star_24_3
    (alpha beta : PM.Architecture.Star22Q341Definitions.Class Object) :
    PM.Architecture.Star22Q341Definitions.Included alpha beta ↔
      PM.Architecture.Star22Q341Definitions.Difference alpha beta =
        PM.Architecture.Star24Q362Kernel.nullClass Object := by
  constructor
  · intro hab
    funext x
    apply propext
    constructor
    · rintro ⟨ha, hnb⟩
      exact False.elim (hnb (hab x ha))
    · intro impossible
      exact False.elim impossible
  · intro hempty x ha
    apply Classical.byContradiction
    intro hnb
    have memberDifference :
        PM.Architecture.Star22Q341Definitions.Difference alpha beta x :=
      ⟨ha, hnb⟩
    have memberNull :
        PM.Architecture.Star24Q362Kernel.nullClass Object x := by
      rw [← hempty]
      exact memberDifference
    exact memberNull

end PM.Architecture.Star24Q364Kernel
