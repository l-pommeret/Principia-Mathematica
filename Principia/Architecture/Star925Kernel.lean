import Principia.Architecture.Star921MatrixKernel

namespace PM.Architecture.Star925Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.Star921MatrixKernel
open PM.OrderedFormula

/-!
# PM I ✱9·25: fixed distribution from existential identity

The printed demonstration is `Id.✱9·23.(✱9·04)`.  The right-hand formula is
the certified ✱9·04 spelling of the same first-order matrix, so this module
only transports the exact closed ✱9·23 self-instance across that definitional
reading.  It adds no general conversion or detachment rule.
-/

/-- Exact closed judgement for the printed ✱9·25 target. -/
abbrev Star925KernelAssertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Star921MatrixKernel.Star9KernelAssertion (star_9_25_target p φ)

/-- PM I ✱9·25 through its fixed `Id.✱9·23.(✱9·04)` chain. -/
theorem derive (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star925KernelAssertion p φ := by
  show Star9KernelAssertion
    (firstImp
      (OrderedFormula.always (Apparent.ofElementary p ∨ₐ φ))
      (.firstOrder (PM.FirstEdition.Volume1.Star9.star_9_04 p φ)))
  exact
  Star921MatrixKernel.Star9KernelAssertion.star_9_23
    (Apparent.ofElementary p ∨ₐ φ)

end PM.Architecture.Star925Kernel
