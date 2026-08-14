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

/-- The exact target retained after withdrawal of the unsound judgement. -/
def target (p : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  star_9_25_target p φ

end PM.Architecture.Star925Kernel
