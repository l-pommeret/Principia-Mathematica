import Principia.Architecture.Star925Kernel

/-!
# PM I ✱10·12

The printed proposition is explicitly cited as ✱9·25 and has the identical
ordered target.  This module exposes that exact closed judgement under its
✱10 number; it introduces no conversion or assertion constructor.
-/

namespace PM.FirstEdition.Volume1.Star10

open PM
open PM.Architecture.FirstOrderPrerequisites

/-- PM I (1910), p. 146, ✱10·12: `⊢ : .(x).p ∨ φx .⊃ : p .∨ .(x).φx`. -/
theorem star_10_12 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    PM.Architecture.Star925Kernel.Star925KernelAssertion p φ :=
  PM.Architecture.Star925Kernel.derive p φ

end PM.FirstEdition.Volume1.Star10
