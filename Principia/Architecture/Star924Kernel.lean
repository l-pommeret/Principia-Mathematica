import Principia.Architecture.Star922Kernel

namespace PM.Architecture.Star924Kernel

open PM.Architecture.FirstOrderPrerequisites

/-!
# PM I ✱9·24: the fixed existential-identity instance

The printed demonstration is `Id.✱9·13·22`.  The earlier closed ✱9·22
certificate is therefore used only at its self-instance; this module adds no
`OrderedAssertion` constructor or Raw-to-assertion conversion.
-/

/-- Exact closed judgement for the printed existential identity. -/
abbrev Star924KernelAssertion
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Star922Kernel.Star922KernelAssertion φ φ

/-- PM I ✱9·24, the source-labelled self-instance of the closed ✱9·22 chain.
No generic detachment or assigned-order reification is introduced. -/
theorem derive (φ : Apparent Γ [.elementaryProposition]) :
    Star924KernelAssertion φ :=
  Star922Kernel.derive φ φ

end PM.Architecture.Star924Kernel
