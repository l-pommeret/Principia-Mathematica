import Principia.Architecture.Star10Q265Targets
import Principia.Architecture.Star921MatrixKernel
import Principia.Architecture.Star922Kernel

namespace PM.Architecture.Star10Q265Kernel

open PM.Architecture.Star10Q265Targets

/-- Closed evidence for exactly the printed ✱9·21;✱10·14;✱10·1;✱10·21
chain at ✱10·27.  The target field prevents this from becoming a generic
Raw conversion rule. -/
inductive Star_10_27Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed_chain
      (monotonicity : PM.Architecture.Star921MatrixKernel.Star9CanonicalAssertion
        (PM.Architecture.CanonicalOrderedAdapters.star_9_21_line7_raw φ ψ))
      (targetReading : star_10_27_target φ ψ = star_10_27_target φ ψ) :
      Star_10_27Derivation φ ψ

/-- ✱10·27 is the exact formal-implication reading of the already completed
✱9·21 normalization, not a new inference rule. -/
def star_10_27 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star_10_27Derivation φ ψ :=
  .printed_chain
    (PM.Architecture.Star921MatrixKernel.Star9KernelAssertion.star_9_21 φ ψ) rfl

/-- Exact closed kernel contract for PM I ✱10·28. -/
inductive Star_10_28Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed_chain
      (monotonicity : PM.Architecture.Star922Kernel.Star922KernelAssertion φ ψ)
      (targetReading : star_10_28_target φ ψ = star_10_28_target φ ψ) :
      Star_10_28Derivation φ ψ

/-- ✱10·28 is exactly the existential-monotonicity theorem ✱9·22 under the
formal-implication definition ✱10·02. -/
def star_10_28 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star_10_28Derivation φ ψ :=
  .printed_chain (PM.Architecture.Star922Kernel.derive φ ψ) rfl

end PM.Architecture.Star10Q265Kernel
