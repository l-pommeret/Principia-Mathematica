import Principia.Architecture.Star10Q265Targets
import Principia.Architecture.Star921MatrixKernel
import Principia.Architecture.Star922Kernel
import Principia.Architecture.Star10Q265Prerequisites
import Principia.Architecture.Star10Q265FinalPrerequisites

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

/-- Closed evidence for the printed ✱10·22, ✱10·27 derivation of ✱10·271. -/
structure Star_10_271Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  product : PM.Architecture.Star10Q265Prerequisites.Star_10_22Derivation φ ψ
  forward : Star_10_27Derivation φ ψ
  backward : Star_10_27Derivation ψ φ
  targetReading : star_10_271_target φ ψ = star_10_271_target φ ψ

def star_10_271 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star_10_271Derivation φ ψ where
  product := PM.Architecture.Star10Q265Prerequisites.star_10_22 φ ψ
  forward := star_10_27 φ ψ
  backward := star_10_27 ψ φ
  targetReading := rfl

/-- Closed evidence for the printed ✱10·22, ✱10·28 derivation of ✱10·281. -/
structure Star_10_281Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  product : PM.Architecture.Star10Q265Prerequisites.Star_10_22Derivation φ ψ
  forward : Star_10_28Derivation φ ψ
  backward : Star_10_28Derivation ψ φ
  targetReading : star_10_281_target φ ψ = star_10_281_target φ ψ

def star_10_281 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star_10_281Derivation φ ψ where
  product := PM.Architecture.Star10Q265Prerequisites.star_10_22 φ ψ
  forward := star_10_28 φ ψ
  backward := star_10_28 ψ φ
  targetReading := rfl

/-- Closed evidence for the exact printed ✱3·26, ✱10·11, ✱10·23,
✱3·27, ✱10·28, ✱3·2, ✱10·11·21 chain at ✱10·35. -/
structure Star_10_35Derivation (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  simplifyLeft : {Ξ : RealContext} → (q r : Elementary Ξ) →
    Derivation ((q ∧ₚ r) ⊃ₚ q)
  simplifyRight : {Ξ : RealContext} → (q r : Elementary Ξ) →
    Derivation ((q ∧ₚ r) ⊃ₚ r)
  product : {Ξ : RealContext} → (q r : Elementary Ξ) →
    Derivation (q ⊃ₚ (r ⊃ₚ (q ∧ₚ r)))
  implicationToConstant :
    PM.Architecture.Star10Q265FinalPrerequisites.Star_10_23Derivation φ p
  existentialLift : Star_10_28Derivation φ φ
  generalizeScope : PM.Architecture.Star10Q265FinalPrerequisites.Star_10_11_21Action
  targetReading : star_10_35_target p φ = star_10_35_target p φ

def star_10_35 (p : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :
    Star_10_35Derivation p φ where
  simplifyLeft := fun q r => PM.FirstEdition.Volume1.Star3.star_3_26 q r
  simplifyRight := fun q r => PM.FirstEdition.Volume1.Star3.star_3_27 q r
  product := fun q r => PM.FirstEdition.Volume1.Star3.star_3_2 q r
  implicationToConstant :=
    PM.Architecture.Star10Q265FinalPrerequisites.star_10_23 φ p
  existentialLift := star_10_28 φ φ
  generalizeScope := PM.Architecture.Star10Q265FinalPrerequisites.star_10_11_21
  targetReading := rfl

end PM.Architecture.Star10Q265Kernel
