import Principia.Architecture.Star921MatrixKernel

namespace PM.Architecture.Star9361Kernel

open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
open PM.CanonicalOrderedFormula

def leftRaw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.quantified .always (ofApparent φ)) (.elementary p)

def rightRaw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.elementary p) (.quantified .always (ofApparent φ))

def targetRaw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.neg (leftRaw p φ)) (rightRaw p φ)

def leftFunction (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] :=
  φ ∨ₐ Apparent.ofElementary p

def rightFunction (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] :=
  Apparent.ofElementary p ∨ₐ φ

structure Star9361KernelAssertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  line1 : PM.Derivation
    ((Apparent.openHead φ ∨ₚ Elementary.schemaInstance (fun v => .var (.succ v)) p) ⊃ₚ
      (Elementary.schemaInstance (fun v => .var (.succ v)) p ∨ₚ Apparent.openHead φ))
  monotonicity : Star921MatrixKernel.Star9CanonicalAssertion
    (star_9_21_line7_raw (leftFunction p φ) (rightFunction p φ))
  endpoint : targetRaw p φ = targetRaw p φ

theorem derive (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star9361KernelAssertion p φ where
  line1 := PM.Derivation.star_1_4
    (Apparent.openHead φ) (Elementary.schemaInstance (fun v => .var (.succ v)) p)
  monotonicity := Star921MatrixKernel.Star9KernelAssertion.star_9_21
    (leftFunction p φ) (rightFunction p φ)
  endpoint := rfl

end PM.Architecture.Star9361Kernel
