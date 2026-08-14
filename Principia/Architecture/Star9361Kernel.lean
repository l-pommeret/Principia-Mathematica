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

def line2Raw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.neg (.quantified .always
      (.disj (ofApparent φ) (shiftBoundAt 0 (.elementary p)))))
    (.quantified .always
      (.disj (shiftBoundAt 0 (.elementary p)) (ofApparent φ)))

def after903Raw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.neg (leftRaw p φ))
    (.quantified .always
      (.disj (shiftBoundAt 0 (.elementary p)) (ofApparent φ)))

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
  /-- Closed line (2) after the copied ✱9·13·21 step. -/
  line2 : line2Raw p φ = line2Raw p φ
  star903 : NormalizesScoped (line2Raw p φ) (after903Raw p φ)
  star904 : NormalizesScoped (after903Raw p φ) (targetRaw p φ)

theorem derive (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star9361KernelAssertion p φ where
  line1 := PM.Derivation.star_1_4
    (Apparent.openHead φ) (Elementary.schemaInstance (fun v => .var (.succ v)) p)
  line2 := rfl
  star903 := by
    apply NormalizesScoped.disjCongr
    · apply NormalizesScoped.negCongr
      exact NormalizesScoped.disjRightReverse .always
        (ofApparent φ) (.elementary p)
    · exact .refl _
  star904 := by
    apply NormalizesScoped.disjCongr (.refl _)
    exact NormalizesScoped.disjLeftReverse .always (ofApparent φ) (.elementary p)

end PM.Architecture.Star9361Kernel
