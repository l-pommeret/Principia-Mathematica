import Principia.Architecture.Star922Kernel

namespace PM.Architecture.Star937Kernel

open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
open PM.CanonicalOrderedFormula

def leftRaw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.elementary p) (.quantified .sometimes (ofApparent φ))

def rightRaw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.quantified .sometimes (ofApparent φ)) (.elementary p)

def targetRaw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.neg (leftRaw p φ)) (rightRaw p φ)

def leftFunction (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] :=
  Apparent.ofElementary p ∨ₐ φ

def rightFunction (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] :=
  φ ∨ₐ Apparent.ofElementary p

def line2Raw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.neg (.quantified .sometimes
      (.disj (shiftBoundAt 0 (.elementary p)) (ofApparent φ))))
    (.quantified .sometimes
      (.disj (ofApparent φ) (shiftBoundAt 0 (.elementary p))))

def afterLeft905Raw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.neg (leftRaw p φ))
    (.quantified .sometimes
      (.disj (ofApparent φ) (shiftBoundAt 0 (.elementary p))))

structure Star937KernelAssertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  line1 : PM.Derivation
    ((Elementary.schemaInstance (fun v => .var (.succ v)) p ∨ₚ
      Apparent.openHead φ) ⊃ₚ
      (Apparent.openHead φ ∨ₚ
        Elementary.schemaInstance (fun v => .var (.succ v)) p))
  monotonicity : Star922Kernel.Star922KernelAssertion
    (leftFunction p φ) (rightFunction p φ)
  line2 : line2Raw p φ = line2Raw p φ
  left905 : NormalizesScoped (line2Raw p φ) (afterLeft905Raw p φ)
  right905 : NormalizesScoped (afterLeft905Raw p φ) (targetRaw p φ)

theorem derive (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star937KernelAssertion p φ where
  line1 := PM.Derivation.star_1_4
    (Elementary.schemaInstance (fun v => .var (.succ v)) p)
    (Apparent.openHead φ)
  monotonicity := Star922Kernel.derive (leftFunction p φ) (rightFunction p φ)
  line2 := rfl
  left905 := by
    apply NormalizesScoped.disjCongr
    · apply NormalizesScoped.negCongr
      exact NormalizesScoped.star_9_05_disj_independent_left
        (.elementary p) (ofApparent φ)
    · exact .refl _
  right905 := by
    apply NormalizesScoped.disjCongr (.refl _)
    exact NormalizesScoped.star_9_05_disj_independent_right
      (ofApparent φ) (.elementary p)

end PM.Architecture.Star937Kernel
