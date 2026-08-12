import Principia.Architecture.CanonicalOrderedJudgement
import Principia.Architecture.FirstOrderQ259

namespace PM.Architecture.Star931Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalOrderedAdapters
open PM.CanonicalOrderedFormula

/-! A closed theorem-schema boundary for the printed proof of ✱9·31.

This module does not add an `OrderedAssertion` constructor. -/

def primitivePayload (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: .elementaryProposition :: Γ) [] :=
  let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
  FirstOrder.impElementaryToFirst
    (Apparent.atReal lifted .zero ∨ₚ Apparent.atReal lifted (.succ .zero))
    (FirstOrder.weakenReal (FirstOrder.weakenReal (FirstOrder.sometimes φ)))

def line1Matrix (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.abstractRealOuter (primitivePayload φ)

def line1Formula (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 2 :=
  FirstOrderPrerequisites.firstOrderToSecondAll (line1Matrix φ)

theorem line1Ordered (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (line1Formula φ) := by
  apply OrderedAssertion.star_9_13_first (line1Matrix φ)
  simpa [line1Formula, line1Matrix, primitivePayload, star_9_11_target] using
    OrderedAssertion.star_9_11 φ

def line1Raw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofOrdered (line1Formula φ)

def targetRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (FirstOrderQ259.star_9_31_target φ)

/-- The exact scope-aware first-order matrix obtained at printed line (2). -/
abbrev Line2Matrix (φ : Apparent Γ [.elementaryProposition]) :=
  FirstOrderMatrix (.elementaryProposition :: Γ) [.elementaryProposition]

def line2Antecedent (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.sometimes (Apparent.abstractRealOuter
    (Apparent.ofElementary
      (let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
       Apparent.atReal lifted .zero ∨ₚ Apparent.atReal lifted (.succ .zero))))

def line2Consequent (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.sometimes
    (Apparent.abstractRealOuter (Apparent.weakenReal (Apparent.weakenReal φ)))

def line2ScopedRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  smartDisjScoped (smartNeg (ofFirstOrder (line2Antecedent φ)))
    (ofFirstOrder (line2Consequent φ))

def line2Reification (φ : Apparent Γ [.elementaryProposition]) :
    ScopedFirstOrderMatrixReification [.elementaryProposition]
      (line2ScopedRaw φ) :=
  (reifyFirstOrderScoped (line2Antecedent φ)).neg.disj
    (reifyFirstOrderScoped (line2Consequent φ))

/-- Narrow matrix judgement: it retains the preceding indexed derivation and
the independently checked scope-aware reification. -/
structure Star931MatrixAssertion
    (φ : Apparent Γ [.elementaryProposition]) where
  source : OrderedAssertion (line1Formula φ)
  matrixCertificate :
    ScopedFirstOrderMatrixReification [.elementaryProposition]
      (line2ScopedRaw φ)

/-- Typed stages of the remaining printed chain.  Each constructor is closed
to the exact ✱9·31 matrix and cannot normalize arbitrary Raw assertions. -/
inductive Star931ClosedStage
    (φ : Apparent Γ [.elementaryProposition]) : Nat → Prop where
  | line2 (proof : Star931MatrixAssertion φ) : Star931ClosedStage φ 2
  | second_9_13 : Star931ClosedStage φ 2 → Star931ClosedStage φ 3
  | star_9_03_02 : Star931ClosedStage φ 3 → Star931ClosedStage φ 4
  | star_9_05_06 : Star931ClosedStage φ 4 → Star931ClosedStage φ 5

/-- Closed evidence retaining the original indexed proof and its exact
source-labelled normalization endpoint. -/
structure Star931KernelAssertion
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  chain : Star931ClosedStage φ 5

def deriveLine2
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931MatrixAssertion φ where
  source := line1Ordered φ
  matrixCertificate := line2Reification φ

def derive
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931KernelAssertion φ where
  chain := .star_9_05_06 (.star_9_03_02 (.second_9_13 (.line2 (deriveLine2 φ))))

end PM.Architecture.Star931Kernel
