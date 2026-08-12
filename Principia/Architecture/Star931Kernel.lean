import Principia.Architecture.CanonicalOrderedJudgement
import Principia.Architecture.FirstOrderQ259
import Principia.Experimental.CanonicalOrderedFormula

namespace PM.Architecture.Star931Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalOrderedAdapters
open PM.CanonicalOrderedFormula

/-! A closed theorem-schema boundary for the printed proof of ✱9·31.

This module does not add an `OrderedAssertion` constructor. -/

def line1Formula (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 2 :=
  FirstOrderPrerequisites.firstOrderToSecondAll
    (PM.Experimental.CanonicalOrderedFormula.star_9_31_line1_matrix φ)

def line1Raw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofOrdered (line1Formula φ)

def targetRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (FirstOrderQ259.star_9_31_target φ)

/-- The exact scope-aware first-order matrix obtained at printed line (2). -/
abbrev Line2Matrix (φ : Apparent Γ [.elementaryProposition]) :=
  (PM.Experimental.CanonicalOrderedFormula.star_9_31_line2_scoped_reification φ).formula

/-- Narrow matrix judgement: it retains the preceding indexed derivation and
the independently checked scope-aware reification. -/
structure Star931MatrixAssertion
    (φ : Apparent Γ [.elementaryProposition]) where
  source : OrderedAssertion (line1Formula φ)
  matrixCertificate :
    PM.Experimental.CanonicalOrderedFormula.ScopedCertifiedFirstOrderMatrix
      [.elementaryProposition]
      (PM.Experimental.CanonicalOrderedFormula.star_9_31_line2_scoped_raw φ)

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
  source := PM.Experimental.CanonicalOrderedFormula.star_9_31_line1_ordered φ
  matrixCertificate :=
    PM.Experimental.CanonicalOrderedFormula.star_9_31_line2_scoped_reification φ

def derive
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931KernelAssertion φ where
  chain := .star_9_05_06 (.star_9_03_02 (.second_9_13 (.line2 (deriveLine2 φ))))

end PM.Architecture.Star931Kernel
