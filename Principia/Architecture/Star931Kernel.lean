import Principia.Architecture.CanonicalOrderedJudgement
import Principia.Architecture.FirstOrderQ259
import Principia.Experimental.CanonicalOrderedFormula

namespace PM.Architecture.Star931Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalOrderedAdapters
open PM.CanonicalOrderedFormula

/-! A closed theorem-schema boundary for the printed proof of ✱9·31.

This module does not add an `OrderedAssertion` constructor.  It records the
existing indexed line-(1) proof and the single source-labelled normalization
chain whose endpoint is the already-declared ✱9·31 target. -/

def line1Formula (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 2 :=
  FirstOrderPrerequisites.firstOrderToSecondAll
    (PM.Experimental.CanonicalOrderedFormula.star_9_31_line1_matrix φ)

def line1Raw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofOrdered (line1Formula φ)

def targetRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (FirstOrderQ259.star_9_31_target φ)

/-- The closed printed normalization from the twice-closed existential
matrix to `(∃x).φx ∨ (∃x).φx ⊃ (∃x).φx`.  Its endpoints are fixed by `φ`;
it is not a generic Raw conversion. -/
inductive Star931Normalization
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed_9_13_9_03_02_9_05_06 : Star931Normalization φ

/-- Closed evidence retaining the original indexed proof and its exact
source-labelled normalization endpoint. -/
structure Star931KernelAssertion
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  line1 : OrderedAssertion (line1Formula φ)
  normalization : Star931Normalization φ

def derive
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931KernelAssertion φ where
  line1 := PM.Experimental.CanonicalOrderedFormula.star_9_31_line1_ordered φ
  normalization := .printed_9_13_9_03_02_9_05_06

end PM.Architecture.Star931Kernel
