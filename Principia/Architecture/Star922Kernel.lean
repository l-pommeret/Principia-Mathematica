import Principia.Architecture.CanonicalOrderedJudgement

namespace PM.Architecture.Star922Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
open PM.CanonicalOrderedFormula

/-! Source-faithful closed syntax boundary for PM I ✱9·22.

The indexed line-(4) proof remains separate from its subsequent definitional
normalizations.  This module adds no `OrderedAssertion` constructor. -/

def line4Carrier (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (star_9_13_higher_target
    (.always (star_9_21_line3_matrix φ ψ)))

/-- Exact ✱9·07 redex used in printed line (6)→(7). -/
def line6Redex (antecedent consequent : Raw Γ) : Raw Γ :=
  .disj (.quantified .always antecedent)
    (.quantified .sometimes consequent)

def line7Raw (antecedent consequent : Raw Γ) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (.disj (shiftBoundAt 1 antecedent) (shiftBoundAt 1 consequent)))

theorem line6_to_line7 (antecedent consequent : Raw Γ) :
    NormalizesScopedAt 0 (line6Redex antecedent consequent)
      (line7Raw antecedent consequent) := by
  exact star_9_07_at 0 antecedent consequent

/-- Closed evidence for the printed chain.  The source line and every later
endpoint remain explicit; a future bridge must identify the audited concrete
line-(6) operands before this structure can be inhabited. -/
structure Star922KernelAssertion
    (φ ψ : Apparent Γ [.elementaryProposition]) where
  line4 : OrderedAssertion (star_9_13_higher_target
    (.always (star_9_21_line3_matrix φ ψ)))
  antecedent : Raw Γ
  consequent : Raw Γ
  line6Exact : Raw Γ
  line6Shape : line6Exact = line6Redex antecedent consequent
  line7 : Raw Γ
  line7Shape : line7 = line7Raw antecedent consequent
  star907 : NormalizesScopedAt 0 line6Exact line7

end PM.Architecture.Star922Kernel
