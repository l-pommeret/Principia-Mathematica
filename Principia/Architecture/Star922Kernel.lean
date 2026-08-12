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
    (.sometimes (star_9_21_line3_matrix φ ψ)))

/-- Literal ✱9·08 redex in printed line (5). -/
def line5Redex (existentialBody universalBody : Raw Γ) : Raw Γ :=
  .disj (.quantified .sometimes existentialBody)
    (.quantified .always universalBody)

def line6From908 (existentialBody universalBody : Raw Γ) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (.disj (shiftBoundAt 1 existentialBody)
      (shiftBoundAt 1 universalBody)))

theorem line5_to_line6 (existentialBody universalBody : Raw Γ) :
    NormalizesScopedAt 0 (line5Redex existentialBody universalBody)
      (line6From908 existentialBody universalBody) := by
  exact star_9_08_at 0 existentialBody universalBody

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

/-- Dedicated ✱9·22 slots, constructed before the inner `z` binder is
introduced.  In particular `φy` is an outer operand and is weakened only
when placed under `z`; this differs essentially from the already-closed
✱9·21 slots. -/
def phiYOuterRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofApparent φ

def psiZBodyRaw (ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofApparent ψ

def rightLine6Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (.disj (.neg (weakenBound (phiYOuterRaw φ))) (psiZBodyRaw ψ)))

def rightLine7Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always
    (.disj (.neg (phiYOuterRaw φ))
      (.quantified .sometimes (psiZBodyRaw ψ)))

/-- The concrete inner ✱9·07 occurrence in line (6)→(7).  Its left operand
is weakened explicitly beneath `z`, so capture-freedom is syntactic rather
than an untrue post-hoc unused-binder claim. -/
theorem rightLine6_to_line7
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScoped (rightLine6Raw φ ψ) (rightLine7Raw φ ψ) := by
  apply NormalizesScoped.alwaysCongr
  exact NormalizesScoped.star_9_06_imp
    (phiYOuterRaw φ) (psiZBodyRaw ψ)

def leftLine6Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .sometimes
    (.neg (.disj (.neg (phiYOuterRaw φ)) (psiZBodyRaw ψ)))

def concreteLine6Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (leftLine6Raw φ ψ) (rightLine6Raw φ ψ)

def concreteLine7Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (leftLine6Raw φ ψ) (rightLine7Raw φ ψ)

theorem concreteLine6_to_line7
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScoped (concreteLine6Raw φ ψ) (concreteLine7Raw φ ψ) :=
  .disjCongr (.refl _) (rightLine6_to_line7 φ ψ)

def implicationOuterRaw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (.neg (phiYOuterRaw φ)) (psiZBodyRaw ψ)

def post906Line5Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  line5Redex (.neg (implicationOuterRaw φ ψ))
    (.quantified .sometimes
      (.disj (.neg (weakenBound (phiYOuterRaw φ))) (psiZBodyRaw ψ)))

def post908Line6Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  line6From908 (.neg (implicationOuterRaw φ ψ))
    (.quantified .sometimes
      (.disj (.neg (weakenBound (phiYOuterRaw φ))) (psiZBodyRaw ψ)))

theorem post906Line5_to_post908Line6
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (post906Line5Raw φ ψ) (post908Line6Raw φ ψ) :=
  line5_to_line6 _ _

/-- Correct source orientation of printed line (5)→(6): the line-(5)
quantifiers are eliminated into the separated disjunction of line (6). -/
def sourceLine5Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  line6From908 (.neg (implicationOuterRaw φ ψ))
    (.quantified .sometimes
      (.disj (.neg (weakenBound (phiYOuterRaw φ))) (psiZBodyRaw ψ)))

def sourceLine6Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  line5Redex (.neg (implicationOuterRaw φ ψ))
    (.quantified .sometimes
      (.disj (.neg (weakenBound (phiYOuterRaw φ))) (psiZBodyRaw ψ)))

theorem sourceLine5_to_line6
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (sourceLine5Raw φ ψ) (sourceLine6Raw φ ψ) :=
  .disjSometimesAlwaysReverse 0 _ _

theorem sourceLine6_eq_concreteLine6
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    sourceLine6Raw φ ψ = concreteLine6Raw φ ψ := by
  rfl

theorem sourceLine6_to_concreteLine7
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScoped (sourceLine6Raw φ ψ) (concreteLine7Raw φ ψ) := by
  rw [sourceLine6_eq_concreteLine6]
  exact concreteLine6_to_line7 φ ψ

def existentialPsiRaw (ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .sometimes (psiZBodyRaw ψ)

theorem existentialPsi_unused_outer
    (ψ : Apparent Γ [.elementaryProposition]) :
    UnusedBoundAt 0 (existentialPsiRaw ψ) := by
  induction ψ with
  | constant name => trivial
  | real v => trivial
  | bound v =>
      cases v with
      | zero => simp [existentialPsiRaw, psiZBodyRaw, UnusedBoundAt,
          ofApparent, boundIndex]
      | succ v => exact nomatch v
  | neg p ih => exact ih
  | disj p q ihp ihq => exact ⟨ihp, ihq⟩

def finalRaw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.neg (.quantified .always (implicationOuterRaw φ ψ)))
    (.disj
      (.neg (.quantified .sometimes (phiYOuterRaw φ)))
      (dropUnusedBound (existentialPsiRaw ψ)))

theorem concreteLine7_to_final
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScoped (concreteLine7Raw φ ψ) (finalRaw φ ψ) := by
  apply NormalizesScoped.disjCongr
  · exact .negAlwaysReverse _
  · have unused := existentialPsi_unused_outer ψ
    have reinsert := weakenBound_dropUnusedBound (existentialPsiRaw ψ) unused
    rw [rightLine7Raw]
    change NormalizesScoped
      (.quantified .always
        (.disj (.neg (phiYOuterRaw φ)) (existentialPsiRaw ψ))) _
    have extraction := NormalizesScoped.disjRightReverse .always
      (.neg (phiYOuterRaw φ)) (dropUnusedBound (existentialPsiRaw ψ))
    rw [reinsert] at extraction
    exact .trans extraction
      (NormalizesScoped.disjCongr (.negSometimesReverse _) (.refl _))

theorem line4Raw_is_adjacent_line4
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    line4Carrier φ ψ = star_9_21_line4_raw φ ψ := by
  rfl


/-- Closed evidence for the printed chain.  The source line and every later
endpoint remain explicit; a future bridge must identify the audited concrete
line-(6) operands before this structure can be inhabited. -/
structure Star922KernelAssertion
    (φ ψ : Apparent Γ [.elementaryProposition]) where
  line4 : OrderedAssertion (star_9_13_higher_target
    (.sometimes (star_9_21_line3_matrix φ ψ)))
  line5ExistentialBody : Raw Γ
  line5UniversalBody : Raw Γ
  line5 : Raw Γ
  line5Shape : line5 = line5Redex line5ExistentialBody line5UniversalBody
  line6FromLine5 : Raw Γ
  line6FromLine5Shape : line6FromLine5 =
    line6From908 line5ExistentialBody line5UniversalBody
  star908 : NormalizesScopedAt 0 line5 line6FromLine5
  antecedent : Raw Γ
  consequent : Raw Γ
  line6Exact : Raw Γ
  line6CarrierExact : line6Exact = line6FromLine5
  line6Shape : line6Exact = line6Redex antecedent consequent
  line7 : Raw Γ
  line7Shape : line7 = line7Raw antecedent consequent
  star907 : NormalizesScopedAt 0 line6Exact line7

/-- The source-authorized indexed proof of printed line (4). -/
def line4Ordered (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_13_higher_target
      (.sometimes (star_9_21_line3_matrix φ ψ))) :=
  derive_star_9_21_line4 φ ψ

end PM.Architecture.Star922Kernel
