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

/-- The actual ✱9·06 operands in printed line (4).  They are stated in the
scope outside `z`: the antecedent already lies below the retained `y,x`
binders, while the consequent is shifted past both of them. -/
def line4AntecedentRaw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  dropUnusedBound (rawImp (star_9_21_phi_x_closed_raw φ)
    (star_9_21_psi_x_closed_raw ψ))

def line4ConsequentRaw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  rawImp (star_9_21_phi_y_closed_raw φ) (star_9_21_psi_z_closed_raw ψ)

def sourceLine4Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes (.quantified .sometimes
    (.disj (.neg (weakenBound (line4AntecedentRaw φ ψ)))
      (line4ConsequentRaw φ ψ))))

def sourceLine5From906Raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (.disj (.neg (line4AntecedentRaw φ ψ))
      (.quantified .sometimes (line4ConsequentRaw φ ψ))))

theorem sourceLine4_to_line5
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScoped (sourceLine4Raw φ ψ) (sourceLine5From906Raw φ ψ) := by
  apply NormalizesScoped.alwaysCongr
  apply NormalizesScoped.sometimesCongr
  exact NormalizesScoped.star_9_06_imp
    (line4AntecedentRaw φ ψ) (line4ConsequentRaw φ ψ)

theorem line4Carrier_eq_sourceLine4
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    line4Carrier φ ψ = sourceLine4Raw φ ψ := by
  change star_9_21_line4_raw φ ψ = sourceLine4Raw φ ψ
  rw [star_9_21_line4_raw_named]
  have unused : UnusedBoundAt 0
      (rawImp (star_9_21_phi_x_closed_raw φ)
        (star_9_21_psi_x_closed_raw ψ)) :=
    ⟨star_9_21_phi_x_closed_unused_zero φ,
      star_9_21_psi_x_closed_unused_zero ψ⟩
  have reinsert := weakenBound_dropUnusedBound
    (rawImp (star_9_21_phi_x_closed_raw φ)
      (star_9_21_psi_x_closed_raw ψ)) unused
  simp only [star_9_21_line4_named_raw, sourceLine4Raw,
    line4AntecedentRaw, line4ConsequentRaw]
  rw [reinsert]
  rfl

theorem phiXClosed_slot
    (φ : Apparent Γ [.elementaryProposition]) :
    star_9_21_phi_x_closed_raw φ = weakenBound (weakenBound (ofApparent φ)) := by
  induction φ with
  | constant name => rfl
  | real v => cases v <;> rfl
  | bound v => cases v with
    | zero => rfl
    | succ v => exact nomatch v
  | neg p ih =>
      change Raw.neg (star_9_21_phi_x_closed_raw p) =
        Raw.neg (weakenBound (weakenBound (ofApparent p)))
      exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj (star_9_21_phi_x_closed_raw p)
          (star_9_21_phi_x_closed_raw q) =
        Raw.disj (weakenBound (weakenBound (ofApparent p)))
          (weakenBound (weakenBound (ofApparent q)))
      rw [ihp, ihq]

theorem psiXClosed_slot
    (ψ : Apparent Γ [.elementaryProposition]) :
    star_9_21_psi_x_closed_raw ψ = weakenBound (weakenBound (ofApparent ψ)) := by
  induction ψ with
  | constant name => rfl
  | real v => cases v <;> rfl
  | bound v => cases v with
    | zero => rfl
    | succ v => exact nomatch v
  | neg p ih =>
      change Raw.neg (star_9_21_psi_x_closed_raw p) =
        Raw.neg (weakenBound (weakenBound (ofApparent p)))
      exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj (star_9_21_psi_x_closed_raw p)
          (star_9_21_psi_x_closed_raw q) =
        Raw.disj (weakenBound (weakenBound (ofApparent p)))
          (weakenBound (weakenBound (ofApparent q)))
      rw [ihp, ihq]

theorem phiYClosed_slot
    (φ : Apparent Γ [.elementaryProposition]) :
    star_9_21_phi_y_closed_raw φ = ofApparent φ := by
  induction φ with
  | constant name => rfl
  | real v => cases v <;> rfl
  | bound v => cases v with
    | zero => rfl
    | succ v => exact nomatch v
  | neg p ih =>
      change Raw.neg (star_9_21_phi_y_closed_raw p) = Raw.neg (ofApparent p)
      exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj (star_9_21_phi_y_closed_raw p)
          (star_9_21_phi_y_closed_raw q) = Raw.disj (ofApparent p) (ofApparent q)
      rw [ihp, ihq]

theorem psiZClosed_slot
    (ψ : Apparent Γ [.elementaryProposition]) :
    star_9_21_psi_z_closed_raw ψ = weakenBound (ofApparent ψ) := by
  induction ψ with
  | constant name => rfl
  | real v => cases v <;> rfl
  | bound v => cases v with
    | zero => rfl
    | succ v => exact nomatch v
  | neg p ih =>
      change Raw.neg (star_9_21_psi_z_closed_raw p) =
        Raw.neg (weakenBound (ofApparent p))
      exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj (star_9_21_psi_z_closed_raw p)
          (star_9_21_psi_z_closed_raw q) =
        Raw.disj (weakenBound (ofApparent p)) (weakenBound (ofApparent q))
      rw [ihp, ihq]

private theorem dropUnusedBoundAt_shiftBoundAt (cutoff : Nat) (p : Raw Γ) :
    dropUnusedBoundAt cutoff (shiftBoundAt cutoff p) = p := by
  induction p generalizing cutoff with
  | elementary proposition => rfl
  | schema slot => rfl
  | bound index =>
      by_cases h : cutoff ≤ index
      · simp [dropUnusedBoundAt, shiftBoundAt, shiftIndex, h]
        omega
      · have below : index < cutoff := by omega
        simp [dropUnusedBoundAt, shiftBoundAt, shiftIndex, h, below]
  | quantified quantifier body ih =>
      simp [dropUnusedBoundAt, shiftBoundAt, ih]
  | neg proposition ih =>
      simp [dropUnusedBoundAt, shiftBoundAt, ih]
  | disj left right ihLeft ihRight =>
      simp [dropUnusedBoundAt, shiftBoundAt, ihLeft, ihRight]

private theorem dropUnusedBound_weakenBound (p : Raw Γ) :
    dropUnusedBound (weakenBound p) = p :=
  dropUnusedBoundAt_shiftBoundAt 0 p

theorem line4Antecedent_slot
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    line4AntecedentRaw φ ψ = weakenBound (implicationOuterRaw φ ψ) := by
  rw [line4AntecedentRaw, phiXClosed_slot, psiXClosed_slot]
  change dropUnusedBound
      (weakenBound (rawImp (weakenBound (ofApparent φ))
        (weakenBound (ofApparent ψ)))) = _
  rw [dropUnusedBound_weakenBound]
  rfl

theorem line4Consequent_slot
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    line4ConsequentRaw φ ψ =
      .disj (.neg (phiYOuterRaw φ)) (weakenBound (psiZBodyRaw ψ)) := by
  rw [line4ConsequentRaw, phiYClosed_slot, psiZClosed_slot]
  rfl

def computedLine6From906Raw
    (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.quantified .sometimes (.neg (implicationOuterRaw φ ψ)))
    (.quantified .always (.quantified .sometimes
      (.disj (.neg (phiYOuterRaw φ)) (weakenBound (psiZBodyRaw ψ)))))

theorem sourceLine5From906_to_computedLine6
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (sourceLine5From906Raw φ ψ)
      (computedLine6From906Raw φ ψ) := by
  rw [sourceLine5From906Raw, line4Antecedent_slot, line4Consequent_slot]
  exact .disjSometimesAlwaysReverseLocalRight 0
    (.neg (implicationOuterRaw φ ψ))
    (.quantified .sometimes
      (.disj (.neg (phiYOuterRaw φ)) (weakenBound (psiZBodyRaw ψ))))

def computedLine7From906Raw
    (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.quantified .sometimes (.neg (implicationOuterRaw φ ψ)))
    (.quantified .always
      (.disj (.neg (phiYOuterRaw φ))
        (.quantified .sometimes (psiZBodyRaw ψ))))

theorem computedLine6From906_to_line7
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (computedLine6From906Raw φ ψ)
      (computedLine7From906Raw φ ψ) := by
  apply NormalizesScopedAt.disjCongr 0 (.refl 0 _)
  exact .disjUnderAlwaysSometimesLocal 0
    (.neg (phiYOuterRaw φ)) (psiZBodyRaw ψ)

theorem computedLine7From906_eq_concreteLine7
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    computedLine7From906Raw φ ψ = concreteLine7Raw φ ψ := by
  rfl

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
    (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  line4 : OrderedAssertion (star_9_13_higher_target
    (.sometimes (star_9_21_line3_matrix φ ψ)))
  line4Shape : line4Carrier φ ψ = sourceLine4Raw φ ψ
  star906 : NormalizesScoped (sourceLine4Raw φ ψ)
    (sourceLine5From906Raw φ ψ)
  star908 : NormalizesScopedAt 0 (sourceLine5From906Raw φ ψ)
    (computedLine6From906Raw φ ψ)
  star907 : NormalizesScopedAt 0 (computedLine6From906Raw φ ψ)
    (computedLine7From906Raw φ ψ)
  line7Shape : computedLine7From906Raw φ ψ = concreteLine7Raw φ ψ
  finalReduction : NormalizesScoped (concreteLine7Raw φ ψ) (finalRaw φ ψ)

/-- The source-authorized indexed proof of printed line (4). -/
def line4Ordered (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_13_higher_target
      (.sometimes (star_9_21_line3_matrix φ ψ))) :=
  derive_star_9_21_line4 φ ψ

theorem derive (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star922KernelAssertion φ ψ where
  line4 := line4Ordered φ ψ
  line4Shape := line4Carrier_eq_sourceLine4 φ ψ
  star906 := sourceLine4_to_line5 φ ψ
  star908 := sourceLine5From906_to_computedLine6 φ ψ
  star907 := computedLine6From906_to_line7 φ ψ
  line7Shape := computedLine7From906_eq_concreteLine7 φ ψ
  finalReduction := concreteLine7_to_final φ ψ

end PM.Architecture.Star922Kernel
