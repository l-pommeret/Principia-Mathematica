import Principia.Architecture.CanonicalOrderedJudgement
import Principia.Architecture.FirstOrderQ259

namespace PM.Architecture.Star931Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
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

def line2Formula (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrderMatrix (.elementaryProposition :: Γ) [.elementaryProposition] :=
  (line2Reification φ).formula

/-- Exact quantified carrier consumed by the second printed ✱9·13. -/
def line3Carrier (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrderMatrix.Quantified (.elementaryProposition :: Γ) [] :=
  .always (line2Formula φ)

def line3Target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 3 :=
  star_9_13_higher_target (line3Carrier φ)

def closedLine3Raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (line3Target φ)

def closedLine3ScopedRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofThirdOrderScoped
    (FirstOrderMatrix.abstractThirdOuter (line3Carrier φ))

theorem closedLine3Raw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    closedLine3Raw φ =
      .quantified .always (.quantified .always
        (ofFirstOrderMatrix
          (FirstOrderMatrix.abstractRealOuter (line2Formula φ)))) := by
  rfl

theorem closedLine3ScopedRaw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    closedLine3ScopedRaw φ =
      .quantified .always (.quantified .always
        (ofFirstOrderMatrixScoped
          (FirstOrderMatrix.abstractRealOuter (line2Formula φ)))) := by
  rfl

def closedLine3DisplayRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always
    (ofFirstOrderMatrixRedex
      (FirstOrderMatrix.abstractRealOuter (line2Formula φ))))

theorem closedMatrixRedex_shape
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrderMatrixRedex
        (FirstOrderMatrix.abstractRealOuter (line2Formula φ)) =
      .disj
        (.neg (ofFirstOrder
          (FirstOrder.abstractRealOuter (line2Antecedent φ))))
        (ofFirstOrder
          (FirstOrder.abstractRealOuter (line2Consequent φ))) := by
  rfl

def closedConsequentOutside (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofFirstOrder (FirstOrder.sometimes φ)

theorem ofApparent_abstract_inner_weakenReal
    (φ : Apparent Γ [.elementaryProposition]) :
    ofApparent (Apparent.abstractRealOuter
      (Apparent.rename Apparent.innerVariableRenaming
        (Apparent.weakenReal (τ := .elementaryProposition) φ))) =
      shiftBoundAt 1 (ofApparent φ) := by
  induction φ with
  | constant name => rfl
  | real v => rfl
  | bound v =>
      cases v with
      | zero => rfl
      | succ v => exact nomatch v
  | neg p ih => exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj _ _ = Raw.disj _ _
      simp only [Apparent.weakenReal] at ihp ihq
      rw [ihp, ihq]

theorem closedConsequent_is_weakened
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrder (FirstOrder.abstractRealOuter (line2Consequent φ)) =
      shiftBoundAt 0 (closedConsequentOutside φ) := by
  change Raw.quantified .sometimes
      (ofApparent (Apparent.abstractRealOuter
        (Apparent.abstractRealOuter
          (Apparent.weakenReal (Apparent.weakenReal φ))))) = _
  rw [Apparent.abstractRealOuter_weakenReal]
  exact congrArg (Raw.quantified .sometimes)
    (ofApparent_abstract_inner_weakenReal φ)

def closedLine4DisplayRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always
    (.disj
      (.neg (.quantified .sometimes
        (ofFirstOrder (FirstOrder.abstractRealOuter (line2Antecedent φ)))))
      (closedConsequentOutside φ))

theorem closedLine3_to_line4
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (closedLine3DisplayRaw φ)
      (closedLine4DisplayRaw φ) := by
  rw [closedLine3DisplayRaw, closedMatrixRedex_shape,
    closedConsequent_is_weakened]
  exact .quantifiedClosedCongr .always
    (.alwaysImpToSometimesAntecedent 0
      (ofFirstOrder (FirstOrder.abstractRealOuter (line2Antecedent φ)))
      (closedConsequentOutside φ))

def closedAntecedentLeftUnder (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofApparent (Apparent.abstractRealOuter (Apparent.abstractRealOuter
    ((Apparent.ofElementary
      (Apparent.atReal (Apparent.weakenReal (Apparent.weakenReal φ)) .zero)) :
        Apparent (.elementaryProposition :: .elementaryProposition :: Γ)
          [.elementaryProposition])))

def closedAntecedentRightBody (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofApparent (Apparent.abstractRealOuter (Apparent.abstractRealOuter
    ((Apparent.ofElementary
      (Apparent.atReal (Apparent.weakenReal (Apparent.weakenReal φ))
        (.succ .zero))) :
          Apparent (.elementaryProposition :: .elementaryProposition :: Γ)
            [.elementaryProposition])))

theorem closedAntecedentRedex_shape
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrder (FirstOrder.abstractRealOuter (line2Antecedent φ)) =
      .quantified .sometimes
        (.disj (closedAntecedentLeftUnder φ)
          (closedAntecedentRightBody φ)) := by
  rfl

theorem closedAntecedentLeft_unused
    (φ : Apparent Γ [.elementaryProposition]) :
    UnusedBoundAt 0 (closedAntecedentLeftUnder φ) := by
  induction φ with
  | constant name => simp [closedAntecedentLeftUnder, UnusedBoundAt,
      Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
      Apparent.substitute, Apparent.instantiateSubstitution,
      Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
      Apparent.rename, Apparent.abstractRealOuter, ofApparent]
  | real v => simp [closedAntecedentLeftUnder, UnusedBoundAt,
      Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
      Apparent.substitute, Apparent.instantiateSubstitution,
      Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
      Apparent.rename, Apparent.abstractRealOuter, ofApparent]
  | bound v =>
      cases v with
      | zero => simp [closedAntecedentLeftUnder, UnusedBoundAt,
          Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
          Apparent.substitute, Apparent.instantiateSubstitution,
          Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
          Apparent.rename, Apparent.abstractRealOuter, ofApparent, boundIndex]
      | succ v => exact nomatch v
  | neg p ih =>
      simpa [closedAntecedentLeftUnder, UnusedBoundAt,
        Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
        Apparent.substitute, Apparent.instantiateSubstitution,
        Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
        Apparent.rename, Apparent.abstractRealOuter, ofApparent] using ih
  | disj p q ihp ihq =>
      simpa [closedAntecedentLeftUnder, UnusedBoundAt,
        Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
        Apparent.substitute, Apparent.instantiateSubstitution,
        Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
        Apparent.rename, Apparent.abstractRealOuter, ofApparent] using And.intro ihp ihq

def closedFinalDisplayRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always
    (.disj
      (.neg (.disj
        (.quantified .sometimes
          (dropUnusedBound (closedAntecedentLeftUnder φ)))
        (.quantified .sometimes (closedAntecedentRightBody φ))))
      (closedConsequentOutside φ))

/-- Source-faithful endpoint of printed ✱9·31.  It remains a canonical Raw
formula because the printed derivation reaches it through the order-three
carrier introduced by the second ✱9·13; collapsing it to the historical
order-one target would erase that assigned-order binder. -/
def exactTargetRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always
    (.disj
      (.neg (.disj
        (.quantified .sometimes
          (dropUnusedBound (closedAntecedentLeftUnder φ)))
        (.quantified .sometimes (closedAntecedentRightBody φ))))
      (closedConsequentOutside φ))

theorem closedFinalDisplayRaw_eq_exactTargetRaw
    (φ : Apparent Γ [.elementaryProposition]) :
    closedFinalDisplayRaw φ = exactTargetRaw φ := by
  rfl

theorem closedLine4_to_final
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (closedLine4DisplayRaw φ)
      (closedFinalDisplayRaw φ) := by
  rw [closedLine4DisplayRaw, closedAntecedentRedex_shape]
  exact .quantifiedClosedCongr .always
    (.disjCongr 0
      (.negCongr 0
        (.sometimesSometimesDisjWitness 0
          (closedAntecedentLeftUnder φ) (closedAntecedentRightBody φ)
          (closedAntecedentLeft_unused φ)))
      (.refl 0 (closedConsequentOutside φ)))

theorem closedLine3_to_final
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (closedLine3DisplayRaw φ)
      (closedFinalDisplayRaw φ) :=
  .trans (closedLine3_to_line4 φ) (closedLine4_to_final φ)

def closedLine3NormalizedRaw
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always
    (normalizeFirstOrderMatrixAfterAbstract 0 (line2Formula φ)))

structure ClosedLine3NormalizationCertificate
    (φ : Apparent Γ [.elementaryProposition]) where
  matrix : FirstOrderMatrix Γ
    [.elementaryProposition, .elementaryProposition]
  matrixExact : matrix = FirstOrderMatrix.abstractRealOuter (line2Formula φ)
  sourceExact : closedLine3DisplayRaw φ =
    .quantified .always (.quantified .always
      (ofFirstOrderMatrixRedex matrix))
  targetExact : closedLine3NormalizedRaw φ =
    .quantified .always (.quantified .always
      (ofFirstOrderMatrixScoped matrix))
  normalization : NormalizesScopedAt 0
    (closedLine3DisplayRaw φ) (closedLine3NormalizedRaw φ)

def closedLine3NormalizationCertificate
    (φ : Apparent Γ [.elementaryProposition]) :
    ClosedLine3NormalizationCertificate φ := by
  let matrix := FirstOrderMatrix.abstractRealOuter (line2Formula φ)
  refine ⟨matrix, rfl, rfl, ?_, ?_⟩
  · rfl
  · exact .quantifiedClosedCongr .always
      (.quantifiedClosedCongr .always
        (normalizesFirstOrderMatrixRedexScoped matrix))

def line2DisplayRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofFirstOrderMatrixRedex (line2Formula φ)

def line3DisplayRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  .quantified .always (line2DisplayRaw φ)

theorem line2DisplayRaw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    line2DisplayRaw φ =
      .disj (.neg (ofFirstOrder (line2Antecedent φ)))
        (ofFirstOrder (line2Consequent φ)) := by
  rfl

theorem line3DisplayRaw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    line3DisplayRaw φ =
      .quantified .always
        (.disj (.neg (ofFirstOrder (line2Antecedent φ)))
          (ofFirstOrder (line2Consequent φ))) := by
  rw [line3DisplayRaw, line2DisplayRaw_unfold]

def line3ConsequentOutside (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofFirstOrder (FirstOrder.weakenReal (FirstOrder.sometimes φ))

theorem ofApparent_inner_weakenReal
    (φ : Apparent Γ [.elementaryProposition]) :
    ofApparent (Apparent.rename Apparent.innerVariableRenaming
      (Apparent.weakenReal (τ := .elementaryProposition) φ)) =
      shiftBoundAt 1 (ofApparent
        (Apparent.weakenReal (τ := .elementaryProposition) φ)) := by
  induction φ with
  | constant name => rfl
  | real v => rfl
  | bound v => cases v <;> rfl
  | neg p ih => exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj _ _ = Raw.disj _ _
      have hp := ihp
      have hq := ihq
      simp only [Apparent.weakenReal] at hp hq
      rw [hp, hq]

theorem line2Consequent_is_weakened
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrder (line2Consequent φ) =
      weakenBound (line3ConsequentOutside φ) := by
  change Raw.quantified .sometimes
      (ofApparent (Apparent.abstractRealOuter
        (Apparent.weakenReal (Apparent.weakenReal φ)))) = _
  rw [Apparent.abstractRealOuter_weakenReal]
  exact congrArg (Raw.quantified .sometimes)
    (ofApparent_inner_weakenReal φ)

def line4DisplayRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  .disj
    (.neg (.quantified .sometimes (ofFirstOrder (line2Antecedent φ))))
    (line3ConsequentOutside φ)

theorem line3_to_line4
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (line3DisplayRaw φ) (line4DisplayRaw φ) := by
  rw [line3DisplayRaw_unfold, line2Consequent_is_weakened]
  exact .alwaysImpToSometimesAntecedent 0
    (ofFirstOrder (line2Antecedent φ)) (line3ConsequentOutside φ)

theorem line2ScopedRaw_roundTrip (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrderMatrixScoped (line2Formula φ) = line2ScopedRaw φ :=
  (line2Reification φ).roundTrip

def line3ScopedRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  .quantified .always (line2ScopedRaw φ)

theorem line3Display_to_scoped
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (line3DisplayRaw φ) (line3ScopedRaw φ) := by
  exact .quantifiedClosedCongr .always
    (normalizesFirstOrderMatrixRedexScoped (line2Formula φ))

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
  | second_9_13
      (line2Proof : Star931ClosedStage φ 2)
      (carrier : FirstOrderMatrix.Quantified
        (.elementaryProposition :: Γ) [])
      (carrierExact : carrier = line3Carrier φ)
      (targetExact : star_9_13_higher_target carrier = line3Target φ) :
      Star931ClosedStage φ 3
  | star_9_03_02
      (line3Proof : Star931ClosedStage φ 3)
      (certificate : NormalizesScopedAt 0
        (closedLine3DisplayRaw φ) (closedLine4DisplayRaw φ)) :
      Star931ClosedStage φ 4
  | star_9_05_06
      (line4Proof : Star931ClosedStage φ 4)
      (certificate : NormalizesScopedAt 0
        (closedLine4DisplayRaw φ) (closedFinalDisplayRaw φ)) :
      Star931ClosedStage φ 5

/-- Closed evidence retaining the original indexed proof and its exact
source-labelled normalization endpoint. -/
structure Star931KernelAssertion
    (φ : Apparent Γ [.elementaryProposition]) where
  chain : Star931ClosedStage φ 5
  endpoint : Raw Γ
  endpointExact : endpoint = exactTargetRaw φ
  normalization : NormalizesScopedAt 0
    (closedLine3DisplayRaw φ) endpoint

def deriveLine2
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931MatrixAssertion φ where
  source := line1Ordered φ
  matrixCertificate := line2Reification φ

def derive
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931KernelAssertion φ where
  chain := .star_9_05_06 (.star_9_03_02
    (.second_9_13 (.line2 (deriveLine2 φ)) (line3Carrier φ) rfl rfl)
    (closedLine3_to_line4 φ)) (closedLine4_to_final φ)
  endpoint := closedFinalDisplayRaw φ
  endpointExact := closedFinalDisplayRaw_eq_exactTargetRaw φ
  normalization := closedLine3_to_final φ

end PM.Architecture.Star931Kernel
