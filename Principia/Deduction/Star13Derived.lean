import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star5Ramified
import Principia.Deduction.Star10Derived
import Principia.Deduction.Star12Derived
import Principia.FirstEdition.Volume1.Star13

namespace PM.RamifiedSyntax

private def star13_normalizedDisjunction
    (equality : max leftOrder rightOrder = resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    Formula signature real apparent resultOrder :=
  Eq.mp (congrArg (Formula signature real apparent) equality)
    (.disj
      (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
      left right)

private theorem star13_normalizedDisjunction_weakenReal
    (equality : max leftOrder rightOrder = resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    (star13_normalizedDisjunction equality disjunction left right).weakenReal
        (fresh := fresh) =
      star13_normalizedDisjunction equality disjunction
        left.weakenReal right.weakenReal := by
  cases equality
  rfl

private theorem star13_normalizedDisjunction_instantiate
    (equality : max leftOrder rightOrder = resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real (sort :: apparent) leftOrder)
    (right : Formula signature real (sort :: apparent) rightOrder)
    (term : Term signature real apparent sort) :
    (star13_normalizedDisjunction equality disjunction left right).instantiate
        term =
      star13_normalizedDisjunction equality disjunction
        (left.instantiate term) (right.instantiate term) := by
  cases equality
  rfl

/-- The purely truth-functional bridge in printed line (2) of ✱13·101.
It is proved once in the elementary PM calculus and transported below with
three ramified support orders. -/
private theorem star13_elementarySubstitutionBridge
    {context : PM.RealContext}
    (a e x y z w : PM.Elementary context) :
    PM.Derivation (
      (x ⊃ₚ (y ⊃ₚ (z ⊃ₚ w))) ⊃ₚ
      ((a ⊃ₚ x) ⊃ₚ
        ((a ⊃ₚ y) ⊃ₚ
          ((e ⊃ₚ z) ⊃ₚ (a ⊃ₚ (e ⊃ₚ w)))))) := by
  let syll : ∀ p q r : PM.Elementary context,
      PM.Derivation (p ⊃ₚ q) → PM.Derivation (q ⊃ₚ r) →
        PM.Derivation (p ⊃ₚ r) := by
    intro p q r line1 line2
    exact PM.Derivation.detach line1
      (PM.Derivation.detach line2
        (PM.FirstEdition.Volume1.Star2.star_2_05 p q r))
  let mapUnder : ∀ p q r : PM.Elementary context,
      PM.Derivation (q ⊃ₚ r) →
        PM.Derivation ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)) := by
    intro p q r line1
    exact PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star2.star_2_05 p q r)
  let r2 := z ⊃ₚ w
  let r1 := y ⊃ₚ r2
  let d1 := a ⊃ₚ x
  let d2 := a ⊃ₚ y
  let d3 := e ⊃ₚ z
  let target := a ⊃ₚ (e ⊃ₚ w)
  have line1 := PM.FirstEdition.Volume1.Star2.star_2_05 a x r1
  have line2 := PM.FirstEdition.Volume1.Star2.star_2_77 a y r2
  have line3a := PM.FirstEdition.Volume1.Star2.star_2_05 e z w
  have line3b := mapUnder a r2 (d3 ⊃ₚ (e ⊃ₚ w)) line3a
  have line3c := PM.FirstEdition.Volume1.Star2.star_2_04 a d3
    (e ⊃ₚ w)
  have line3 := syll (a ⊃ₚ r2)
    (a ⊃ₚ (d3 ⊃ₚ (e ⊃ₚ w)))
    (d3 ⊃ₚ target) line3b line3c
  have line4 := mapUnder d2 (a ⊃ₚ r2) (d3 ⊃ₚ target) line3
  have line5 := syll (a ⊃ₚ r1) (d2 ⊃ₚ (a ⊃ₚ r2))
    (d2 ⊃ₚ (d3 ⊃ₚ target)) line2 line4
  have line6 := mapUnder d1 (a ⊃ₚ r1)
    (d2 ⊃ₚ (d3 ⊃ₚ target)) line5
  exact syll (x ⊃ₚ r1) (d1 ⊃ₚ (a ⊃ₚ r1))
    (d1 ⊃ₚ (d2 ⊃ₚ (d3 ⊃ₚ target))) line1 line6

private abbrev Star13BridgeContext : PM.RealContext :=
  [.elementaryProposition, .elementaryProposition, .elementaryProposition,
    .elementaryProposition, .elementaryProposition, .elementaryProposition]

private def star13_bridgeA : PM.Elementary Star13BridgeContext := .var .zero
private def star13_bridgeE : PM.Elementary Star13BridgeContext :=
  .var (.succ .zero)
private def star13_bridgeX : PM.Elementary Star13BridgeContext :=
  .var (.succ (.succ .zero))
private def star13_bridgeY : PM.Elementary Star13BridgeContext :=
  .var (.succ (.succ (.succ .zero)))
private def star13_bridgeZ : PM.Elementary Star13BridgeContext :=
  .var (.succ (.succ (.succ (.succ .zero))))
private def star13_bridgeW : PM.Elementary Star13BridgeContext :=
  .var (.succ (.succ (.succ (.succ (.succ .zero)))))

private def star13_bridgeB : PM.Elementary Star13BridgeContext :=
  star13_bridgeX ⊃ₚ (star13_bridgeY ⊃ₚ (star13_bridgeZ ⊃ₚ star13_bridgeW))
private def star13_bridgeD1 : PM.Elementary Star13BridgeContext :=
  star13_bridgeA ⊃ₚ star13_bridgeX
private def star13_bridgeD2 : PM.Elementary Star13BridgeContext :=
  star13_bridgeA ⊃ₚ star13_bridgeY
private def star13_bridgeD3 : PM.Elementary Star13BridgeContext :=
  star13_bridgeE ⊃ₚ star13_bridgeZ
private def star13_bridgeTarget : PM.Elementary Star13BridgeContext :=
  star13_bridgeA ⊃ₚ (star13_bridgeE ⊃ₚ star13_bridgeW)
private def star13_bridgeTail3 : PM.Elementary Star13BridgeContext :=
  star13_bridgeD3 ⊃ₚ star13_bridgeTarget
private def star13_bridgeTail2 : PM.Elementary Star13BridgeContext :=
  star13_bridgeD2 ⊃ₚ star13_bridgeTail3
private def star13_bridgeTail1 : PM.Elementary Star13BridgeContext :=
  star13_bridgeD1 ⊃ₚ star13_bridgeTail2
private def star13_bridgeFormula : PM.Elementary Star13BridgeContext :=
  star13_bridgeB ⊃ₚ star13_bridgeTail1

private def star13_13_sourceElement : PM.Elementary Star13BridgeContext :=
  star13_bridgeE ⊃ₚ (star13_bridgeX ⊃ₚ star13_bridgeY)

private def star13_13_targetElement : PM.Elementary Star13BridgeContext :=
  (star13_bridgeX ∧ₚ star13_bridgeE) ⊃ₚ star13_bridgeY

private def star13_13_bridgeElement : PM.Elementary Star13BridgeContext :=
  star13_13_sourceElement ⊃ₚ star13_13_targetElement

/-- The printed `Comm . Imp` transformation used at ✱13·13. -/
private theorem star13_elementaryCommImp :
    PM.Derivation star13_13_bridgeElement := by
  have line1 := PM.FirstEdition.Volume1.Star2.star_2_04
    star13_bridgeE star13_bridgeX star13_bridgeY
  have line2 := PM.FirstEdition.Volume1.Star3.star_3_31
    star13_bridgeX star13_bridgeE star13_bridgeY
  have line3 := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_13_sourceElement
    (star13_bridgeX ⊃ₚ (star13_bridgeE ⊃ₚ star13_bridgeY))
    star13_13_targetElement
  unfold star13_13_bridgeElement
  exact PM.Derivation.detach line1 (PM.Derivation.detach line2 line3)

private def star13_equivalenceForwardElement :
    PM.Elementary Star13BridgeContext :=
  star13_bridgeA ⊃ₚ star13_bridgeE

private def star13_equivalenceReverseElement :
    PM.Elementary Star13BridgeContext :=
  star13_bridgeE ⊃ₚ star13_bridgeA

private def star13_equivalenceTargetElement :
    PM.Elementary Star13BridgeContext :=
  star13_equivalenceForwardElement ∧ₚ star13_equivalenceReverseElement

private def star13_equivalenceIntroElement :
    PM.Elementary Star13BridgeContext :=
  star13_equivalenceForwardElement ⊃ₚ
    (star13_equivalenceReverseElement ⊃ₚ
      star13_equivalenceTargetElement)

private theorem star13_elementaryEquivalenceIntro :
    PM.Derivation star13_equivalenceIntroElement := by
  have line1 := PM.FirstEdition.Volume1.Star3.star_3_2
    star13_equivalenceForwardElement star13_equivalenceReverseElement
  unfold star13_equivalenceIntroElement star13_equivalenceTargetElement
  exact line1

private def star13_specializationSourceElement :
    PM.Elementary Star13BridgeContext :=
  star13_bridgeA ⊃ₚ (star13_bridgeE ⊃ₚ star13_bridgeX)

private def star13_specializationTargetElement :
    PM.Elementary Star13BridgeContext :=
  star13_bridgeA ⊃ₚ star13_bridgeX

private def star13_specializationBridgeElement :
    PM.Elementary Star13BridgeContext :=
  star13_bridgeE ⊃ₚ
    (star13_specializationSourceElement ⊃ₚ
      star13_specializationTargetElement)

/-- Printed ✱10·1 followed by ✱13·15, at independent orders. -/
private theorem star13_elementarySpecializationBridge :
    PM.Derivation star13_specializationBridgeElement := by
  have line1 := PM.FirstEdition.Volume1.Star2.star_2_27
    star13_bridgeE star13_bridgeX
  have line2 := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_bridgeA (star13_bridgeE ⊃ₚ star13_bridgeX) star13_bridgeX
  have line3 := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_bridgeE
    ((star13_bridgeE ⊃ₚ star13_bridgeX) ⊃ₚ star13_bridgeX)
    (star13_specializationSourceElement ⊃ₚ
      star13_specializationTargetElement)
  unfold star13_specializationBridgeElement
  exact PM.Derivation.detach line1 (PM.Derivation.detach line2 line3)

private def star13_191_pointwiseSourceElement :
    PM.Elementary Star13BridgeContext :=
  star13_bridgeE ⊃ₚ
    (star13_bridgeX ≡ₚ star13_bridgeY)

private def star13_191_pointwiseTargetElement :
    PM.Elementary Star13BridgeContext :=
  star13_bridgeY ⊃ₚ (star13_bridgeE ⊃ₚ star13_bridgeX)

private def star13_191_pointwiseBridgeElement :
    PM.Elementary Star13BridgeContext :=
  star13_191_pointwiseSourceElement ⊃ₚ
    star13_191_pointwiseTargetElement

/-- The propositional `✱13·12 . Comm` part of printed ✱13·191 line (2). -/
private theorem star13_elementary191PointwiseBridge :
    PM.Derivation star13_191_pointwiseBridgeElement := by
  let forward := star13_bridgeX ⊃ₚ star13_bridgeY
  let reverse := star13_bridgeY ⊃ₚ star13_bridgeX
  let equivalence := star13_bridgeX ≡ₚ star13_bridgeY
  let middle := star13_bridgeE ⊃ₚ reverse
  have line1 := PM.FirstEdition.Volume1.Star3.star_3_27 forward reverse
  change PM.Derivation (equivalence ⊃ₚ reverse) at line1
  have line2a := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_bridgeE equivalence reverse
  have line2 := PM.Derivation.detach line1 line2a
  have line3 := PM.FirstEdition.Volume1.Star2.star_2_04
    star13_bridgeE star13_bridgeY star13_bridgeX
  have line4 := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_191_pointwiseSourceElement middle
    star13_191_pointwiseTargetElement
  unfold star13_191_pointwiseBridgeElement
  exact PM.Derivation.detach line2 (PM.Derivation.detach line3 line4)

private def star13_bridgeSupport :
    PM.RealVar Star13BridgeContext .elementaryProposition →
      MixedOrder.TernarySupport
  | .zero => .p
  | .succ .zero => .q
  | .succ (.succ .zero) => .r
  | .succ (.succ (.succ .zero)) => .r
  | .succ (.succ (.succ (.succ .zero))) => .r
  | .succ (.succ (.succ (.succ (.succ .zero)))) => .r

private def star13_bridgeValuation
    (negation : MixedOrder.TernaryNegations signature)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z w : Formula signature real [] negation.rOrder) :
    ∀ v : PM.RealVar Star13BridgeContext .elementaryProposition,
      Formula signature real []
        (negation.order (star13_bridgeSupport v))
  | .zero => a
  | .succ .zero => e
  | .succ (.succ .zero) => x
  | .succ (.succ (.succ .zero)) => y
  | .succ (.succ (.succ (.succ .zero))) => z
  | .succ (.succ (.succ (.succ (.succ .zero)))) => w

private def star13_bridgeInterpret
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z w : Formula signature real [] negation.rOrder)
    (proposition : PM.Elementary Star13BridgeContext) :=
  MixedOrder.interpret MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_bridgeSupport
    (star13_bridgeValuation negation a e x y z w) proposition

private theorem star13_ramifiedSubstitutionBridge
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z w : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ implication negation.r disjunction.r x
      (implication negation.r disjunction.r y
        (implication negation.r disjunction.r z w)))
    (line2 : ⊢ᵣ mixedImplication negation.p disjunction.pr a x)
    (line3 : ⊢ᵣ mixedImplication negation.p disjunction.pr a y)
    (line4 : ⊢ᵣ mixedImplication negation.q disjunction.qr e z) :
    ⊢ᵣ mixedImplication negation.p disjunction.pqr a
      (mixedImplication negation.q disjunction.qr e w) := by
  have bridge := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_bridgeSupport (star13_bridgeValuation negation a e x y z w)
    (star13_elementarySubstitutionBridge star13_bridgeA star13_bridgeE
      star13_bridgeX star13_bridgeY star13_bridgeZ star13_bridgeW)
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w star13_bridgeB at line1
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w star13_bridgeD1 at line2
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w star13_bridgeD2 at line3
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w star13_bridgeD3 at line4
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w star13_bridgeFormula at bridge
  have line5 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_bridgeTail1 := by
    exact MixedOrder.detach
      (MixedOrder.ternaryOrderCombine negation .r .pqr)
      (negation.meaning .r) (disjunction.toVocabulary.meaning .r .pqr)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeB)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeTail1) line1 bridge
  have line6 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_bridgeTail2 := by
    exact MixedOrder.detach
      (MixedOrder.ternaryOrderCombine negation .pr .pqr)
      (negation.meaning .pr) (disjunction.toVocabulary.meaning .pr .pqr)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeD1)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeTail2) line2 line5
  have line7 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_bridgeTail3 := by
    exact MixedOrder.detach
      (MixedOrder.ternaryOrderCombine negation .pr .pqr)
      (negation.meaning .pr) (disjunction.toVocabulary.meaning .pr .pqr)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeD2)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeTail3) line3 line6
  have line8 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_bridgeTarget := by
    exact MixedOrder.detach
      (MixedOrder.ternaryOrderCombine negation .qr .pqr)
      (negation.meaning .qr) (disjunction.toVocabulary.meaning .qr .pqr)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeD3)
      (star13_bridgeInterpret negation disjunction a e x y z w
        star13_bridgeTarget) line4 line7
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w star13_bridgeTarget
  exact line8

/-- The ✱4·84·85 truth-functional core of printed ✱13·101 line (2). -/
private theorem star13_equivalenceSubstitutionBridge
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (psiX psiY phiX phiY : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction
      (equivalence negation disjunction psiX phiX)
      (implication negation disjunction
        (equivalence negation disjunction psiY phiY)
        (implication negation disjunction
          (implication negation disjunction phiX phiY)
          (implication negation disjunction psiX psiY))) := by
  let detach : ∀ p q : Formula signature real [] order,
      (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) →
        (⊢ᵣ q) := by
    intro p q line1 line2
    cases real with
    | nil => exact Derivation.star_1_1_same negation disjunction line1 line2
    | cons head tail =>
        exact Derivation.star_1_11_same negation disjunction line1 line2
  let syll : ∀ p q r : Formula signature real [] order,
      (⊢ᵣ implication negation disjunction p q) →
      (⊢ᵣ implication negation disjunction q r) →
      (⊢ᵣ implication negation disjunction p r) := by
    intro p q r line1 line2
    have line3 := detach (implication negation disjunction q r)
      (implication negation disjunction
        (implication negation disjunction p q)
        (implication negation disjunction p r)) line2
      (star_2_05 negation disjunction p q r)
    exact detach (implication negation disjunction p q)
      (implication negation disjunction p r) line1 line3
  let eqX := equivalence negation disjunction psiX phiX
  let eqY := equivalence negation disjunction psiY phiY
  let phiImplication := implication negation disjunction phiX phiY
  let middle := implication negation disjunction psiX phiY
  let result := implication negation disjunction psiX psiY
  have line1a := star_4_84 negation disjunction psiX phiX phiY
  have line1b := star_3_27 negation disjunction
    (implication negation disjunction middle phiImplication)
    (implication negation disjunction phiImplication middle)
  change ⊢ᵣ implication negation disjunction
    (equivalence negation disjunction middle phiImplication)
    (implication negation disjunction phiImplication middle) at line1b
  have line1 := syll eqX
    (equivalence negation disjunction middle phiImplication)
    (implication negation disjunction phiImplication middle) line1a line1b
  have line2a := star_4_85 negation disjunction psiY phiY psiX
  have line2b := star_3_27 negation disjunction
    (implication negation disjunction result middle)
    (implication negation disjunction middle result)
  change ⊢ᵣ implication negation disjunction
    (equivalence negation disjunction result middle)
    (implication negation disjunction middle result) at line2b
  have line2 := syll eqY
    (equivalence negation disjunction result middle)
    (implication negation disjunction middle result) line2a line2b
  have line3a := star_2_05 negation disjunction phiImplication middle result
  have line3b := star_2_04 negation disjunction
    (implication negation disjunction middle result)
    (implication negation disjunction phiImplication middle)
    (implication negation disjunction phiImplication result)
  have line3 := detach _ _ line3a line3b
  have line4 := syll eqX
    (implication negation disjunction phiImplication middle)
    (implication negation disjunction
      (implication negation disjunction middle result)
      (implication negation disjunction phiImplication result)) line1 line3
  have line5a := star_2_05 negation disjunction eqY
    (implication negation disjunction middle result)
    (implication negation disjunction phiImplication result)
  have line5 := syll eqX
    (implication negation disjunction
      (implication negation disjunction middle result)
      (implication negation disjunction phiImplication result))
    (implication negation disjunction
      (implication negation disjunction eqY
        (implication negation disjunction middle result))
      (implication negation disjunction eqY
        (implication negation disjunction phiImplication result)))
    line4 line5a
  have line6a := detach _ _ line2
    (star_2_02 negation disjunction eqX
      (implication negation disjunction eqY
        (implication negation disjunction middle result)))
  have line6b := star_2_77 negation disjunction eqX
    (implication negation disjunction eqY
      (implication negation disjunction middle result))
    (implication negation disjunction eqY
      (implication negation disjunction phiImplication result))
  have line7 := detach _ _ line5 line6b
  exact detach _ _ line6a line7

private theorem star13_equivalence_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (equivalence negation disjunction left right).substitute sigma =
      equivalence negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).substitute
        sigma) = _
  rw [sameDisjunction_substitute]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).substitute sigma))
      (.neg negation
        ((implication negation disjunction right left).substitute sigma))) = _
  rw [implication_substitute, implication_substitute]

private theorem star13_equivalence_weakenReal
    {fresh : RSort}
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (equivalence negation disjunction left right).weakenReal
      (fresh := fresh) =
      equivalence negation disjunction left.weakenReal right.weakenReal := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).weakenReal))
      (.neg negation
        ((implication negation disjunction right left).weakenReal))) = _
  rw [implication_weakenReal, implication_weakenReal]

private def star13_weakenSubstitution
    (sigma : Substitution signature real source target) :
    Substitution signature (fresh :: real) source target :=
  fun v => (sigma v).weakenReal

private theorem star13_termSubstitute_weakenReal
    (sigma : Substitution signature real source target)
    (term : Term signature real source sort) :
    (term.substitute sigma).weakenReal (fresh := fresh) =
      term.weakenReal.substitute (star13_weakenSubstitution sigma) := by
  cases term <;> rfl

private theorem star13_argumentsSubstitute_weakenReal
    (sigma : Substitution signature real source target)
    (arguments : Arguments signature real source sorts) :
    (arguments.substitute sigma).weakenReal (fresh := fresh) =
      arguments.weakenReal.substitute (star13_weakenSubstitution sigma) := by
  induction arguments with
  | nil => rfl
  | cons term tail line1 =>
      unfold Arguments.substitute Arguments.weakenReal
      rw [star13_termSubstitute_weakenReal, line1]

private theorem star13_termSubstitute_congr
    (sigma tau : Substitution signature real source target)
    (line1 : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (term : Term signature real source resultSort) :
    term.substitute sigma = term.substitute tau := by
  cases term with
  | real v => rfl
  | apparent v => exact line1 v
  | symbol payload => rfl

private theorem star13_argumentsSubstitute_congr
    (sigma tau : Substitution signature real source target)
    (line1 : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (arguments : Arguments signature real source sorts) :
    arguments.substitute sigma = arguments.substitute tau := by
  induction arguments with
  | nil => rfl
  | cons term tail line2 =>
      unfold Arguments.substitute
      rw [star13_termSubstitute_congr sigma tau line1 term, line2]

private theorem star13_liftSubstitution_congr
    (sigma tau : Substitution signature real source target)
    (line1 : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (v : Var (binder :: source) resultSort) :
    liftSubstitution sigma v = liftSubstitution tau v := by
  cases v with
  | zero => rfl
  | succ v => exact congrArg Term.weaken (line1 v)

private theorem star13_liftSubstitutionN_congr
    (binders : List RSort)
    (sigma tau : Substitution signature real source target)
    (line1 : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (v : Var (binders ++ source) resultSort) :
    liftSubstitutionN binders sigma v = liftSubstitutionN binders tau v := by
  induction binders generalizing resultSort with
  | nil => exact line1 v
  | cons binder rest line2 =>
      unfold liftSubstitutionN
      exact star13_liftSubstitution_congr _ _ line2 v

private theorem star13_formulaSubstitute_congr
    (sigma tau : Substitution signature real source target)
    (line1 : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (formula : Formula signature real source order) :
    formula.substitute sigma = formula.substitute tau := by
  induction formula generalizing target with
  | proposition term =>
      exact congrArg Formula.proposition
        (star13_termSubstitute_congr sigma tau line1 term)
  | apply function arguments =>
      unfold Formula.substitute
      rw [star13_termSubstitute_congr sigma tau line1 function,
        star13_argumentsSubstitute_congr sigma tau line1 arguments]
  | neg meaning body line2 =>
      exact congrArg (Formula.neg meaning) (line2 sigma tau line1)
  | disj meaning left right line2 line3 =>
      unfold Formula.substitute
      rw [line2 sigma tau line1, line3 sigma tau line1]
  | always meaning body line2 =>
      exact congrArg (Formula.always meaning)
        (line2 (liftSubstitution sigma) (liftSubstitution tau)
          (star13_liftSubstitution_congr sigma tau line1))
  | incompleteScope kind parameters resultOrder excess scopeOrder matrix
      continuation line2 line3 =>
      unfold Formula.substitute
      rw [line2 (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau)
          (star13_liftSubstitutionN_congr parameters sigma tau line1),
        line3 (liftSubstitution sigma) (liftSubstitution tau)
          (star13_liftSubstitution_congr sigma tau line1)]
  | descriptionScope sort conditionOrder scopeOrder condition continuation
      line2 line3 =>
      unfold Formula.substitute
      rw [line2 (liftSubstitution sigma) (liftSubstitution tau)
          (star13_liftSubstitution_congr sigma tau line1),
        line3 (liftSubstitution sigma) (liftSubstitution tau)
          (star13_liftSubstitution_congr sigma tau line1)]

private theorem star13_liftSubstitution_weakenReal
    (sigma : Substitution signature real source target)
    (v : Var (binder :: source) resultSort) :
    star13_weakenSubstitution (fresh := fresh) (liftSubstitution sigma) v =
      liftSubstitution (star13_weakenSubstitution sigma) v := by
  cases v with
  | zero => rfl
  | succ v => exact Term.weakenReal_rename (fun v => .succ v) (sigma v)

private theorem star13_liftSubstitutionN_weakenReal
    (binders : List RSort)
    (sigma : Substitution signature real source target)
    (v : Var (binders ++ source) resultSort) :
    star13_weakenSubstitution (fresh := fresh)
        (liftSubstitutionN binders sigma) v =
      liftSubstitutionN binders
        (star13_weakenSubstitution (fresh := fresh) sigma) v := by
  induction binders generalizing resultSort with
  | nil => rfl
  | cons binder rest line1 =>
      cases v with
      | zero => rfl
      | succ v =>
          change ((liftSubstitutionN rest sigma v).weaken).weakenReal =
            (liftSubstitutionN rest
              (star13_weakenSubstitution sigma) v).weaken
          unfold Term.weaken
          rw [Term.weakenReal_rename]
          exact congrArg Term.weaken (line1 v)

private theorem star13_formulaSubstitute_weakenReal
    (sigma : Substitution signature real source target)
    (formula : Formula signature real source order) :
    (formula.substitute sigma).weakenReal (fresh := fresh) =
      formula.weakenReal.substitute (star13_weakenSubstitution sigma) := by
  induction formula generalizing target with
  | proposition term =>
      exact congrArg Formula.proposition
        (star13_termSubstitute_weakenReal sigma term)
  | apply function arguments =>
      unfold Formula.substitute Formula.weakenReal
      rw [star13_termSubstitute_weakenReal,
        star13_argumentsSubstitute_weakenReal]
  | neg meaning body line1 =>
      exact congrArg (Formula.neg meaning) (line1 sigma)
  | disj meaning left right line1 line2 =>
      unfold Formula.substitute Formula.weakenReal
      rw [line1 sigma, line2 sigma]
  | always meaning body line1 =>
      have line2 := line1 (liftSubstitution sigma)
      have line3 :
          (body.weakenReal (fresh := fresh)).substitute
              (star13_weakenSubstitution (fresh := fresh)
                (liftSubstitution sigma)) =
            (body.weakenReal (fresh := fresh)).substitute
              (liftSubstitution
                (star13_weakenSubstitution (fresh := fresh) sigma)) := by
        exact star13_formulaSubstitute_congr _ _
          (star13_liftSubstitution_weakenReal (fresh := fresh) sigma)
          (body.weakenReal (fresh := fresh))
      exact congrArg (Formula.always meaning) (Eq.trans line2 line3)
  | incompleteScope kind parameters resultOrder excess scopeOrder matrix
      continuation line1 line2 =>
      have line3 := line1 (liftSubstitutionN parameters sigma)
      have line4 := line2 (liftSubstitution sigma)
      have line5 :
          (matrix.weakenReal (fresh := fresh)).substitute
              (star13_weakenSubstitution (fresh := fresh)
                (liftSubstitutionN parameters sigma)) =
            (matrix.weakenReal (fresh := fresh)).substitute
              (liftSubstitutionN parameters
                (star13_weakenSubstitution (fresh := fresh) sigma)) := by
        exact star13_formulaSubstitute_congr _ _
          (star13_liftSubstitutionN_weakenReal
            (fresh := fresh) parameters sigma)
          (matrix.weakenReal (fresh := fresh))
      have line6 :
          (continuation.weakenReal (fresh := fresh)).substitute
              (star13_weakenSubstitution (fresh := fresh)
                (liftSubstitution sigma)) =
            (continuation.weakenReal (fresh := fresh)).substitute
              (liftSubstitution
                (star13_weakenSubstitution (fresh := fresh) sigma)) := by
        exact star13_formulaSubstitute_congr _ _
          (star13_liftSubstitution_weakenReal (fresh := fresh) sigma)
          (continuation.weakenReal (fresh := fresh))
      unfold Formula.substitute Formula.weakenReal
      rw [line3, line4, line5, line6]
  | descriptionScope sort conditionOrder scopeOrder condition continuation
      line1 line2 =>
      have line3 := line1 (liftSubstitution sigma)
      have line4 := line2 (liftSubstitution sigma)
      have line5 :
          (condition.weakenReal (fresh := fresh)).substitute
              (star13_weakenSubstitution (fresh := fresh)
                (liftSubstitution sigma)) =
            (condition.weakenReal (fresh := fresh)).substitute
              (liftSubstitution
                (star13_weakenSubstitution (fresh := fresh) sigma)) := by
        exact star13_formulaSubstitute_congr _ _
          (star13_liftSubstitution_weakenReal (fresh := fresh) sigma)
          (condition.weakenReal (fresh := fresh))
      have line6 :
          (continuation.weakenReal (fresh := fresh)).substitute
              (star13_weakenSubstitution (fresh := fresh)
                (liftSubstitution sigma)) =
            (continuation.weakenReal (fresh := fresh)).substitute
              (liftSubstitution
                (star13_weakenSubstitution (fresh := fresh) sigma)) := by
        exact star13_formulaSubstitute_congr _ _
          (star13_liftSubstitution_weakenReal (fresh := fresh) sigma)
          (continuation.weakenReal (fresh := fresh))
      unfold Formula.substitute Formula.weakenReal
      rw [line3, line4, line5, line6]

private theorem star13_instantiate_weakenReal
    (formula : Formula signature real (sort :: apparent) order)
    (term : Term signature real apparent sort) :
    (formula.instantiate term).weakenReal (fresh := fresh) =
      formula.weakenReal.instantiate term.weakenReal := by
  unfold Formula.instantiate
  rw [star13_formulaSubstitute_weakenReal]
  exact star13_formulaSubstitute_congr _ _ (by
    intro resultSort v
    cases v <;> rfl) formula.weakenReal

private theorem star13_mixedImplication_weakenReal
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    (mixedImplication negation disjunction left right).weakenReal
        (fresh := fresh) =
      mixedImplication negation disjunction left.weakenReal right.weakenReal := by
  rfl

private theorem star13_mixedImplication_substitute
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real source leftOrder)
    (right : Formula signature real source rightOrder)
    (sigma : Substitution signature real source target) :
    (mixedImplication negation disjunction left right).substitute sigma =
      mixedImplication negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  rfl

private theorem star13_mixedImplication_instantiate
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real (sort :: apparent) leftOrder)
    (right : Formula signature real (sort :: apparent) rightOrder)
    (term : Term signature real apparent sort) :
    (mixedImplication negation disjunction left right).instantiate term =
      mixedImplication negation disjunction
        (left.instantiate term) (right.instantiate term) := by
  rfl

private theorem star13_identity_weakenReal
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real apparent sort) :
    (star_13_01 vocabulary x y).weakenReal (fresh := fresh) =
      star_13_01 vocabulary x.weakenReal y.weakenReal := by
  unfold star_13_01
  dsimp
  change Formula.always vocabulary.universal
    ((implication vocabulary.negation vocabulary.disjunction
      (applyUnary (.apparent .zero) x.weaken)
      (applyUnary (.apparent .zero) y.weaken)).weakenReal) = _
  rw [implication_weakenReal]
  cases x <;> cases y <;> rfl

private theorem star13_reducibilityMatrix_atFunction
    (argumentUniversal : signature.Universal sort order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (psi : Formula signature real [sort] order) :
    let functionSort : RSort := .function [sort] order 0
    let function : Term signature (functionSort :: real) [] functionSort :=
      .real .zero
    (unaryReducibilityMatrix argumentUniversal negation disjunction psi).weakenReal.instantiate
        function =
      Formula.always argumentUniversal
        (equivalence negation disjunction psi.weakenReal
          (applyUnary function.weaken (.apparent .zero))) := by
  let functionSort : RSort := .function [sort] order 0
  let function : Term signature (functionSort :: real) [] functionSort :=
    .real .zero
  let rho : Renaming [sort] [sort, functionSort] :=
    liftRenamingN [sort] (emptyRenaming (target := [functionSort]))
  have line1 : IsIdentitySubstitution
      (substitutionAfterRenaming rho
        (liftSubstitution (instantiateSubstitution function))) := by
    intro resultSort v
    cases v with
    | zero => unfold rho; rfl
    | succ v => cases v
  unfold unaryReducibilityMatrix
  dsimp
  change (Formula.always argumentUniversal
    (equivalence negation disjunction
      (psi.rename rho)
      (applyUnary (.apparent (.succ .zero))
        (.apparent .zero)))).weakenReal.instantiate function = _
  change (Formula.always argumentUniversal
    ((equivalence negation disjunction
      (psi.rename rho)
      (applyUnary (.apparent (.succ .zero))
        (.apparent .zero))).weakenReal)).instantiate function = _
  rw [star13_equivalence_weakenReal, Formula.instantiate,
    substitute_always, star13_equivalence_substitute,
    Formula.weakenReal_rename, Formula.rename_substitute,
    Formula.substitute_eq_self _ line1]
  rfl

private def star13_101_formulaCore
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (max (bindOrder order (.function [sort] order 0)) order) :=
  mixedImplication identityNegation identityDisjunction
    (star_13_01 vocabulary x y)
    (implication vocabulary.negation vocabulary.disjunction
      (psi.instantiate x) (psi.instantiate y))

private theorem star13_101_pointwise
    (vocabulary : IdentityVocabulary signature sort order 0)
    (argumentUniversal : signature.Universal sort order)
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction (bindOrder order sort))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    let functionSort : RSort := .function [sort] order 0
    let function : Term signature (functionSort :: real) [] functionSort :=
      .real .zero
    let phi : Formula signature (functionSort :: real) [sort] order :=
      applyUnary function.weaken (.apparent .zero)
    let a := Formula.always argumentUniversal
      (equivalence vocabulary.negation vocabulary.disjunction
        psi.weakenReal phi)
    ⊢ᵣ mixedImplication
      reducibilityNegation resultDisjunction
      a
      (star13_101_formulaCore vocabulary identityNegation
        identityBaseDisjunction
        psi x y).weakenReal := by
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := bindOrder order sort
    qOrder := bindOrder order (.function [sort] order 0)
    rOrder := order
    p := reducibilityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := reducibilityIdentityNegation
    pr := reducibilityBaseNegation
    qr := identityBaseNegation
    pqr := resultNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := reducibilityDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := reducibilityIdentityDisjunction
    pr := reducibilityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := resultDisjunction
  }
  let functionSort : RSort := .function [sort] order 0
  let function : Term signature (functionSort :: real) [] functionSort :=
    .real .zero
  let phi : Formula signature (functionSort :: real) [sort] order :=
    applyUnary function.weaken (.apparent .zero)
  let a := Formula.always argumentUniversal
    (equivalence vocabulary.negation vocabulary.disjunction
      psi.weakenReal phi)
  let psiX := (psi.weakenReal (fresh := functionSort)).instantiate
    (x.weakenReal (fresh := functionSort))
  let psiY := (psi.weakenReal (fresh := functionSort)).instantiate
    (y.weakenReal (fresh := functionSort))
  let phiX := phi.instantiate (x.weakenReal (fresh := functionSort))
  let phiY := phi.instantiate (y.weakenReal (fresh := functionSort))
  let e := star_13_01 vocabulary
    (x.weakenReal (fresh := functionSort))
    (y.weakenReal (fresh := functionSort))
  let z := implication vocabulary.negation vocabulary.disjunction phiX phiY
  let w := implication vocabulary.negation vocabulary.disjunction psiX psiY
  have line1 := star13_equivalenceSubstitutionBridge
    vocabulary.negation vocabulary.disjunction psiX psiY phiX phiY
  have line2a := star_10_43 argumentUniversal vocabulary.negation
    vocabulary.disjunction negation.p disjunction.pr
    (psi.weakenReal (fresh := functionSort)) phi
    (x.weakenReal (fresh := functionSort))
  have line2 : ⊢ᵣ mixedImplication negation.p disjunction.pr a
      (equivalence vocabulary.negation vocabulary.disjunction psiX phiX) := by
    unfold a psiX phiX
    unfold star_10_43_reading at line2a
    rw [Formula.instantiate, star13_equivalence_substitute] at line2a
    exact line2a
  have line3a := star_10_43 argumentUniversal vocabulary.negation
    vocabulary.disjunction negation.p disjunction.pr
    (psi.weakenReal (fresh := functionSort)) phi
    (y.weakenReal (fresh := functionSort))
  have line3 : ⊢ᵣ mixedImplication negation.p disjunction.pr a
      (equivalence vocabulary.negation vocabulary.disjunction psiY phiY) := by
    unfold a psiY phiY
    unfold star_10_43_reading at line3a
    rw [Formula.instantiate, star13_equivalence_substitute] at line3a
    exact line3a
  let predicate : Term signature (functionSort :: real) [functionSort]
      functionSort := .apparent .zero
  let identityBody : Formula signature (functionSort :: real) [functionSort]
      order := implication vocabulary.negation vocabulary.disjunction
    (applyUnary predicate
      ((x.weakenReal (fresh := functionSort)).weaken
        (fresh := functionSort)))
    (applyUnary predicate
      ((y.weakenReal (fresh := functionSort)).weaken
        (fresh := functionSort)))
  have line4a := Derivation.star_10_1 vocabulary.universal negation.q
    disjunction.qr identityBody function
  have identityInstance : identityBody.instantiate function = z := by
    unfold identityBody predicate z phiX phiY phi
    rw [Formula.instantiate, implication_substitute]
    cases x <;> cases y <;> rfl
  have line4 : ⊢ᵣ mixedImplication negation.q disjunction.qr e z := by
    unfold e star_13_01
    exact Derivation.castAssertion
      (congrArg (fun consequent => mixedImplication negation.q
        disjunction.qr (.always vocabulary.universal identityBody)
        consequent) identityInstance.symm) line4a
  have line5 := star13_ramifiedSubstitutionBridge negation disjunction
    a e
    (equivalence vocabulary.negation vocabulary.disjunction psiX phiX)
    (equivalence vocabulary.negation vocabulary.disjunction psiY phiY)
    z w line1 line2 line3 line4
  have targetEquality :
      (star13_101_formulaCore vocabulary negation.q disjunction.qr
        psi x y).weakenReal = mixedImplication negation.q disjunction.qr e w := by
    unfold star13_101_formulaCore e w psiX psiY
    rw [star13_mixedImplication_weakenReal,
      star13_identity_weakenReal,
      implication_weakenReal,
      star13_instantiate_weakenReal,
      star13_instantiate_weakenReal]
  exact Derivation.castAssertion
    (congrArg (fun consequent => mixedImplication negation.p
      disjunction.pqr a consequent) targetEquality) line5

private theorem star13_detach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons head tail => exact Derivation.star_1_11_same negation disjunction

private theorem star13_mixedDetach
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real [] leftOrder)
    (right : Formula signature real [] rightOrder)
    (line1 : ⊢ᵣ left)
    (line2 : ⊢ᵣ mixedImplication negation disjunction left right) :
    ⊢ᵣ right := by
  exact Derivation.star_9_12 negation disjunction line1 line2

private theorem star13_uncastAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) equality) formula)) →
      Derivation (.assertion formula) := by
  cases equality
  exact fun line1 => line1

private theorem star13_castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun line1 => line1

private def star13_castImplicationDisjunctionResult
    (equality : sourceOrder = targetOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder)
    (result : Formula signature real apparent sourceOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real left right
      (Eq.mp (congrArg (Formula signature real apparent) equality) result) := by
  cases equality
  exact reading

private theorem star13_exposeSameImplication
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (line1 : ⊢ᵣ implication negation disjunction p q) :
    ⊢ᵣ mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction
        (natMaxSelf order).symm) disjunction) p q := by
  let equality := natMaxSelf order
  let rawDisjunction := Eq.mp (congrArg signature.Disjunction
    equality.symm) disjunction
  let rawFormula := mixedImplication negation rawDisjunction p q
  have line2 : ⊢ᵣ Eq.mp
      (congrArg (Formula signature real []) equality) rawFormula := by
    exact Derivation.castAssertion
      (mixedImplication_normalizeSameOrder rfl rfl
        negation disjunction p q) line1
  exact star13_uncastAssertionOrder equality rawFormula line2

/-- The generalized printed `Syll`/`Sum` step used below.  Each of its
three component implications is built independently at its own ramified
order; the `Star2_05Reading` certificate is the generalized ✱2·05
presentation rather than an equality between the displayed members. -/
private theorem star13_mixedSyll
    (pNegation : signature.Negation pOrder)
    (pDisjunction : signature.Disjunction pOrder)
    (qNegation : signature.Negation qOrder)
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (qrNegation : signature.Negation (max qOrder rOrder))
    (pqNegation : signature.Negation (max pOrder qOrder))
    (consequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (outerDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (line1 : ⊢ᵣ mixedImplication pNegation pqDisjunction p q)
    (line2 : ⊢ᵣ mixedImplication qNegation qrDisjunction q r) :
    ⊢ᵣ mixedImplication pNegation prDisjunction p r := by
  let pNegated := Formula.neg pNegation p
  let qNegated := Formula.neg qNegation q
  let pqFormula := mixedImplication pNegation pqDisjunction p q
  let qrFormula := mixedImplication qNegation qrDisjunction q r
  let prFormula := mixedImplication pNegation prDisjunction p r
  let consequenceFormula := mixedImplication pqNegation
    consequenceDisjunction pqFormula prFormula
  let formula := mixedImplication qrNegation outerDisjunction
    qrFormula consequenceFormula
  let reading : Star2_05Reading pNegation pDisjunction p q r formula := {
    pNegated := pNegated
    pNegation := pNegation
    pNegationDefinition := .star_1_01 pNegation p
    primitiveQNegation := qNegation
    primitiveQRDisjunction := qrDisjunction
    primitiveOuterNegation := qrNegation
    primitiveConsequenceNegation := pqNegation
    primitivePQDisjunction := pqDisjunction
    primitivePRDisjunction := prDisjunction
    primitiveConsequenceDisjunction := consequenceDisjunction
    primitiveOuterDisjunction := outerDisjunction
    sumReading := {
      qrFormulaOrder := max qOrder rOrder
      pqFormulaOrder := max pOrder qOrder
      prFormulaOrder := max pOrder rOrder
      consequenceFormulaOrder :=
        max (max pOrder qOrder) (max pOrder rOrder)
      qNegated := qNegated
      qrFormula := qrFormula
      pqFormula := pqFormula
      prFormula := prFormula
      consequenceNegated := .neg pqNegation pqFormula
      consequenceFormula := consequenceFormula
      qrNegated := .neg qrNegation qrFormula
      consequenceNegation := pqNegation
      outerNegation := qrNegation
      qNegationDefinition := .star_1_01 qNegation q
      qrDisjunctionDefinition := .star_1_01 qrDisjunction qNegated r
      pqDisjunctionDefinition := .star_1_01 pqDisjunction pNegated q
      prDisjunctionDefinition := .star_1_01 prDisjunction pNegated r
      consequenceNegationDefinition := .star_1_01 pqNegation pqFormula
      consequenceDisjunctionDefinition := .star_1_01 consequenceDisjunction
        (.neg pqNegation pqFormula) prFormula
      outerNegationDefinition := .star_1_01 qrNegation qrFormula
      outerDisjunctionDefinition := .star_1_01 outerDisjunction
        (.neg qrNegation qrFormula) consequenceFormula
    }
  }
  have line3 := star_2_05 pNegation pDisjunction p q r
    (reading := reading)
  have line4 := star13_mixedDetach qrNegation outerDisjunction
    qrFormula consequenceFormula line2 line3
  exact star13_mixedDetach pqNegation consequenceDisjunction
    pqFormula prFormula line1 line4

/-- Re-present a scoped implication between two members of one assigned
order as the literal ✱1·01 implication.  This is the generalized ✱2·05
conversion used when a ✱9·04 root must feed a printed equivalence. -/
private theorem star13_canonicalizeSameOrderImplication
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (sourceNegation : signature.Negation sourceOrder)
    (sourceConsequenceDisjunction : signature.Disjunction
      (max sourceOrder order))
    (sourceOuterDisjunction : signature.Disjunction
      (max order (max sourceOrder order)))
    (p q : Formula signature real [] order)
    (sourceFormula : Formula signature real [] sourceOrder)
    (sourceDefinition : ImplicationDisjunction signature real
      (.neg negation p) q sourceFormula)
    (line1 : ⊢ᵣ sourceFormula) :
    ⊢ᵣ implication negation disjunction p q := by
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
      disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation (natMaxSelf order).symm) negation
  let consequenceEquality := natMaxCongr
    (natMaxSelf order) (natMaxSelf order)
  let consequenceDisjunction :=
    Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      disjunction
  let resultEquality := natMaxCongr
    (natMaxSelf order) consequenceEquality
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEquality.symm) disjunction
  let pNegated := Formula.neg negation p
  let qNegated := Formula.neg negation q
  let qrFormula := implication negation disjunction q q
  let prFormula := implication negation disjunction p q
  let consequenceFormula := mixedImplication sourceNegation
    sourceConsequenceDisjunction sourceFormula prFormula
  let formula := mixedImplication negation sourceOuterDisjunction
    qrFormula consequenceFormula
  let reading : Star2_05Reading negation disjunction p q q formula := {
    pNegated := pNegated
    pNegation := negation
    pNegationDefinition := .star_1_01 negation p
    primitiveQNegation := negation
    primitiveQRDisjunction := pairDisjunction
    primitiveOuterNegation := pairNegation
    primitiveConsequenceNegation := pairNegation
    primitivePQDisjunction := pairDisjunction
    primitivePRDisjunction := pairDisjunction
    primitiveConsequenceDisjunction := consequenceDisjunction
    primitiveOuterDisjunction := outerDisjunction
    sumReading := {
      qrFormulaOrder := order
      pqFormulaOrder := sourceOrder
      prFormulaOrder := order
      consequenceFormulaOrder := max sourceOrder order
      qNegated := qNegated
      qrFormula := qrFormula
      pqFormula := sourceFormula
      prFormula := prFormula
      consequenceNegated := .neg sourceNegation sourceFormula
      consequenceFormula := consequenceFormula
      qrNegated := .neg negation qrFormula
      consequenceNegation := sourceNegation
      outerNegation := negation
      qNegationDefinition := .star_1_01 negation q
      qrDisjunctionDefinition := .star_1_01_same disjunction qNegated q
      pqDisjunctionDefinition := sourceDefinition
      prDisjunctionDefinition := .star_1_01_same disjunction pNegated q
      consequenceNegationDefinition := .star_1_01 sourceNegation sourceFormula
      consequenceDisjunctionDefinition := .star_1_01
        sourceConsequenceDisjunction (.neg sourceNegation sourceFormula)
        prFormula
      outerNegationDefinition := .star_1_01 negation qrFormula
      outerDisjunctionDefinition := .star_1_01 sourceOuterDisjunction
        (.neg negation qrFormula) consequenceFormula
    }
  }
  have line2 := star_2_05 negation disjunction p q q
    (reading := reading)
  have line3 := star13_mixedDetach negation sourceOuterDisjunction
    qrFormula consequenceFormula (star_2_08 negation disjunction q) line2
  exact star13_mixedDetach sourceNegation sourceConsequenceDisjunction
    sourceFormula prFormula line1 line3

/-- Generalized ✱2·05 conversion of a certified scope tree into the literal
mixed-order implication displayed outside the scope. -/
private theorem star13_canonicalizeMixedImplication
    (pNegation : signature.Negation pOrder)
    (pDisjunction : signature.Disjunction pOrder)
    (qNegation : signature.Negation qOrder)
    (qDisjunction : signature.Disjunction qOrder)
    (targetNegation : signature.Negation (max pOrder qOrder))
    (targetDisjunction : signature.Disjunction (max pOrder qOrder))
    (qPairNegation : signature.Negation (max qOrder qOrder))
    (qPairDisjunction : signature.Disjunction (max qOrder qOrder))
    (targetPairDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder qOrder)))
    (primitiveOuterDisjunction : signature.Disjunction
      (max (max qOrder qOrder)
        (max (max pOrder qOrder) (max pOrder qOrder))))
    (sourceNegation : signature.Negation sourceOrder)
    (sourceConsequenceDisjunction : signature.Disjunction
      (max sourceOrder (max pOrder qOrder)))
    (sourceOuterDisjunction : signature.Disjunction
      (max qOrder (max sourceOrder (max pOrder qOrder))))
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (sourceFormula : Formula signature real [] sourceOrder)
    (sourceDefinition : ImplicationDisjunction signature real
      (.neg pNegation p) q sourceFormula)
    (line1 : ⊢ᵣ sourceFormula) :
    ⊢ᵣ mixedImplication pNegation targetDisjunction p q := by
  let pNegated := Formula.neg pNegation p
  let qNegated := Formula.neg qNegation q
  let qrFormula := implication qNegation qDisjunction q q
  let prFormula := mixedImplication pNegation targetDisjunction p q
  let consequenceFormula := mixedImplication sourceNegation
    sourceConsequenceDisjunction sourceFormula prFormula
  let formula := mixedImplication qNegation sourceOuterDisjunction
    qrFormula consequenceFormula
  let reading : Star2_05Reading pNegation pDisjunction p q q formula := {
    pNegated := pNegated
    pNegation := pNegation
    pNegationDefinition := .star_1_01 pNegation p
    primitiveQNegation := qNegation
    primitiveQRDisjunction := qPairDisjunction
    primitiveOuterNegation := qPairNegation
    primitiveConsequenceNegation := targetNegation
    primitivePQDisjunction := targetDisjunction
    primitivePRDisjunction := targetDisjunction
    primitiveConsequenceDisjunction := targetPairDisjunction
    primitiveOuterDisjunction := primitiveOuterDisjunction
    sumReading := {
      qrFormulaOrder := qOrder
      pqFormulaOrder := sourceOrder
      prFormulaOrder := max pOrder qOrder
      consequenceFormulaOrder := max sourceOrder (max pOrder qOrder)
      qNegated := qNegated
      qrFormula := qrFormula
      pqFormula := sourceFormula
      prFormula := prFormula
      consequenceNegated := .neg sourceNegation sourceFormula
      consequenceFormula := consequenceFormula
      qrNegated := .neg qNegation qrFormula
      consequenceNegation := sourceNegation
      outerNegation := qNegation
      qNegationDefinition := .star_1_01 qNegation q
      qrDisjunctionDefinition := .star_1_01_same qDisjunction qNegated q
      pqDisjunctionDefinition := sourceDefinition
      prDisjunctionDefinition := .star_1_01 targetDisjunction pNegated q
      consequenceNegationDefinition := .star_1_01 sourceNegation sourceFormula
      consequenceDisjunctionDefinition := .star_1_01
        sourceConsequenceDisjunction (.neg sourceNegation sourceFormula)
        prFormula
      outerNegationDefinition := .star_1_01 qNegation qrFormula
      outerDisjunctionDefinition := .star_1_01 sourceOuterDisjunction
        (.neg qNegation qrFormula) consequenceFormula
    }
  }
  have line2 := star_2_05 pNegation pDisjunction p q q
    (reading := reading)
  have line3 := star13_mixedDetach qNegation sourceOuterDisjunction
    qrFormula consequenceFormula (star_2_08 qNegation qDisjunction q) line2
  exact star13_mixedDetach sourceNegation sourceConsequenceDisjunction
    sourceFormula prFormula line1 line3

/-- The heterogeneous forward half of ✱4·76: two consequences under one
antecedent are paired without changing either member's assigned order. -/
private theorem star13_ramifiedPairUnder
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (q r : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ mixedImplication negation.p disjunction.pr p q)
    (line2 : ⊢ᵣ mixedImplication negation.p disjunction.pr p r) :
    ⊢ᵣ mixedImplication negation.p disjunction.pr p
      (conjunction negation.r disjunction.r q r) := by
  have bridge := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => p)
    star13_bridgeSupport
    (star13_bridgeValuation negation p e q r q q)
    (PM.FirstEdition.Volume1.Star4.star_4_76
      star13_bridgeA star13_bridgeX star13_bridgeY)
  let left := conjunction negation.pr disjunction.pr
    (mixedImplication negation.p disjunction.pr p q)
    (mixedImplication negation.p disjunction.pr p r)
  let right := mixedImplication negation.p disjunction.pr p
    (conjunction negation.r disjunction.r q r)
  change ⊢ᵣ star_4_01 negation.pr disjunction.pr left right at bridge
  have line3 : ⊢ᵣ implication negation.pr disjunction.pr left right :=
    star13_detach negation.pr disjunction.pr _ _ bridge
      (star_3_26 negation.pr disjunction.pr
        (implication negation.pr disjunction.pr left right)
        (implication negation.pr disjunction.pr right left))
  have line4 := star13_detach negation.pr disjunction.pr _ _ line1
    (star_3_2 negation.pr disjunction.pr
      (mixedImplication negation.p disjunction.pr p q)
      (mixedImplication negation.p disjunction.pr p r))
  have line5 : ⊢ᵣ left :=
    star13_detach negation.pr disjunction.pr _ _ line2 line4
  exact star13_detach negation.pr disjunction.pr left right line5 line3

/-! The full-scope ✱10·3 matrix used in the printed proof of ✱13·17. -/

private def star13_apparentConjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation left) (.neg negation right))

private theorem star13_apparentConjunction_weakenReal
    {fresh : RSort}
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (star13_apparentConjunction negation disjunction left right).weakenReal
        (fresh := fresh) =
      star13_apparentConjunction negation disjunction
        (left.weakenReal (fresh := fresh))
        (right.weakenReal (fresh := fresh)) := by
  unfold star13_apparentConjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  rfl

private theorem star13_apparentConjunction_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (star13_apparentConjunction negation disjunction left right).substitute sigma =
      star13_apparentConjunction negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold star13_apparentConjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).substitute sigma) = _
  rw [sameDisjunction_substitute]
  rfl

private def star13_star_10_3_formula
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [argument] order) :
    Formula signature real [] (bindOrder order argument) :=
  .always universal
    (implication negation disjunction
      (star13_apparentConjunction negation disjunction
        (implication negation disjunction phi psi)
        (implication negation disjunction psi chi))
      (implication negation disjunction phi chi))

/-- The ✱10·3 instance needed at ✱13·17, reconstructed by pointwise
`Syll` and the primitive generalization rule ✱10·11. -/
private theorem star13_star_10_3
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [argument] order) :
    ⊢ᵣ star13_star_10_3_formula universal negation disjunction phi psi chi := by
  let body := implication negation disjunction
    (star13_apparentConjunction negation disjunction
      (implication negation disjunction phi psi)
      (implication negation disjunction psi chi))
    (implication negation disjunction phi chi)
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 : ⊢ᵣ body.weakenReal.instantiate value := by
    unfold body
    rw [implication_weakenReal, star13_apparentConjunction_weakenReal,
      Formula.instantiate, implication_substitute,
      star13_apparentConjunction_substitute]
    unfold star13_apparentConjunction
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    exact star_3_33 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/-!
# Definitions of PM I, ✱13

Identity itself remains exactly `star_13_01`, the reducible Leibniz
definition in `Principia.Syntax.Ramified`.  The two following declarations are
likewise eliminable definitions; neither adds a constructor to `Derivation`.
-/

/-- ✱13·02: diversity is the eliminable negation of Leibniz identity. -/
def star_13_02
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real apparent sort) :
    Formula signature real apparent
      (bindOrder order (.function [sort] order excess)) :=
  .neg negation (star_13_01 vocabulary x y)

/-- ✱13·03: chained identity is the eliminable conjunction of the two
adjacent Leibniz identities. -/
def star_13_03
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real apparent sort) :
    Formula signature real apparent
      (bindOrder order (.function [sort] order excess)) :=
  .neg negation (sameDisjunction disjunction
    (.neg negation (star_13_01 vocabulary x y))
    (.neg negation (star_13_01 vocabulary y z)))

/-- Audited scope reading of ✱13·01.  Identity is the reducible Leibniz
definition, not Lean equality. -/
def star_13_01_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "x = y .=: (φ) : φ!x .⊃ . φ!y  Df"
  parsed := .assertion (star_13_01 vocabulary x y)

/-- Audited scope reading of ✱13·02. -/
def star_13_02_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "x ≠ y .=. ∼(x = y)  Df"
  parsed := .assertion (star_13_02 vocabulary negation x y)

/-- Audited scope reading of ✱13·03. -/
def star_13_03_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort) : ClaimReading signature real where
  printed := "x = y = z .=. x = y . y = z  Df"
  parsed := .assertion (star_13_03 vocabulary negation disjunction x y z)

/-- Printed left member of ✱13·1, built from the defined identity sign. -/
def star_13_1_left
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) :=
  star_13_01 vocabulary x y

/-- Printed right member of ✱13·1, built directly as Leibniz's quantified
implication rather than by reusing the left-member definition. -/
def star_13_1_right
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (bindOrder order (.function [sort] order excess)) :=
  .always vocabulary.universal
    (implication vocabulary.negation vocabulary.disjunction
      (applyUnary (.apparent .zero) x.weaken)
      (applyUnary (.apparent .zero) y.weaken))

theorem star_13_1_left_unfold
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) :
    star_13_1_left vocabulary x y = star_13_1_right vocabulary x y := rfl

/-- Audited scope reading of ✱13·1. -/
def star_13_1_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ :: x = y .≡ : φ!x .⊃φ . φ!y"
  parsed := .assertion (star_4_01 negation disjunction
    (star_13_1_left vocabulary x y) (star_13_1_right vocabulary x y))

/-- ✱13·1, exactly ✱4·2 after unfolding the Leibniz definition ✱13·01.
`demonstration_provenance: follows-printed`. -/
theorem star_13_1
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) :
    Derivation (star_13_1_reading vocabulary negation disjunction x y).parsed := by
  have line1 := star_4_2 negation disjunction (star_13_1_right vocabulary x y)
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_13_1_left vocabulary x y) (star_13_1_right vocabulary x y)))
  rw [star_13_1_left_unfold]
  exact line1

/-- Object formula asserted at ✱13·101.  The arbitrary `ψ` has the order
used by the predicative representative supplied through ✱12·1. -/
def star_13_101_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (outerNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (max (bindOrder order (.function [sort] order 0)) order) :=
  star13_101_formulaCore vocabulary outerNegation outerDisjunction psi x y

/-- Audited scope reading of ✱13·101. -/
def star_13_101_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (outerNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y .⊃ . ψx .⊃ . ψy"
  parsed := .assertion (star_13_101_formula vocabulary outerNegation
    outerDisjunction psi x y)

/-- ✱13·101.  Printed line (1) is ✱12·1.  For line (2), the
✱4·84·85 substitution bridge is generalized over the representative
function and passed through the exact ✱10·23 scoped implication.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_101
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation
      (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction
      (bindOrder order sort))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (scopeUniversal : signature.Universal (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (scopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (scopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Derivation (star_13_101_reading vocabulary identityNegation
      identityBaseDisjunction psi x y).parsed := by
  let functionSort : RSort := .function [sort] order 0
  let function : Term signature (functionSort :: real) [] functionSort :=
    .real .zero
  let matrix := unaryReducibilityMatrix argumentUniversal
    vocabulary.negation vocabulary.disjunction psi
  let target := star_13_101_formula vocabulary identityNegation
    identityBaseDisjunction psi x y
  let scopeBody := mixedImplication reducibilityNegation resultDisjunction
    matrix (target.rename (fun v => .succ v))
  have matrixAt : matrix.weakenReal.instantiate function =
      Formula.always argumentUniversal
        (equivalence vocabulary.negation vocabulary.disjunction
          psi.weakenReal
          (applyUnary function.weaken (.apparent .zero))) := by
    exact star13_reducibilityMatrix_atFunction argumentUniversal
      vocabulary.negation vocabulary.disjunction psi
  have scopeAt : scopeBody.weakenReal.instantiate function =
      mixedImplication reducibilityNegation resultDisjunction
        (Formula.always argumentUniversal
          (equivalence vocabulary.negation vocabulary.disjunction
            psi.weakenReal
            (applyUnary function.weaken (.apparent .zero))))
        target.weakenReal := by
    unfold scopeBody
    rw [star13_mixedImplication_weakenReal,
      star13_mixedImplication_instantiate, matrixAt,
      Formula.closed_weakenReal_instantiate]
  have line1a := star13_101_pointwise vocabulary argumentUniversal
    reducibilityNegation identityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation resultNegation
    reducibilityDisjunction identityOrderDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    identityBaseDisjunction resultDisjunction psi x y
  have line1 : ⊢ᵣ scopeBody.weakenReal.instantiate function := by
    exact Derivation.castAssertion scopeAt line1a
  have line2 : ⊢ᵣ Formula.always scopeUniversal scopeBody := by
    exact star_10_11 scopeUniversal scopeBody line1
  let leftMember := star_10_23_left scopeUniversal reducibilityNegation
    resultDisjunction matrix target
  let rightMember := star_10_23_right reducibilityExistential
    reducibilityExistential.universal scopeUniversal reducibilityNegation
    resultDisjunction matrix target
  have line3a := star_10_23 reducibilityExistential
    reducibilityExistential.universal scopeUniversal reducibilityNegation
    resultDisjunction scopeNegation scopeDisjunction matrix target
  change ⊢ᵣ star_4_01 scopeNegation scopeDisjunction
    leftMember rightMember at line3a
  have line3b : ⊢ᵣ implication scopeNegation scopeDisjunction
      leftMember rightMember :=
    Derivation.star_9_12_same scopeNegation scopeDisjunction line3a
      (star_3_26 scopeNegation scopeDisjunction
        (implication scopeNegation scopeDisjunction leftMember rightMember)
        (implication scopeNegation scopeDisjunction rightMember leftMember))
  have line3c : ⊢ᵣ leftMember := by
    unfold leftMember star_10_23_left
    exact line2
  have line3 : ⊢ᵣ rightMember :=
    Derivation.star_9_12_same scopeNegation scopeDisjunction line3c line3b
  letI : ImplicationReading reducibilityExistential.outerNegation
      existentialTargetDisjunction
      (.sometimes reducibilityExistential matrix) rightMember target := {
    negated := star_9_02 reducibilityExistential.universal
      reducibilityNegation matrix
    negationDefinition := ImplicationNegation.star_9_02
      reducibilityExistential.outerNegation reducibilityExistential
      reducibilityExistential.universal reducibilityNegation matrix
    disjunctionDefinition := ImplicationDisjunction.star_9_03
      reducibilityExistential.universal scopeUniversal
      (.neg reducibilityNegation matrix) target
      (.disj resultDisjunction (.neg reducibilityNegation matrix)
        (target.rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01 resultDisjunction
        (.neg reducibilityNegation matrix)
        (target.rename (fun v => .succ v)))
  }
  have line4 : ⊢ᵣ .sometimes reducibilityExistential matrix := by
    unfold matrix
    exact star_12_1 reducibilityExistential argumentUniversal
      vocabulary.negation vocabulary.disjunction psi
  exact Derivation.star_9_12 reducibilityExistential.outerNegation
    existentialTargetDisjunction line4 line3

/-- Audited scope reading of ✱13·15. -/
def star_13_15_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ . x = x"
  parsed := .assertion (star_13_01 vocabulary x x)

/-- ✱13·15.  This follows the printed `Id.✱10·11.✱13·1` citation.
`demonstration_provenance: follows-printed`. -/
theorem star_13_15
    (vocabulary : IdentityVocabulary signature sort order excess)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x : Term signature real [] sort) :
    Derivation (star_13_15_reading vocabulary x).parsed := by
  let predicate : Term signature real
      (.function [sort] order excess :: [])
      (.function [sort] order excess) := .apparent .zero
  let body := implication vocabulary.negation vocabulary.disjunction
    (applyUnary predicate x.weaken) (applyUnary predicate x.weaken)
  let value : Term signature (.function [sort] order excess :: real) []
      (.function [sort] order excess) :=
    .real (.zero : Var (.function [sort] order excess :: real)
      (.function [sort] order excess))
  let matrixInstance := (applyUnary predicate x.weaken).weakenReal.instantiate value
  have matrixEq : body.weakenReal.instantiate value =
      implication vocabulary.negation vocabulary.disjunction matrixInstance matrixInstance := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    rfl
  have line1 : ⊢ᵣ body.weakenReal.instantiate value := by
    exact Derivation.castAssertion matrixEq
      (star_2_08 vocabulary.negation vocabulary.disjunction matrixInstance)
  have line2 : ⊢ᵣ star_13_01 vocabulary x x := by
    exact star_10_11 vocabulary.universal body line1
  have line3 := star_13_1 vocabulary identityNegation
    identityDisjunction x x
  exact star13_detach identityNegation identityDisjunction _ _ line2
    (star13_detach identityNegation identityDisjunction _ _ line3
      (star_3_26 identityNegation identityDisjunction _ _))

/-!
The remaining assertions in this section are recorded at their exact
ramified propositional envelopes.  Their named hypotheses are intentional:
the unconditional ✱13·101 substitution theorem, on which the printed chain
depends, has not yet been reconstructed in `Derivation`.  Consequently none
of these declarations is presented as an unconditional derivation.
-/

/-- Audited scope reading of ✱13·11. -/
def star_13_11_right
    (vocabulary : IdentityVocabulary signature sort order 0)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (bindOrder order (.function [sort] order 0)) :=
  let predicate : Term signature real [.function [sort] order 0]
      (.function [sort] order 0) := .apparent .zero
  .always vocabulary.universal
    (equivalence vocabulary.negation vocabulary.disjunction
      (applyUnary predicate x.weaken)
      (applyUnary predicate y.weaken))

def star_13_11_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (x y : Term signature real [] sort) :
    ClaimReading signature real where
  printed := "⊢ :: x = y .≡ : φ!x .≡φ . φ!y"
  parsed := .assertion (star_4_01 negation disjunction
    (star_13_01 vocabulary x y) (star_13_11_right vocabulary x y))

/-- ✱13·11, following the four printed lines.  The two uses of ✱10·11·21
are represented by their literal ✱9·04 scope trees and converted to the
displayed implication only by generalized ✱2·05.
`demonstration_provenance: follows-printed`. -/
theorem star_13_11
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction
      (bindOrder order sort))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (equivalenceScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order (.function [sort] order 0)) order))
    (scopedNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order)
        (.function [sort] order 0)))
    (scopedConsequenceDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order)
          (.function [sort] order 0))
        (bindOrder order (.function [sort] order 0))))
    (scopedOuterDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0))
        (max
          (bindOrder
            (max (bindOrder order (.function [sort] order 0)) order)
            (.function [sort] order 0))
          (bindOrder order (.function [sort] order 0)))))
    (x y : Term signature real [] sort) :
    Derivation (star_13_11_reading vocabulary identityNegation
      identityDisjunction x y).parsed := by
  let functionSort : RSort := .function [sort] order 0
  let function : Term signature (functionSort :: real) [] functionSort :=
    .real .zero
  let predicate : Term signature real [functionSort] functionSort :=
    .apparent .zero
  let phiXBody := applyUnary predicate x.weaken
  let phiYBody := applyUnary predicate y.weaken
  let forwardBody := implication vocabulary.negation vocabulary.disjunction
    phiXBody phiYBody
  let reverseBody := implication vocabulary.negation vocabulary.disjunction
    phiYBody phiXBody
  let equivalenceBody := equivalence vocabulary.negation
    vocabulary.disjunction phiXBody phiYBody
  let identity := star_13_01 vocabulary x y
  let right := star_13_11_right vocabulary x y
  let phi : Formula signature (functionSort :: real) [sort] order :=
    applyUnary function.weaken (.apparent .zero)
  let phiX := phi.instantiate (x.weakenReal (fresh := functionSort))
  let phiY := phi.instantiate (y.weakenReal (fresh := functionSort))
  let forward := implication vocabulary.negation vocabulary.disjunction
    phiX phiY
  let reverse := implication vocabulary.negation vocabulary.disjunction
    phiY phiX
  let pairNegation : MixedOrder.TernaryNegations signature := {
    pOrder := bindOrder order (.function [sort] order 0)
    qOrder := order
    rOrder := order
    p := identityNegation
    q := vocabulary.negation
    r := vocabulary.negation
    pq := identityBaseNegation
    pr := identityBaseNegation
    qr := Eq.mp (congrArg signature.Negation
      (natMaxSelf order).symm) vocabulary.negation
    pqr := Eq.mp (congrArg signature.Negation
      (congrArg (fun inner => max
        (bindOrder order (.function [sort] order 0)) inner)
        (natMaxSelf order)).symm) identityBaseNegation
  }
  let pairDisjunction : MixedOrder.TernaryDisjunctions signature
      pairNegation := {
    p := identityDisjunction
    q := vocabulary.disjunction
    r := vocabulary.disjunction
    pq := identityBaseDisjunction
    pr := identityBaseDisjunction
    qr := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf order).symm) vocabulary.disjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (congrArg (fun inner => max
        (bindOrder order (.function [sort] order 0)) inner)
        (natMaxSelf order)).symm) identityBaseDisjunction
  }
  let consequenceEquality := MixedOrder.ternaryOrderCombine
    pairNegation .pr .pr
  let outerEquality := Eq.trans
    (congrArg (fun inner => max
      (pairNegation.order MixedOrder.TernarySupport.qr) inner)
      consequenceEquality)
    (MixedOrder.ternaryOrderCombine pairNegation .qr .pr)
  have equivalenceAt : equivalenceBody.weakenReal.instantiate function =
      equivalence vocabulary.negation vocabulary.disjunction phiX phiY := by
    unfold equivalenceBody phiX phiY phi phiXBody phiYBody predicate
    rw [star13_equivalence_weakenReal, Formula.instantiate,
      star13_equivalence_substitute]
    cases x <;> cases y <;> rfl
  have line1aRaw := Derivation.star_10_1 vocabulary.universal
    identityNegation identityBaseDisjunction equivalenceBody.weakenReal function
  have line1a : ⊢ᵣ mixedImplication identityNegation
      identityBaseDisjunction right.weakenReal
      (equivalence vocabulary.negation vocabulary.disjunction phiX phiY) := by
    unfold right star_13_11_right
    exact Derivation.castAssertion
      (congrArg (fun consequent => mixedImplication identityNegation
        identityBaseDisjunction
        (.always vocabulary.universal equivalenceBody.weakenReal)
        consequent) equivalenceAt.symm) line1aRaw
  have line1b := star_3_26 vocabulary.negation vocabulary.disjunction
    forward reverse
  change ⊢ᵣ implication vocabulary.negation vocabulary.disjunction
    (equivalence vocabulary.negation vocabulary.disjunction phiX phiY)
    forward at line1b
  have line1b' := star13_exposeSameImplication vocabulary.negation
    vocabulary.disjunction
    (equivalence vocabulary.negation vocabulary.disjunction phiX phiY)
    forward line1b
  have line1c := star13_mixedSyll pairNegation.p pairDisjunction.p
    pairNegation.r pairDisjunction.pr pairDisjunction.qr
    pairDisjunction.pr pairNegation.qr pairNegation.pr
    (Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      pairDisjunction.pr)
    (Eq.mp (congrArg signature.Disjunction outerEquality.symm)
      pairDisjunction.pqr)
    right.weakenReal
    (equivalence vocabulary.negation vocabulary.disjunction phiX phiY)
    forward line1a line1b'
  let line1ScopeBody := mixedImplication identityNegation
    identityBaseDisjunction (right.rename (fun v => .succ v)) forwardBody
  have line1ScopeAt : line1ScopeBody.weakenReal.instantiate function =
      mixedImplication identityNegation identityBaseDisjunction
        right.weakenReal forward := by
    unfold line1ScopeBody forward forwardBody phiX phiY phi
    rw [star13_mixedImplication_weakenReal,
      star13_mixedImplication_instantiate,
      Formula.closed_weakenReal_instantiate]
    rw [implication_weakenReal, Formula.instantiate,
      implication_substitute]
    cases x <;> cases y <;> rfl
  have line1d : ⊢ᵣ line1ScopeBody.weakenReal.instantiate function := by
    exact Derivation.castAssertion line1ScopeAt line1c
  have line1e : ⊢ᵣ Formula.always equivalenceScopeUniversal
      line1ScopeBody := by
    exact star_10_11 equivalenceScopeUniversal line1ScopeBody line1d
  have line1Definition : ImplicationDisjunction signature real
      (Formula.neg identityNegation right) identity
      (.always equivalenceScopeUniversal line1ScopeBody) := by
    unfold identity star_13_01 line1ScopeBody forwardBody
    apply ImplicationDisjunction.star_9_04 vocabulary.universal
      equivalenceScopeUniversal
    exact ImplicationDisjunction.star_1_01 identityBaseDisjunction
      ((Formula.neg identityNegation right).rename (fun v => .succ v))
      (implication vocabulary.negation vocabulary.disjunction
        phiXBody phiYBody)
  have line1 : ⊢ᵣ implication identityNegation identityDisjunction
      right identity := by
    exact star13_canonicalizeSameOrderImplication identityNegation
      identityDisjunction scopedNegation scopedConsequenceDisjunction
      scopedOuterDisjunction right identity
      (.always equivalenceScopeUniversal line1ScopeBody)
      line1Definition line1e
  have line2 : ⊢ᵣ implication identityNegation identityDisjunction
      identity identity := by
    exact star_2_08 identityNegation identityDisjunction identity
  have line3a := star_13_101 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation resultNegation
    reducibilityDisjunction identityDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction
    (Formula.neg vocabulary.negation phi)
    (x.weakenReal (fresh := functionSort))
    (y.weakenReal (fresh := functionSort))
  have negativeAt :
      ((Formula.neg vocabulary.negation phi).instantiate
        (x.weakenReal (fresh := functionSort))) =
        Formula.neg vocabulary.negation phiX := by
    rfl
  have negativeAtY :
      ((Formula.neg vocabulary.negation phi).instantiate
        (y.weakenReal (fresh := functionSort))) =
        Formula.neg vocabulary.negation phiY := by
    rfl
  have line3b : ⊢ᵣ mixedImplication identityNegation
      identityBaseDisjunction identity.weakenReal
      (implication vocabulary.negation vocabulary.disjunction
        (Formula.neg vocabulary.negation phiX)
        (Formula.neg vocabulary.negation phiY)) := by
    unfold star_13_101_reading star_13_101_formula
      star13_101_formulaCore at line3a
    rw [negativeAt, negativeAtY] at line3a
    unfold identity
    rw [star13_identity_weakenReal]
    exact line3a
  have line3c := star_2_17 vocabulary.negation vocabulary.disjunction phiY phiX
  have line3c' := star13_exposeSameImplication vocabulary.negation
    vocabulary.disjunction
    (implication vocabulary.negation vocabulary.disjunction
      (Formula.neg vocabulary.negation phiX)
      (Formula.neg vocabulary.negation phiY)) reverse line3c
  have line3 := star13_mixedSyll pairNegation.p pairDisjunction.p
    pairNegation.r pairDisjunction.pr pairDisjunction.qr
    pairDisjunction.pr pairNegation.qr pairNegation.pr
    (Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      pairDisjunction.pr)
    (Eq.mp (congrArg signature.Disjunction outerEquality.symm)
      pairDisjunction.pqr)
    identity.weakenReal
    (implication vocabulary.negation vocabulary.disjunction
      (Formula.neg vocabulary.negation phiX)
      (Formula.neg vocabulary.negation phiY))
    reverse line3b line3c'
  have line4a := star_13_101 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation resultNegation
    reducibilityDisjunction identityDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction phi
    (x.weakenReal (fresh := functionSort))
    (y.weakenReal (fresh := functionSort))
  have line4b : ⊢ᵣ mixedImplication identityNegation
      identityBaseDisjunction identity.weakenReal forward := by
    unfold star_13_101_reading star_13_101_formula
      star13_101_formulaCore at line4a
    unfold identity forward phiX phiY
    rw [star13_identity_weakenReal]
    exact line4a
  have line4c := star13_ramifiedPairUnder pairNegation pairDisjunction
    identity.weakenReal phiX forward reverse line4b line3
  change ⊢ᵣ mixedImplication identityNegation identityBaseDisjunction
    identity.weakenReal
    (equivalence vocabulary.negation vocabulary.disjunction phiX phiY)
    at line4c
  let line4ScopeBody := mixedImplication identityNegation
    identityBaseDisjunction (identity.rename (fun v => .succ v))
    equivalenceBody
  have line4ScopeAt : line4ScopeBody.weakenReal.instantiate function =
      mixedImplication identityNegation identityBaseDisjunction
        identity.weakenReal
        (equivalence vocabulary.negation vocabulary.disjunction phiX phiY) := by
    unfold line4ScopeBody
    rw [star13_mixedImplication_weakenReal,
      star13_mixedImplication_instantiate,
      Formula.closed_weakenReal_instantiate, equivalenceAt]
  have line4d : ⊢ᵣ line4ScopeBody.weakenReal.instantiate function := by
    exact Derivation.castAssertion line4ScopeAt line4c
  have line4e : ⊢ᵣ Formula.always equivalenceScopeUniversal
      line4ScopeBody := by
    exact star_10_11 equivalenceScopeUniversal line4ScopeBody line4d
  have line4Definition : ImplicationDisjunction signature real
      (Formula.neg identityNegation identity) right
      (.always equivalenceScopeUniversal line4ScopeBody) := by
    unfold right star_13_11_right line4ScopeBody
    apply ImplicationDisjunction.star_9_04 vocabulary.universal
      equivalenceScopeUniversal
    exact ImplicationDisjunction.star_1_01 identityBaseDisjunction
      ((Formula.neg identityNegation identity).rename (fun v => .succ v))
      equivalenceBody
  have line4 : ⊢ᵣ implication identityNegation identityDisjunction
      identity right := by
    exact star13_canonicalizeSameOrderImplication identityNegation
      identityDisjunction scopedNegation scopedConsequenceDisjunction
      scopedOuterDisjunction identity right
      (.always equivalenceScopeUniversal line4ScopeBody)
      line4Definition line4e
  have line5 := star13_detach identityNegation identityDisjunction _ _ line4
    (star_3_2 identityNegation identityDisjunction
      (implication identityNegation identityDisjunction identity right)
      (implication identityNegation identityDisjunction right identity))
  exact star13_detach identityNegation identityDisjunction _ _ line1 line5

/-- The displayed formula at ✱13·12, with the two occurrences of `ψ`
obtained by substitution in one arbitrary matrix. -/
def star_13_12_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (max (bindOrder order (.function [sort] order 0)) order) :=
  mixedImplication identityNegation identityBaseDisjunction
    (star_13_01 vocabulary x y)
    (equivalence vocabulary.negation vocabulary.disjunction
      (psi.instantiate x) (psi.instantiate y))

/-- Audited scope reading of ✱13·12. -/
def star_13_12_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y .⊃ . ψx .≡ . ψy"
  parsed := .assertion (star_13_12_formula vocabulary identityNegation
    identityBaseDisjunction psi x y)

/-- ✱13·12.  Printed line (1) is ✱13·101; line (2) applies it to `∼ψ`
and then uses Transp; line (3) combines both consequences by Comp.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_12
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation
      (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction
      (bindOrder order sort))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (scopeUniversal : signature.Universal (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (scopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (scopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Derivation (star_13_12_reading vocabulary identityNegation
      identityBaseDisjunction psi x y).parsed := by
  let identity := star_13_01 vocabulary x y
  let psiX := psi.instantiate x
  let psiY := psi.instantiate y
  let forward := implication vocabulary.negation vocabulary.disjunction
    psiX psiY
  let reverse := implication vocabulary.negation vocabulary.disjunction
    psiY psiX
  let pairNegation : MixedOrder.TernaryNegations signature := {
    pOrder := bindOrder order (.function [sort] order 0)
    qOrder := order
    rOrder := order
    p := identityNegation
    q := vocabulary.negation
    r := vocabulary.negation
    pq := identityBaseNegation
    pr := identityBaseNegation
    qr := Eq.mp (congrArg signature.Negation
      (natMaxSelf order).symm) vocabulary.negation
    pqr := Eq.mp (congrArg signature.Negation
      (congrArg (fun inner => max
        (bindOrder order (.function [sort] order 0)) inner)
        (natMaxSelf order)).symm) identityBaseNegation
  }
  let pairDisjunction : MixedOrder.TernaryDisjunctions signature
      pairNegation := {
    p := identityOrderDisjunction
    q := vocabulary.disjunction
    r := vocabulary.disjunction
    pq := identityBaseDisjunction
    pr := identityBaseDisjunction
    qr := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf order).symm) vocabulary.disjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (congrArg (fun inner => max
        (bindOrder order (.function [sort] order 0)) inner)
        (natMaxSelf order)).symm) identityBaseDisjunction
  }
  let consequenceEquality := MixedOrder.ternaryOrderCombine
    pairNegation .pr .pr
  let outerEquality := Eq.trans
    (congrArg (fun inner => max
      (pairNegation.order MixedOrder.TernarySupport.qr) inner)
      consequenceEquality)
    (MixedOrder.ternaryOrderCombine pairNegation .qr .pr)
  have line1 := star_13_101 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation resultNegation
    reducibilityDisjunction identityOrderDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction scopeUniversal scopeNegation scopeDisjunction
    existentialTargetDisjunction psi x y
  have line2a := star_13_101 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation resultNegation
    reducibilityDisjunction identityOrderDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction scopeUniversal scopeNegation scopeDisjunction
    existentialTargetDisjunction (Formula.neg vocabulary.negation psi) x y
  have line2b : ⊢ᵣ mixedImplication identityNegation
      identityBaseDisjunction identity
      (implication vocabulary.negation vocabulary.disjunction
        (Formula.neg vocabulary.negation psiX)
        (Formula.neg vocabulary.negation psiY)) := by
    unfold star_13_101_reading star_13_101_formula
      star13_101_formulaCore at line2a
    unfold identity psiX psiY
    exact line2a
  have line2c := star_2_17 vocabulary.negation vocabulary.disjunction psiY psiX
  have line2d := star13_exposeSameImplication vocabulary.negation
    vocabulary.disjunction
    (implication vocabulary.negation vocabulary.disjunction
      (Formula.neg vocabulary.negation psiX)
      (Formula.neg vocabulary.negation psiY)) reverse line2c
  have line2 := star13_mixedSyll pairNegation.p pairDisjunction.p
    pairNegation.r pairDisjunction.pr pairDisjunction.qr
    pairDisjunction.pr pairNegation.qr pairNegation.pr
    (Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      pairDisjunction.pr)
    (Eq.mp (congrArg signature.Disjunction outerEquality.symm)
      pairDisjunction.pqr)
    identity
    (implication vocabulary.negation vocabulary.disjunction
      (Formula.neg vocabulary.negation psiX)
      (Formula.neg vocabulary.negation psiY))
    reverse line2b line2d
  have line3 := star13_ramifiedPairUnder pairNegation pairDisjunction
    identity psiX forward reverse line1 line2
  change ⊢ᵣ star_13_12_formula vocabulary identityNegation
    identityBaseDisjunction psi x y
  unfold star_13_12_formula
  exact line3

/-- Object formula asserted at ✱13·13.  Its mixed-order conjunction is
the literal interpretation of `ψx . x = y`, in that printed order. -/
def star_13_13_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (max (bindOrder order (.function [sort] order 0)) order) :=
  let identityOrder := bindOrder order (.function [sort] order 0)
  let identity := star_13_01 vocabulary x y
  let psiX := psi.instantiate x
  let psiY := psi.instantiate y
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm) identityBaseNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm) identityBaseDisjunction
  }
  star13_bridgeInterpret negation disjunction identity identity
    psiX psiY psiX psiY star13_13_targetElement

/-- Audited scope reading of ✱13·13. -/
def star_13_13_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : ψx . x = y .⊃ . ψy"
  parsed := .assertion (star_13_13_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    psi x y)

/-- ✱13·13, by the printed `✱13·101 . Comm . Imp` chain.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_13
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation
      (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction
      (bindOrder order sort))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (scopeUniversal : signature.Universal (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (scopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (scopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Derivation (star_13_13_reading vocabulary identityNegation
      identityOrderDisjunction identityBaseNegation
      identityBaseDisjunction psi x y).parsed := by
  let identityOrder := bindOrder order (.function [sort] order 0)
  let identity := star_13_01 vocabulary x y
  let psiX := psi.instantiate x
  let psiY := psi.instantiate y
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm) identityBaseNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm) identityBaseDisjunction
  }
  have line1 := star_13_101 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation resultNegation
    reducibilityDisjunction identityOrderDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction scopeUniversal scopeNegation scopeDisjunction
    existentialTargetDisjunction psi x y
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    identity identity psiX psiY psiX psiY star13_13_sourceElement at line1
  have line2 := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => identity)
    star13_bridgeSupport
    (star13_bridgeValuation negation identity identity
      psiX psiY psiX psiY)
    star13_elementaryCommImp
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    identity identity psiX psiY psiX psiY star13_13_bridgeElement at line2
  have line3 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      identity identity psiX psiY psiX psiY star13_13_sourceElement)
    (star13_bridgeInterpret negation disjunction
      identity identity psiX psiY psiX psiY star13_13_targetElement)
    line1 line2
  change ⊢ᵣ star_13_13_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    psi x y
  unfold star_13_13_formula
  exact line3

/-- Audited scope reading of ✱13·16. -/
def star_13_16_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y .≡ . y = x"
  parsed := .assertion (star_4_01 negation disjunction
    (star_13_01 vocabulary x y) (star_13_01 vocabulary y x))

/-- ✱13·16, by the printed `✱13·11 . ✱10·32` citation.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_16
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction
      (bindOrder order sort))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (equivalenceScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order (.function [sort] order 0)) order))
    (symmetryScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (bindOrder order (.function [sort] order 0)))
    (scopedNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order)
        (.function [sort] order 0)))
    (scopedConsequenceDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order)
          (.function [sort] order 0))
        (bindOrder order (.function [sort] order 0))))
    (scopedOuterDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0))
        (max
          (bindOrder
            (max (bindOrder order (.function [sort] order 0)) order)
            (.function [sort] order 0))
          (bindOrder order (.function [sort] order 0)))))
    (x y : Term signature real [] sort) :
    Derivation
      (star_13_16_reading vocabulary identityNegation identityDisjunction x y).parsed := by
  let functionSort : RSort := .function [sort] order 0
  let predicate : Term signature real [functionSort] functionSort :=
    .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let identityXY := star_13_01 vocabulary x y
  let identityYX := star_13_01 vocabulary y x
  let formalXY := star_13_11_right vocabulary x y
  let formalYX := star_13_11_right vocabulary y x
  have line1 := star_13_11 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityDisjunction
    identityBaseDisjunction reducibilityNegation
    reducibilityIdentityNegation reducibilityBaseNegation
    identityBaseNegation resultNegation reducibilityDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction
    equivalenceScopeUniversal scopedNegation scopedConsequenceDisjunction
    scopedOuterDisjunction x y
  change ⊢ᵣ star_4_01 identityNegation identityDisjunction
    identityXY formalXY at line1
  have line2 := star_10_32 vocabulary.universal symmetryScopeUniversal
    vocabulary.negation vocabulary.disjunction identityNegation
    identityDisjunction phiX phiY
  change ⊢ᵣ star_4_01 identityNegation identityDisjunction
    formalXY formalYX at line2
  have line3 := star_13_11 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityDisjunction
    identityBaseDisjunction reducibilityNegation
    reducibilityIdentityNegation reducibilityBaseNegation
    identityBaseNegation resultNegation reducibilityDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction
    equivalenceScopeUniversal scopedNegation scopedConsequenceDisjunction
    scopedOuterDisjunction y x
  change ⊢ᵣ star_4_01 identityNegation identityDisjunction
    identityYX formalYX at line3
  have line4 := star_10_13 identityNegation identityDisjunction
    (star_4_01 identityNegation identityDisjunction identityXY formalXY)
    (star_4_01 identityNegation identityDisjunction formalXY formalYX)
    line1 line2
  unfold star_10_13_reading at line4
  have line5 := star13_detach identityNegation identityDisjunction _ _ line4
    (star_4_22 identityNegation identityDisjunction identityXY formalXY formalYX)
  have line6 := star_4_21 identityNegation identityDisjunction
    identityYX formalYX
  change ⊢ᵣ conjunction identityNegation identityDisjunction
    (implication identityNegation identityDisjunction
      (star_4_01 identityNegation identityDisjunction identityYX formalYX)
      (star_4_01 identityNegation identityDisjunction formalYX identityYX))
    (implication identityNegation identityDisjunction
      (star_4_01 identityNegation identityDisjunction formalYX identityYX)
      (star_4_01 identityNegation identityDisjunction identityYX formalYX))
    at line6
  have line7 := star13_detach identityNegation identityDisjunction _ _ line6
    (star_3_26 identityNegation identityDisjunction
      (implication identityNegation identityDisjunction
        (star_4_01 identityNegation identityDisjunction identityYX formalYX)
        (star_4_01 identityNegation identityDisjunction formalYX identityYX))
      (implication identityNegation identityDisjunction
        (star_4_01 identityNegation identityDisjunction formalYX identityYX)
        (star_4_01 identityNegation identityDisjunction identityYX formalYX)))
  have line8 := star13_detach identityNegation identityDisjunction _ _ line3 line7
  have line9 := star_10_13 identityNegation identityDisjunction
    (star_4_01 identityNegation identityDisjunction identityXY formalYX)
    (star_4_01 identityNegation identityDisjunction formalYX identityYX)
    line5 line8
  unfold star_10_13_reading at line9
  have line10 := star13_detach identityNegation identityDisjunction _ _ line9
    (star_4_22 identityNegation identityDisjunction identityXY formalYX identityYX)
  unfold star_13_16_reading
  exact line10

/-- Audited scope reading of ✱13·17. -/
def star_13_17_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y z : Term signature real [] sort) : ClaimReading signature real :=
  let predicate : Term signature real
      [.function [sort] order excess]
      (.function [sort] order excess) := .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let phiZ := applyUnary predicate z.weaken
  {
    printed := "⊢ : x = y . y = z .⊃ . x = z"
    parsed := .assertion (star13_star_10_3_formula vocabulary.universal
      vocabulary.negation vocabulary.disjunction phiX phiY phiZ)
  }

/-- ✱13·17, following the printed ✱13·1, ✱10·3 chain.  Unfolding the
Leibniz definition turns the assertion into the full-scope `Syll` matrix;
✱10·11 then generalizes over the same bound propositional function.
`demonstration_provenance: follows-printed`. -/
theorem star_13_17
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y z : Term signature real [] sort) :
    Derivation (star_13_17_reading vocabulary x y z).parsed := by
  let predicate : Term signature real
      [.function [sort] order excess]
      (.function [sort] order excess) := .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let phiZ := applyUnary predicate z.weaken
  have line1 := star13_star_10_3 vocabulary.universal vocabulary.negation
    vocabulary.disjunction phiX phiY phiZ
  exact line1

/-- The full-scope form of ✱13·17 converted to the displayed implication
between three Leibniz identities. -/
private theorem star13_directTransitivity
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (scopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order (.function [sort] order 0)) order))
    (scopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order)
        (.function [sort] order 0)))
    (scopeConsequenceDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order)
          (.function [sort] order 0))
        (bindOrder order (.function [sort] order 0))))
    (scopeOuterDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0))
        (max
          (bindOrder
            (max (bindOrder order (.function [sort] order 0)) order)
            (.function [sort] order 0))
          (bindOrder order (.function [sort] order 0)))))
    (x y z : Term signature real [] sort) :
    ⊢ᵣ implication identityNegation identityDisjunction
      (conjunction identityNegation identityDisjunction
        (star_13_01 vocabulary x y) (star_13_01 vocabulary y z))
      (star_13_01 vocabulary x z) := by
  let functionSort : RSort := .function [sort] order 0
  let identityXY := star_13_01 vocabulary x y
  let identityYZ := star_13_01 vocabulary y z
  let identityXZ := star_13_01 vocabulary x z
  let source := conjunction identityNegation identityDisjunction
    identityXY identityYZ
  let predicate : Term signature real [functionSort] functionSort :=
    .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let phiZ := applyUnary predicate z.weaken
  let weakPredicate : Term signature (functionSort :: real)
      [functionSort] functionSort := .apparent .zero
  let weakPhiX := applyUnary weakPredicate
    (x.weakenReal (fresh := functionSort)).weaken
  let weakPhiY := applyUnary weakPredicate
    (y.weakenReal (fresh := functionSort)).weaken
  let weakPhiZ := applyUnary weakPredicate
    (z.weakenReal (fresh := functionSort)).weaken
  let value : Term signature (functionSort :: real) [] functionSort :=
    .real .zero
  let pointXY := (implication vocabulary.negation vocabulary.disjunction
    weakPhiX weakPhiY).instantiate value
  let pointYZ := (implication vocabulary.negation vocabulary.disjunction
    weakPhiY weakPhiZ).instantiate value
  let pointXZ := (implication vocabulary.negation vocabulary.disjunction
    weakPhiX weakPhiZ).instantiate value
  let pointSource := conjunction vocabulary.negation vocabulary.disjunction
    pointXY pointYZ
  let weakSourceBody := implication vocabulary.negation vocabulary.disjunction
    (star13_apparentConjunction vocabulary.negation vocabulary.disjunction
      (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiY)
      (implication vocabulary.negation vocabulary.disjunction weakPhiY weakPhiZ))
    (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiZ)
  have line1 := star_13_17 (real := functionSort :: real) vocabulary
    (x.weakenReal (fresh := functionSort))
    (y.weakenReal (fresh := functionSort))
    (z.weakenReal (fresh := functionSort))
  change ⊢ᵣ Formula.always vocabulary.universal weakSourceBody at line1
  have line2 := Derivation.star_10_1 vocabulary.universal identityNegation
    identityBaseDisjunction weakSourceBody value
  have line3 := star13_mixedDetach identityNegation identityBaseDisjunction
    (.always vocabulary.universal weakSourceBody)
    (weakSourceBody.instantiate value) line1 line2
  have line4 : weakSourceBody.instantiate value =
      implication vocabulary.negation vocabulary.disjunction
        pointSource pointXZ := by
    unfold weakSourceBody pointSource pointXY pointYZ pointXZ
    rw [Formula.instantiate, implication_substitute,
      star13_apparentConjunction_substitute]
    rfl
  have line5 := Derivation.castAssertion line4.symm line3
  let weakBodyXY := implication vocabulary.negation vocabulary.disjunction
    weakPhiX weakPhiY
  have line6 := Derivation.star_10_1 vocabulary.universal identityNegation
    identityBaseDisjunction weakBodyXY value
  have line7 : (identityXY.weakenReal (fresh := functionSort)) =
      .always vocabulary.universal weakBodyXY := by
    unfold identityXY
    rw [star13_identity_weakenReal]
    unfold star_13_01 weakBodyXY weakPhiX weakPhiY weakPredicate
    rfl
  have line8 : weakBodyXY.instantiate value = pointXY := by
    unfold weakBodyXY pointXY
    rfl
  have line9 : ⊢ᵣ mixedImplication identityNegation
      identityBaseDisjunction
        (identityXY.weakenReal (fresh := functionSort)) pointXY := by
    rw [line7]
    exact line6
  let weakBodyYZ := implication vocabulary.negation vocabulary.disjunction
    weakPhiY weakPhiZ
  have line10 := Derivation.star_10_1 vocabulary.universal identityNegation
    identityBaseDisjunction weakBodyYZ value
  have line11 : (identityYZ.weakenReal (fresh := functionSort)) =
      .always vocabulary.universal weakBodyYZ := by
    unfold identityYZ
    rw [star13_identity_weakenReal]
    unfold star_13_01 weakBodyYZ weakPhiY weakPhiZ weakPredicate
    rfl
  have line12 : weakBodyYZ.instantiate value = pointYZ := by
    unfold weakBodyYZ pointYZ
    rfl
  have line13 : ⊢ᵣ mixedImplication identityNegation
      identityBaseDisjunction
        (identityYZ.weakenReal (fresh := functionSort)) pointYZ := by
    rw [line11]
    exact line10
  let weakSource := conjunction identityNegation identityDisjunction
    (identityXY.weakenReal (fresh := functionSort))
    (identityYZ.weakenReal (fresh := functionSort))
  have line14 : (source.weakenReal (fresh := functionSort)) = weakSource := by
    unfold source weakSource conjunction
    change Formula.neg identityNegation
      ((sameDisjunction identityDisjunction
        (.neg identityNegation identityXY)
        (.neg identityNegation identityYZ)).weakenReal) = _
    rw [sameDisjunction_weakenReal]
    rfl
  let pairNegation : MixedOrder.TernaryNegations signature := {
    pOrder := bindOrder order functionSort
    qOrder := bindOrder order functionSort
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf (bindOrder order functionSort)).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb (bindOrder order functionSort) order).symm)
      identityBaseNegation
  }
  let pairDisjunction : MixedOrder.TernaryDisjunctions signature
      pairNegation := {
    p := identityDisjunction
    q := identityDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf (bindOrder order functionSort)).symm) identityDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb (bindOrder order functionSort) order).symm)
      identityBaseDisjunction
  }
  let pairConsequenceEquality := MixedOrder.ternaryOrderCombine
    pairNegation .pq .pr
  let pairOuterEquality := Eq.trans
    (congrArg (fun inner => max
      (pairNegation.order MixedOrder.TernarySupport.qr) inner)
      pairConsequenceEquality)
    (MixedOrder.ternaryOrderCombine pairNegation .qr .pqr)
  have line15 := star_3_26 identityNegation identityDisjunction
    (identityXY.weakenReal (fresh := functionSort))
    (identityYZ.weakenReal (fresh := functionSort))
  change ⊢ᵣ implication identityNegation identityDisjunction
    weakSource (identityXY.weakenReal (fresh := functionSort)) at line15
  have line16 := star13_exposeSameImplication identityNegation
    identityDisjunction weakSource
      (identityXY.weakenReal (fresh := functionSort)) line15
  change ⊢ᵣ mixedImplication pairNegation.p pairDisjunction.pq
    weakSource (identityXY.weakenReal (fresh := functionSort)) at line16
  change ⊢ᵣ mixedImplication pairNegation.q pairDisjunction.qr
    (identityXY.weakenReal (fresh := functionSort)) pointXY at line9
  have line17 := star13_mixedSyll pairNegation.p pairDisjunction.p
    pairNegation.q pairDisjunction.pq pairDisjunction.qr
    pairDisjunction.pr pairNegation.qr pairNegation.pq
    (Eq.mp (congrArg signature.Disjunction pairConsequenceEquality.symm)
      pairDisjunction.pqr)
    (Eq.mp (congrArg signature.Disjunction pairOuterEquality.symm)
      pairDisjunction.pqr)
    weakSource (identityXY.weakenReal (fresh := functionSort))
    pointXY line16 line9
  have line18 := star_3_27 identityNegation identityDisjunction
    (identityXY.weakenReal (fresh := functionSort))
    (identityYZ.weakenReal (fresh := functionSort))
  change ⊢ᵣ implication identityNegation identityDisjunction
    weakSource (identityYZ.weakenReal (fresh := functionSort)) at line18
  have line19 := star13_exposeSameImplication identityNegation
    identityDisjunction weakSource
      (identityYZ.weakenReal (fresh := functionSort)) line18
  change ⊢ᵣ mixedImplication pairNegation.p pairDisjunction.pq
    weakSource (identityYZ.weakenReal (fresh := functionSort)) at line19
  change ⊢ᵣ mixedImplication pairNegation.q pairDisjunction.qr
    (identityYZ.weakenReal (fresh := functionSort)) pointYZ at line13
  have line20 := star13_mixedSyll pairNegation.p pairDisjunction.p
    pairNegation.q pairDisjunction.pq pairDisjunction.qr
    pairDisjunction.pr pairNegation.qr pairNegation.pq
    (Eq.mp (congrArg signature.Disjunction pairConsequenceEquality.symm)
      pairDisjunction.pqr)
    (Eq.mp (congrArg signature.Disjunction pairOuterEquality.symm)
      pairDisjunction.pqr)
    weakSource (identityYZ.weakenReal (fresh := functionSort))
    pointYZ line19 line13
  have line21 := star13_ramifiedPairUnder pairNegation pairDisjunction
    weakSource (identityXY.weakenReal (fresh := functionSort))
    pointXY pointYZ line17 line20
  let syllNegation : MixedOrder.TernaryNegations signature := {
    pOrder := bindOrder order functionSort
    qOrder := order
    rOrder := order
    p := identityNegation
    q := vocabulary.negation
    r := vocabulary.negation
    pq := identityBaseNegation
    pr := identityBaseNegation
    qr := Eq.mp (congrArg signature.Negation
      (natMaxSelf order).symm) vocabulary.negation
    pqr := Eq.mp (congrArg signature.Negation
      (congrArg (fun inner => max (bindOrder order functionSort) inner)
        (natMaxSelf order)).symm)
      identityBaseNegation
  }
  let syllDisjunction : MixedOrder.TernaryDisjunctions signature
      syllNegation := {
    p := identityDisjunction
    q := vocabulary.disjunction
    r := vocabulary.disjunction
    pq := identityBaseDisjunction
    pr := identityBaseDisjunction
    qr := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf order).symm) vocabulary.disjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (congrArg (fun inner => max (bindOrder order functionSort) inner)
        (natMaxSelf order)).symm)
      identityBaseDisjunction
  }
  let syllConsequenceEquality := MixedOrder.ternaryOrderCombine
    syllNegation .pq .pr
  let syllOuterEquality := Eq.trans
    (congrArg (fun inner => max
      (syllNegation.order MixedOrder.TernarySupport.qr) inner)
      syllConsequenceEquality)
    (MixedOrder.ternaryOrderCombine syllNegation .qr .pqr)
  change ⊢ᵣ mixedImplication syllNegation.p syllDisjunction.pq
    weakSource pointSource at line21
  change ⊢ᵣ implication vocabulary.negation vocabulary.disjunction
    pointSource pointXZ at line5
  have line22 := star13_exposeSameImplication vocabulary.negation
    vocabulary.disjunction pointSource pointXZ line5
  change ⊢ᵣ mixedImplication syllNegation.q syllDisjunction.qr
    pointSource pointXZ at line22
  have line23 := star13_mixedSyll syllNegation.p syllDisjunction.p
    syllNegation.q syllDisjunction.pq syllDisjunction.qr
    syllDisjunction.pr syllNegation.qr syllNegation.pq
    (Eq.mp (congrArg signature.Disjunction syllConsequenceEquality.symm)
      syllDisjunction.pqr)
    (Eq.mp (congrArg signature.Disjunction syllOuterEquality.symm)
      syllDisjunction.pqr)
    weakSource pointSource pointXZ line21 line22
  let scopeBody := mixedImplication identityNegation identityBaseDisjunction
    (source.rename (fun v => .succ v))
    (implication vocabulary.negation vocabulary.disjunction phiX phiZ)
  have line24 : (scopeBody.weakenReal (fresh := functionSort)).instantiate value =
      mixedImplication identityNegation identityBaseDisjunction
        weakSource pointXZ := by
    unfold scopeBody pointXZ phiX phiZ predicate
    rw [star13_mixedImplication_weakenReal,
      star13_mixedImplication_instantiate,
      Formula.closed_weakenReal_instantiate, line14]
    rw [implication_weakenReal, Formula.instantiate,
      implication_substitute]
    rw [Formula.instantiate, implication_substitute]
    cases x <;> cases z <;> rfl
  have line25 : ⊢ᵣ
      (scopeBody.weakenReal (fresh := functionSort)).instantiate value := by
    exact Derivation.castAssertion line24 line23
  have line26 : ⊢ᵣ Formula.always scopeUniversal scopeBody := by
    exact star_10_11 scopeUniversal scopeBody line25
  have line27 : ImplicationDisjunction signature real
      (Formula.neg identityNegation source) identityXZ
      (.always scopeUniversal scopeBody) := by
    unfold identityXZ star_13_01 scopeBody
    apply ImplicationDisjunction.star_9_04 vocabulary.universal scopeUniversal
    exact ImplicationDisjunction.star_1_01 identityBaseDisjunction
      ((Formula.neg identityNegation source).rename (fun v => .succ v))
      (implication vocabulary.negation vocabulary.disjunction phiX phiZ)
  have line28 := star13_canonicalizeSameOrderImplication identityNegation
    identityDisjunction scopeNegation scopeConsequenceDisjunction
    scopeOuterDisjunction source identityXZ
    (.always scopeUniversal scopeBody) line27 line26
  change ⊢ᵣ implication identityNegation identityDisjunction
    source identityXZ at line28
  exact line28

/-- Audited scope reading of ✱13·171. -/
def star_13_171_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (x y z : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y . x = z .⊃ . y = z"
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction
      (star_13_01 vocabulary x y) (star_13_01 vocabulary x z))
    (star_13_01 vocabulary y z))

/-- ✱13·171, by the printed `✱13·16·17` citation.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_171
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction
      (bindOrder order sort))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (equivalenceScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order (.function [sort] order 0)) order))
    (symmetryScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (bindOrder order (.function [sort] order 0)))
    (scopedNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order)
        (.function [sort] order 0)))
    (scopedConsequenceDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order)
          (.function [sort] order 0))
        (bindOrder order (.function [sort] order 0))))
    (scopedOuterDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0))
        (max
          (bindOrder
            (max (bindOrder order (.function [sort] order 0)) order)
            (.function [sort] order 0))
          (bindOrder order (.function [sort] order 0)))))
    (x y z : Term signature real [] sort) :
    Derivation
      (star_13_171_reading vocabulary identityNegation
        identityDisjunction x y z).parsed := by
  let identityXY := star_13_01 vocabulary x y
  let identityYX := star_13_01 vocabulary y x
  let identityXZ := star_13_01 vocabulary x z
  let identityYZ := star_13_01 vocabulary y z
  let source := conjunction identityNegation identityDisjunction
    identityXY identityXZ
  let middle := conjunction identityNegation identityDisjunction
    identityYX identityXZ
  have line1 := star_13_16 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityDisjunction
    identityBaseDisjunction reducibilityNegation
    reducibilityIdentityNegation reducibilityBaseNegation
    identityBaseNegation resultNegation reducibilityDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction
    equivalenceScopeUniversal symmetryScopeUniversal scopedNegation
    scopedConsequenceDisjunction scopedOuterDisjunction x y
  unfold star_13_16_reading star_4_01 at line1
  have line2 := star13_directTransitivity vocabulary identityNegation
    identityDisjunction identityBaseNegation identityBaseDisjunction
    equivalenceScopeUniversal scopedNegation scopedConsequenceDisjunction
    scopedOuterDisjunction y x z
  have line3 := star13_detach identityNegation identityDisjunction _ _ line1
    (star_3_26 identityNegation identityDisjunction
      (implication identityNegation identityDisjunction identityXY identityYX)
      (implication identityNegation identityDisjunction identityYX identityXY))
  have line4 := star_3_45 identityNegation identityDisjunction
    identityXY identityYX identityXZ
  have line5 := star13_detach identityNegation identityDisjunction _ _ line3 line4
  change ⊢ᵣ implication identityNegation identityDisjunction
    middle identityYZ at line2
  change ⊢ᵣ implication identityNegation identityDisjunction
    source middle at line5
  have line6 := star13_detach identityNegation identityDisjunction _ _ line2
    (star_2_05 identityNegation identityDisjunction source middle identityYZ)
  have line7 := star13_detach identityNegation identityDisjunction _ _ line5 line6
  unfold star_13_171_reading
  exact line7

/-- Audited scope reading of ✱13·18. -/
def star_13_18_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y z : Term signature real [] sort) : ClaimReading signature real :=
  let predicate : Term signature real
      [.function [sort] order excess]
      (.function [sort] order excess) := .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let phiZ := applyUnary predicate z.weaken
  {
    printed := "⊢ : x = y . x ≠ z .⊃ . y ≠ z"
    parsed := .assertion (.always vocabulary.universal
      (implication vocabulary.negation vocabulary.disjunction
        (star13_apparentConjunction vocabulary.negation
          vocabulary.disjunction
          (implication vocabulary.negation vocabulary.disjunction phiX phiY)
          (.neg vocabulary.negation
            (implication vocabulary.negation vocabulary.disjunction phiX phiZ)))
        (.neg vocabulary.negation
          (implication vocabulary.negation vocabulary.disjunction phiY phiZ))))
  }

/-- ✱13·18, by the printed `✱13·17 . ✱4·14` citation.
`demonstration_provenance: follows-printed`. -/
theorem star_13_18
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order excess)) order))
    (x y z : Term signature real [] sort) :
    Derivation
      (star_13_18_reading vocabulary x y z).parsed := by
  let functionSort : RSort := .function [sort] order excess
  let identityOrder := bindOrder order functionSort
  let predicate : Term signature real [functionSort] functionSort :=
    .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let phiZ := applyUnary predicate z.weaken
  let weakPredicate : Term signature (functionSort :: real)
      [functionSort] functionSort := .apparent .zero
  let weakPhiX := applyUnary weakPredicate
    (x.weakenReal (fresh := functionSort)).weaken
  let weakPhiY := applyUnary weakPredicate
    (y.weakenReal (fresh := functionSort)).weaken
  let weakPhiZ := applyUnary weakPredicate
    (z.weakenReal (fresh := functionSort)).weaken
  let weakSourceBody := implication vocabulary.negation vocabulary.disjunction
    (star13_apparentConjunction vocabulary.negation vocabulary.disjunction
      (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiY)
      (implication vocabulary.negation vocabulary.disjunction weakPhiY weakPhiZ))
    (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiZ)
  let targetBody := implication vocabulary.negation vocabulary.disjunction
    (star13_apparentConjunction vocabulary.negation vocabulary.disjunction
      (implication vocabulary.negation vocabulary.disjunction phiX phiY)
      (.neg vocabulary.negation
        (implication vocabulary.negation vocabulary.disjunction phiX phiZ)))
    (.neg vocabulary.negation
      (implication vocabulary.negation vocabulary.disjunction phiY phiZ))
  let value : Term signature (functionSort :: real) [] functionSort :=
    .real .zero
  have line1a := star_13_17 (real := functionSort :: real) vocabulary
    (x.weakenReal (fresh := functionSort))
    (y.weakenReal (fresh := functionSort))
    (z.weakenReal (fresh := functionSort))
  change ⊢ᵣ Formula.always vocabulary.universal weakSourceBody at line1a
  have line1b := Derivation.star_10_1 vocabulary.universal negation
    disjunction weakSourceBody value
  have line1 := star13_mixedDetach negation disjunction
    (.always vocabulary.universal weakSourceBody)
    (weakSourceBody.instantiate value) line1a line1b
  let pointXY :=
    (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiY).instantiate value
  let pointYZ :=
    (implication vocabulary.negation vocabulary.disjunction weakPhiY weakPhiZ).instantiate value
  let pointXZ :=
    (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiZ).instantiate value
  let sourcePoint := implication vocabulary.negation vocabulary.disjunction
    (conjunction vocabulary.negation vocabulary.disjunction pointXY pointYZ) pointXZ
  let targetPoint := implication vocabulary.negation vocabulary.disjunction
    (conjunction vocabulary.negation vocabulary.disjunction pointXY
      (.neg vocabulary.negation pointXZ))
    (.neg vocabulary.negation pointYZ)
  have line1Equality : weakSourceBody.instantiate value = sourcePoint := by
    unfold weakSourceBody sourcePoint pointXY pointYZ pointXZ
    rw [Formula.instantiate, implication_substitute,
      star13_apparentConjunction_substitute]
    rfl
  have line1' := Derivation.castAssertion line1Equality.symm line1
  have line2a := star_4_14 vocabulary.negation vocabulary.disjunction
    pointXY pointYZ pointXZ
  have line2b := star_3_26 (real := functionSort :: real)
    vocabulary.negation vocabulary.disjunction
    (implication vocabulary.negation vocabulary.disjunction sourcePoint targetPoint)
    (implication vocabulary.negation vocabulary.disjunction targetPoint sourcePoint)
  have line2c := star13_detach vocabulary.negation vocabulary.disjunction
    (star_4_01 vocabulary.negation vocabulary.disjunction sourcePoint targetPoint)
    (implication vocabulary.negation vocabulary.disjunction sourcePoint targetPoint)
    line2a line2b
  have line2d := star13_detach vocabulary.negation vocabulary.disjunction
    sourcePoint targetPoint line1' line2c
  have line2e :
      (implication vocabulary.negation vocabulary.disjunction phiX phiY).weakenReal
        (fresh := functionSort) =
      implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiY := by
    rw [implication_weakenReal]
    unfold phiX phiY predicate weakPhiX weakPhiY weakPredicate
    cases x <;> cases y <;> rfl
  have line2f :
      (implication vocabulary.negation vocabulary.disjunction phiX phiZ).weakenReal
        (fresh := functionSort) =
      implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiZ := by
    rw [implication_weakenReal]
    unfold phiX phiZ predicate weakPhiX weakPhiZ weakPredicate
    cases x <;> cases z <;> rfl
  have line2g :
      (implication vocabulary.negation vocabulary.disjunction phiY phiZ).weakenReal
        (fresh := functionSort) =
      implication vocabulary.negation vocabulary.disjunction weakPhiY weakPhiZ := by
    rw [implication_weakenReal]
    unfold phiY phiZ predicate weakPhiY weakPhiZ weakPredicate
    cases y <;> cases z <;> rfl
  let weakTargetBody := implication vocabulary.negation vocabulary.disjunction
    (star13_apparentConjunction vocabulary.negation vocabulary.disjunction
      (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiY)
      (.neg vocabulary.negation
        (implication vocabulary.negation vocabulary.disjunction weakPhiX weakPhiZ)))
    (.neg vocabulary.negation
      (implication vocabulary.negation vocabulary.disjunction weakPhiY weakPhiZ))
  have line2h : targetBody.weakenReal = weakTargetBody := by
    unfold targetBody weakTargetBody
    rw [implication_weakenReal, star13_apparentConjunction_weakenReal]
    change implication vocabulary.negation vocabulary.disjunction
      (star13_apparentConjunction vocabulary.negation vocabulary.disjunction
        ((implication vocabulary.negation vocabulary.disjunction phiX phiY).weakenReal)
        (.neg vocabulary.negation
          ((implication vocabulary.negation vocabulary.disjunction phiX phiZ).weakenReal)))
      (.neg vocabulary.negation
        ((implication vocabulary.negation vocabulary.disjunction phiY phiZ).weakenReal)) = _
    rw [line2e, line2f, line2g]
  have line2Equality : targetBody.weakenReal.instantiate value = targetPoint := by
    rw [line2h]
    unfold weakTargetBody targetPoint pointXY pointYZ pointXZ
    rw [Formula.instantiate, implication_substitute,
      star13_apparentConjunction_substitute]
    change implication vocabulary.negation vocabulary.disjunction
      (star13_apparentConjunction vocabulary.negation vocabulary.disjunction
        ((implication vocabulary.negation vocabulary.disjunction
          weakPhiX weakPhiY).instantiate value)
        (.neg vocabulary.negation
          ((implication vocabulary.negation vocabulary.disjunction
            weakPhiX weakPhiZ).instantiate value)))
      (.neg vocabulary.negation
        ((implication vocabulary.negation vocabulary.disjunction
          weakPhiY weakPhiZ).instantiate value)) = _
    rfl
  have line2 := Derivation.castAssertion line2Equality line2d
  exact star_10_11 vocabulary.universal targetBody line2

/-- Audited scope reading of ✱13·181. -/
def star_13_181_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (x y z : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y . y ≠ z .⊃ . x ≠ z"
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction
      (star_13_01 vocabulary x y)
      (star_13_02 vocabulary negation y z))
    (star_13_02 vocabulary negation x z))

/-- ✱13·181, by the printed `✱13·171 . ✱4·14` citation.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_181
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (resultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction
      (bindOrder order sort))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (resultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (equivalenceScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order (.function [sort] order 0)) order))
    (symmetryScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (bindOrder order (.function [sort] order 0)))
    (scopedNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order)
        (.function [sort] order 0)))
    (scopedConsequenceDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order)
          (.function [sort] order 0))
        (bindOrder order (.function [sort] order 0))))
    (scopedOuterDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0))
        (max
          (bindOrder
            (max (bindOrder order (.function [sort] order 0)) order)
            (.function [sort] order 0))
          (bindOrder order (.function [sort] order 0)))))
    (x y z : Term signature real [] sort) :
    Derivation
      (star_13_181_reading vocabulary identityNegation
        identityDisjunction x y z).parsed := by
  let identityXY := star_13_01 vocabulary x y
  let identityXZ := star_13_01 vocabulary x z
  let identityYZ := star_13_01 vocabulary y z
  let source := implication identityNegation identityDisjunction
    (conjunction identityNegation identityDisjunction identityXY identityXZ)
    identityYZ
  let target := implication identityNegation identityDisjunction
    (conjunction identityNegation identityDisjunction identityXY
      (Formula.neg identityNegation identityYZ))
    (Formula.neg identityNegation identityXZ)
  have line1 := star_13_171 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityDisjunction
    identityBaseDisjunction reducibilityNegation
    reducibilityIdentityNegation reducibilityBaseNegation
    identityBaseNegation resultNegation reducibilityDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    resultDisjunction reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction
    equivalenceScopeUniversal symmetryScopeUniversal scopedNegation
    scopedConsequenceDisjunction scopedOuterDisjunction x y z
  change ⊢ᵣ source at line1
  have line2 := star_4_14 identityNegation identityDisjunction
    identityXY identityXZ identityYZ
  unfold star_4_01 at line2
  have line3 := star13_detach identityNegation identityDisjunction _ _ line2
    (star_3_26 identityNegation identityDisjunction
      (implication identityNegation identityDisjunction source target)
      (implication identityNegation identityDisjunction target source))
  have line4 := star13_detach identityNegation identityDisjunction
    source target line1 line3
  unfold star_13_181_reading star_13_02
  exact line4

/-- Audited scope reading of ✱13·19. -/
def star_13_19_reading
    (existential : ExistentialVocabulary signature sort
      (bindOrder order (.function [sort] order excess)))
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ . (∃y). y = x"
  parsed := .assertion (.sometimes existential
    (star_13_01 vocabulary
      (.apparent (.zero : Var [sort] sort)) x.weaken))

/-- ✱13·19, following the printed ✱13·15, ✱10·24 citation.  The
specialization equation below only verifies that the displayed witness is
exactly `x`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_19
    (existential : ExistentialVocabulary signature sort
      (bindOrder order (.function [sort] order excess)))
    (vocabulary : IdentityVocabulary signature sort order excess)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (existentialDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order excess))
        (bindOrder (bindOrder order (.function [sort] order excess)) sort)))
    (x : Term signature real [] sort) :
    Derivation (star_13_19_reading existential vocabulary x).parsed := by
  let body := star_13_01 vocabulary
    (.apparent (.zero : Var [sort] sort)) x.weaken
  have line1 := star_13_15 vocabulary identityNegation
    identityDisjunction x
  have line2 := star_10_24 existential identityNegation
    existentialDisjunction body x
  have bodyEq : body.instantiate x = star_13_01 vocabulary x x := by
    unfold body star_13_01
    rw [Formula.instantiate, substitute_always, implication_substitute]
    cases x <;> rfl
  have line2' := Derivation.castAssertion
    (congrArg (fun antecedent => mixedImplication identityNegation
      existentialDisjunction antecedent (.sometimes existential body)) bodyEq).symm
    line2
  exact Derivation.star_9_12 identityNegation existentialDisjunction line1 line2'

/-- Object formula asserted at ✱13·191. -/
def star_13_191_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityUniversal : signature.Universal sort
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (scopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (scopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (scopeResultNegation : signature.Negation
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        order))
    (scopeResultDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        order))
    (psi : Formula signature real [sort] order)
    (x : Term signature real [] sort) :=
  let identityOrder := bindOrder order (.function [sort] order 0)
  let matrixOrder := max identityOrder order
  let scopeOrder := bindOrder matrixOrder sort
  let body := mixedImplication identityNegation identityBaseDisjunction
    (star_13_01 vocabulary (.apparent (.zero : Var [sort] sort)) x.weaken)
    psi
  let left := Formula.always identityUniversal body
  let right := psi.instantiate x
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := scopeOrder
    qOrder := order
    rOrder := order
    p := scopeNegation
    q := vocabulary.negation
    r := vocabulary.negation
    pq := scopeResultNegation
    pr := scopeResultNegation
    qr := Eq.mp (congrArg signature.Negation
      (natMaxSelf order).symm) vocabulary.negation
    pqr := Eq.mp (congrArg signature.Negation
      (congrArg (fun inner => max scopeOrder inner)
        (natMaxSelf order)).symm) scopeResultNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := scopeDisjunction
    q := vocabulary.disjunction
    r := vocabulary.disjunction
    pq := scopeResultDisjunction
    pr := scopeResultDisjunction
    qr := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf order).symm) vocabulary.disjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (congrArg (fun inner => max scopeOrder inner)
        (natMaxSelf order)).symm) scopeResultDisjunction
  }
  star13_bridgeInterpret negation disjunction left right
    right right right right star13_equivalenceTargetElement

/-- Audited scope reading of ✱13·191. -/
def star_13_191_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityUniversal : signature.Universal sort
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (scopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (scopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (scopeResultNegation : signature.Negation
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        order))
    (scopeResultDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        order))
    (psi : Formula signature real [sort] order)
    (x : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ :: y = x .⊃y . φy : ≡ . φx"
  parsed := .assertion (star_13_191_formula vocabulary identityUniversal
    identityNegation identityBaseDisjunction scopeNegation scopeDisjunction
    scopeResultNegation scopeResultDisjunction psi x)

/-- ✱13·191, following the two printed lines: specialization with ✱13·15,
then ✱13·12, Comm, generalization and the ✱9·04 reading of ✱10·21.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_191
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityUniversal : signature.Universal sort
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityResultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction (bindOrder order sort))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (reducibilityResultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (scopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (scopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (scopeIdentityNegation : signature.Negation
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        (bindOrder order (.function [sort] order 0))))
    (scopeIdentityDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        (bindOrder order (.function [sort] order 0))))
    (scopeResultNegation : signature.Negation
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        order))
    (scopeResultDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        order))
    (specializationNegation : signature.Negation
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (specializationDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder order (.function [sort] order 0)) order) sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x : Term signature real [] sort) :
    Derivation (star_13_191_reading vocabulary identityUniversal
      identityNegation identityBaseDisjunction scopeNegation scopeDisjunction
      scopeResultNegation scopeResultDisjunction psi x).parsed := by
  let identityOrder := bindOrder order (.function [sort] order 0)
  let matrixOrder := max identityOrder order
  let scopeOrder := bindOrder matrixOrder sort
  let identityBody := mixedImplication identityNegation
    identityBaseDisjunction
    (star_13_01 vocabulary (.apparent (.zero : Var [sort] sort)) x.weaken)
    psi
  let left := Formula.always identityUniversal identityBody
  let phiX := psi.instantiate x
  let forwardNegation : MixedOrder.TernaryNegations signature := {
    pOrder := scopeOrder
    qOrder := identityOrder
    rOrder := order
    p := scopeNegation
    q := identityNegation
    r := vocabulary.negation
    pq := scopeIdentityNegation
    pr := scopeResultNegation
    qr := identityBaseNegation
    pqr := specializationNegation
  }
  let forwardDisjunction : MixedOrder.TernaryDisjunctions signature
      forwardNegation := {
    p := scopeDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := scopeIdentityDisjunction
    pr := scopeResultDisjunction
    qr := identityBaseDisjunction
    pqr := specializationDisjunction
  }
  let identityXX := star_13_01 vocabulary x x
  have line1a := star_10_1 identityUniversal scopeNegation
    specializationDisjunction identityBody x
  have identityBodyAt : identityBody.instantiate x =
      mixedImplication identityNegation identityBaseDisjunction
        identityXX phiX := by
    unfold identityBody identityXX phiX
    rw [star13_mixedImplication_instantiate]
    unfold star_13_01
    rw [Formula.instantiate, substitute_always, implication_substitute]
    cases x <;> rfl
  have line1b : ⊢ᵣ star13_bridgeInterpret forwardNegation
      forwardDisjunction left identityXX phiX phiX phiX phiX
      star13_specializationSourceElement := by
    unfold star_10_1_reading at line1a
    rw [identityBodyAt] at line1a
    exact line1a
  have line1c := star_13_15 vocabulary identityNegation
    identityOrderDisjunction x
  have line1d := MixedOrder.transport MixedOrder.TernarySupport.combine
    forwardNegation.toVocabulary forwardDisjunction.toVocabulary
    (MixedOrder.ternaryTautology forwardNegation forwardDisjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => left)
    star13_bridgeSupport
    (star13_bridgeValuation forwardNegation left identityXX
      phiX phiX phiX phiX)
    star13_elementarySpecializationBridge
  change ⊢ᵣ star13_bridgeInterpret forwardNegation forwardDisjunction
    left identityXX phiX phiX phiX phiX
    star13_specializationBridgeElement at line1d
  have line1e := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine forwardNegation .q .pqr)
    forwardNegation.q forwardDisjunction.pqr identityXX
    (star13_bridgeInterpret forwardNegation forwardDisjunction
      left identityXX phiX phiX phiX phiX
      (star13_specializationSourceElement ⊃ₚ
        star13_specializationTargetElement)) line1c line1d
  have line1 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine forwardNegation .pqr .pr)
    forwardNegation.pqr forwardDisjunction.pqr
    (star13_bridgeInterpret forwardNegation forwardDisjunction
      left identityXX phiX phiX phiX phiX
      star13_specializationSourceElement)
    (star13_bridgeInterpret forwardNegation forwardDisjunction
      left identityXX phiX phiX phiX phiX
      star13_specializationTargetElement) line1b line1e
  let pointNegation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseNegation
  }
  let pointDisjunction : MixedOrder.TernaryDisjunctions signature
      pointNegation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseDisjunction
  }
  let yValue : Term signature (sort :: real) [] sort := .real .zero
  let xValue := x.weakenReal (fresh := sort)
  let psiY := (psi.weakenReal (fresh := sort)).instantiate yValue
  let psiX := (psi.weakenReal (fresh := sort)).instantiate xValue
  let identityYX := star_13_01 vocabulary yValue xValue
  have line2a := star_13_12 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation reducibilityResultNegation
    reducibilityDisjunction identityOrderDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    reducibilityResultDisjunction reducibilityScopeUniversal
    reducibilityScopeNegation reducibilityScopeDisjunction
    existentialTargetDisjunction (psi.weakenReal (fresh := sort))
    yValue xValue
  change ⊢ᵣ star13_bridgeInterpret pointNegation pointDisjunction
    identityYX identityYX psiY psiX psiY psiX
    star13_191_pointwiseSourceElement at line2a
  have line2b := MixedOrder.transport MixedOrder.TernarySupport.combine
    pointNegation.toVocabulary pointDisjunction.toVocabulary
    (MixedOrder.ternaryTautology pointNegation pointDisjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => identityYX)
    star13_bridgeSupport
    (star13_bridgeValuation pointNegation identityYX identityYX
      psiY psiX psiY psiX)
    star13_elementary191PointwiseBridge
  change ⊢ᵣ star13_bridgeInterpret pointNegation pointDisjunction
    identityYX identityYX psiY psiX psiY psiX
    star13_191_pointwiseBridgeElement at line2b
  have line2c := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine pointNegation .qr .qr)
    pointNegation.qr pointDisjunction.qr
    (star13_bridgeInterpret pointNegation pointDisjunction
      identityYX identityYX psiY psiX psiY psiX
      star13_191_pointwiseSourceElement)
    (star13_bridgeInterpret pointNegation pointDisjunction
      identityYX identityYX psiY psiX psiY psiX
      star13_191_pointwiseTargetElement) line2a line2b
  let pointwiseEquality := MixedOrder.maxRightLeftAbsorb identityOrder order
  let pointwiseDisjunction := Eq.mp (congrArg signature.Disjunction
    pointwiseEquality.symm) identityBaseDisjunction
  let scopeBody := star13_normalizedDisjunction pointwiseEquality
    identityBaseDisjunction
    (.neg vocabulary.negation (phiX.rename (fun v => .succ v))) identityBody
  have line2c' : ⊢ᵣ MixedOrder.normalizedDisjunction pointwiseEquality
      identityBaseDisjunction (.neg vocabulary.negation psiX)
      (mixedImplication identityNegation identityBaseDisjunction
        identityYX psiY) := by
    change ⊢ᵣ MixedOrder.normalizedDisjunction pointwiseEquality
      identityBaseDisjunction (.neg vocabulary.negation psiX)
      (mixedImplication identityNegation identityBaseDisjunction
        identityYX psiY) at line2c
    exact line2c
  have identityAt :
      ((star_13_01 vocabulary
        (.apparent (.zero : Var [sort] sort)) x.weaken).weakenReal
          (fresh := sort)).instantiate yValue = identityYX := by
    rw [star13_identity_weakenReal]
    unfold identityYX xValue star_13_01
    rw [Formula.instantiate, substitute_always, implication_substitute]
    cases x <;> rfl
  have scopeAt : scopeBody.weakenReal.instantiate yValue =
      MixedOrder.normalizedDisjunction pointwiseEquality
        identityBaseDisjunction (.neg vocabulary.negation psiX)
        (mixedImplication identityNegation identityBaseDisjunction
          identityYX psiY) := by
    unfold scopeBody
    rw [star13_normalizedDisjunction_weakenReal,
      star13_normalizedDisjunction_instantiate]
    change star13_normalizedDisjunction pointwiseEquality
      identityBaseDisjunction
      (.neg vocabulary.negation
        (((phiX.rename (fun v => .succ v)) :
          Formula signature real [sort] order).weakenReal.instantiate yValue))
      (identityBody.weakenReal.instantiate yValue) = _
    rw [Formula.closed_weakenReal_instantiate]
    unfold phiX psiX psiY identityYX identityBody
    rw [star13_mixedImplication_weakenReal,
      star13_mixedImplication_instantiate,
      identityAt,
      star13_instantiate_weakenReal]
    unfold xValue star13_normalizedDisjunction
      MixedOrder.normalizedDisjunction
    rfl
  have line2d : ⊢ᵣ scopeBody.weakenReal.instantiate yValue := by
    exact Derivation.castAssertion scopeAt line2c'
  have line2e : ⊢ᵣ Formula.always identityUniversal scopeBody := by
    exact star_10_11 identityUniversal scopeBody line2d
  have innerDefinition : ImplicationDisjunction signature real
      (.neg vocabulary.negation (phiX.rename (fun v => .succ v)))
      identityBody scopeBody := by
    exact star13_castImplicationDisjunctionResult pointwiseEquality
      (.neg vocabulary.negation (phiX.rename (fun v => .succ v)))
      identityBody
      (.disj pointwiseDisjunction
        (.neg vocabulary.negation (phiX.rename (fun v => .succ v)))
        identityBody)
      (ImplicationDisjunction.star_1_01 pointwiseDisjunction
        (.neg vocabulary.negation (phiX.rename (fun v => .succ v)))
        identityBody)
  have scopeDefinition : ImplicationDisjunction signature real
      (.neg vocabulary.negation phiX) left
      (.always identityUniversal scopeBody) := by
    exact ImplicationDisjunction.star_9_04 identityUniversal
      identityUniversal (.neg vocabulary.negation phiX) identityBody
      scopeBody innerDefinition
  let reverseOrder := max order scopeOrder
  let reverseEquality := MixedOrder.maxComm order scopeOrder
  let reverseNegation := Eq.mp (congrArg signature.Negation
    reverseEquality.symm) scopeResultNegation
  let reverseDisjunction := Eq.mp (congrArg signature.Disjunction
    reverseEquality.symm) scopeResultDisjunction
  let scopePairNegation := Eq.mp (congrArg signature.Negation
    (natMaxSelf scopeOrder).symm) scopeNegation
  let scopePairDisjunction := Eq.mp (congrArg signature.Disjunction
    (natMaxSelf scopeOrder).symm) scopeDisjunction
  let reversePairDisjunction := Eq.mp (congrArg signature.Disjunction
    (natMaxSelf reverseOrder).symm) reverseDisjunction
  let primitiveOuterEquality := Eq.trans
    (Eq.trans
      (congrArg (fun left => max left
        (max (max order scopeOrder) (max order scopeOrder)))
        (natMaxSelf scopeOrder))
      (congrArg (fun right => max scopeOrder right)
        (natMaxSelf (max order scopeOrder))))
    (MixedOrder.maxRightLeftAbsorb order scopeOrder)
  let primitiveOuterDisjunction := Eq.mp (congrArg signature.Disjunction
    primitiveOuterEquality.symm) reverseDisjunction
  let sourceConsequenceEquality :=
    MixedOrder.maxRightLeftAbsorb order scopeOrder
  let sourceConsequenceDisjunction := Eq.mp (congrArg signature.Disjunction
    sourceConsequenceEquality.symm) reverseDisjunction
  let sourceOuterEquality := Eq.trans
    (congrArg (fun inner => max scopeOrder inner)
      sourceConsequenceEquality) sourceConsequenceEquality
  let sourceOuterDisjunction := Eq.mp (congrArg signature.Disjunction
    sourceOuterEquality.symm) reverseDisjunction
  have line2f := star13_canonicalizeMixedImplication
    vocabulary.negation vocabulary.disjunction scopeNegation scopeDisjunction
    reverseNegation reverseDisjunction scopePairNegation
    scopePairDisjunction reversePairDisjunction primitiveOuterDisjunction
    scopeNegation sourceConsequenceDisjunction sourceOuterDisjunction
    phiX left (.always identityUniversal scopeBody) scopeDefinition line2e
  have line2g := star13_castAssertionOrder reverseEquality
    (mixedImplication vocabulary.negation reverseDisjunction phiX left) line2f
  let equivalenceNegation : MixedOrder.TernaryNegations signature := {
    pOrder := scopeOrder
    qOrder := order
    rOrder := order
    p := scopeNegation
    q := vocabulary.negation
    r := vocabulary.negation
    pq := scopeResultNegation
    pr := scopeResultNegation
    qr := Eq.mp (congrArg signature.Negation
      (natMaxSelf order).symm) vocabulary.negation
    pqr := Eq.mp (congrArg signature.Negation
      (congrArg (fun inner => max scopeOrder inner)
        (natMaxSelf order)).symm) scopeResultNegation
  }
  let equivalenceDisjunction : MixedOrder.TernaryDisjunctions signature
      equivalenceNegation := {
    p := scopeDisjunction
    q := vocabulary.disjunction
    r := vocabulary.disjunction
    pq := scopeResultDisjunction
    pr := scopeResultDisjunction
    qr := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf order).symm) vocabulary.disjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (congrArg (fun inner => max scopeOrder inner)
        (natMaxSelf order)).symm) scopeResultDisjunction
  }
  change ⊢ᵣ star13_bridgeInterpret equivalenceNegation
    equivalenceDisjunction left phiX phiX phiX phiX phiX
    star13_equivalenceForwardElement at line1
  change ⊢ᵣ star13_bridgeInterpret equivalenceNegation
    equivalenceDisjunction left phiX phiX phiX phiX phiX
    star13_equivalenceReverseElement at line2g
  have line3a := MixedOrder.transport MixedOrder.TernarySupport.combine
    equivalenceNegation.toVocabulary equivalenceDisjunction.toVocabulary
    (MixedOrder.ternaryTautology equivalenceNegation equivalenceDisjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => left)
    star13_bridgeSupport
    (star13_bridgeValuation equivalenceNegation left phiX
      phiX phiX phiX phiX)
    star13_elementaryEquivalenceIntro
  change ⊢ᵣ star13_bridgeInterpret equivalenceNegation
    equivalenceDisjunction left phiX phiX phiX phiX phiX
    star13_equivalenceIntroElement at line3a
  have line3b := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine equivalenceNegation .pq .pq)
    equivalenceNegation.pq equivalenceDisjunction.pq
    (star13_bridgeInterpret equivalenceNegation equivalenceDisjunction
      left phiX phiX phiX phiX phiX star13_equivalenceForwardElement)
    (star13_bridgeInterpret equivalenceNegation equivalenceDisjunction
      left phiX phiX phiX phiX phiX
      (star13_equivalenceReverseElement ⊃ₚ
        star13_equivalenceTargetElement)) line1 line3a
  have line3 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine equivalenceNegation .pq .pq)
    equivalenceNegation.pq equivalenceDisjunction.pq
    (star13_bridgeInterpret equivalenceNegation equivalenceDisjunction
      left phiX phiX phiX phiX phiX star13_equivalenceReverseElement)
    (star13_bridgeInterpret equivalenceNegation equivalenceDisjunction
      left phiX phiX phiX phiX phiX star13_equivalenceTargetElement)
    line2g line3b
  change ⊢ᵣ star_13_191_formula vocabulary identityUniversal
    identityNegation identityBaseDisjunction scopeNegation scopeDisjunction
    scopeResultNegation scopeResultDisjunction psi x
  unfold star_13_191_formula
  exact line3

private theorem star13_binaryPair
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    (line1 : ⊢ᵣ p)
    (line2 : ⊢ᵣ q) :
    ⊢ᵣ MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ) := by
  have line3 := MixedOrder.star_3_2 negation disjunction p q
  have line4 := MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .left .both)
    negation.left disjunction.both p
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryQ ⊃ₚ
        (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ))) line1 line3
  exact MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .right .both)
    negation.right disjunction.both q
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) line2 line4

private theorem star13_binaryLeft
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    (line1 : ⊢ᵣ MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) :
    ⊢ᵣ p := by
  have line2 := MixedOrder.star_3_26 negation disjunction p q
  exact MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .both .left)
    negation.both disjunction.both
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) p line1 line2

private theorem star13_binaryRight
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    (line1 : ⊢ᵣ MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) :
    ⊢ᵣ q := by
  have line2 := MixedOrder.star_3_27 negation disjunction p q
  exact MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .both .right)
    negation.both disjunction.both
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) q line1 line2

private theorem star13_binaryJoin
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    (line1 : ⊢ᵣ MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ⊃ₚ MixedOrder.binaryQ))
    (line2 : ⊢ᵣ MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryQ ⊃ₚ MixedOrder.binaryP)) :
    ⊢ᵣ MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ≡ₚ MixedOrder.binaryQ) := by
  have line3 := MixedOrder.binaryTransport negation disjunction p q
    (PM.FirstEdition.Volume1.Star3.star_3_2
      (MixedOrder.binaryP ⊃ₚ MixedOrder.binaryQ)
      (MixedOrder.binaryQ ⊃ₚ MixedOrder.binaryP))
  have line4 := MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .both .both)
    negation.both disjunction.both
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ⊃ₚ MixedOrder.binaryQ))
    (MixedOrder.binaryInterpret negation disjunction p q
      ((MixedOrder.binaryQ ⊃ₚ MixedOrder.binaryP) ⊃ₚ
        (MixedOrder.binaryP ≡ₚ MixedOrder.binaryQ))) line1 line3
  exact MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .both .both)
    negation.both disjunction.both
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryQ ⊃ₚ MixedOrder.binaryP))
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryP ≡ₚ MixedOrder.binaryQ)) line2 line4

private theorem star13_ternarySyll
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))
    (line2 : ⊢ᵣ MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR)) :
    ⊢ᵣ MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR) := by
  have line3 := MixedOrder.ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star2.star_2_05 MixedOrder.ternaryP
      MixedOrder.ternaryQ MixedOrder.ternaryR)
  have line4 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .pqr)
    negation.qr disjunction.pqr
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR))
    (MixedOrder.ternaryInterpret negation disjunction p q r
      ((MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ) ⊃ₚ
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR))) line2 line3
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pr)
    negation.pq disjunction.pqr
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)) line1 line4

private theorem star13_binaryPairUnderRight
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    (line1 : ⊢ᵣ p) :
    ⊢ᵣ MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryQ ⊃ₚ
        (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) := by
  have line2 := MixedOrder.star_3_2 negation disjunction p q
  exact MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .left .both)
    negation.left disjunction.both p
    (MixedOrder.binaryInterpret negation disjunction p q
      (MixedOrder.binaryQ ⊃ₚ
        (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ))) line1 line2

private theorem star13_mixedConjunction_weakenReal
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    (mixedConjunction leftNegation rightNegation outerNegation disjunction
      left right).weakenReal (fresh := fresh) =
      mixedConjunction leftNegation rightNegation outerNegation disjunction
        left.weakenReal right.weakenReal := by
  rfl

private theorem star13_mixedConjunction_instantiate
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real (sort :: apparent) leftOrder)
    (right : Formula signature real (sort :: apparent) rightOrder)
    (term : Term signature real apparent sort) :
    (mixedConjunction leftNegation rightNegation outerNegation disjunction
      left right).instantiate term =
      mixedConjunction leftNegation rightNegation outerNegation disjunction
        (left.instantiate term) (right.instantiate term) := by
  rfl

private theorem star13_elementaryReflexiveEquivalence
    {context : PM.RealContext}
    (p q : PM.Elementary context) :
    PM.Derivation (p ⊃ₚ ((p ≡ₚ q) ⊃ₚ q)) := by
  have line1 := PM.FirstEdition.Volume1.Star5.star_5_501 p q
  have line2 := PM.FirstEdition.Volume1.Star3.star_3_27
    (q ⊃ₚ (p ≡ₚ q)) ((p ≡ₚ q) ⊃ₚ q)
  have line3 := PM.FirstEdition.Volume1.Star2.star_2_05 p
    (q ≡ₚ (p ≡ₚ q)) ((p ≡ₚ q) ⊃ₚ q)
  have line4 := PM.Derivation.detach line2 line3
  exact PM.Derivation.detach line1 line4

private theorem star13_elementaryReverseSubstitution
    {context : PM.RealContext}
    (p q r : PM.Elementary context) :
    PM.Derivation
      ((((∼ₚ r) ∧ₚ p) ⊃ₚ (∼ₚ q)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)) := by
  let source := ((∼ₚ r) ∧ₚ p) ⊃ₚ (∼ₚ q)
  let middle := (p ∧ₚ (∼ₚ r)) ⊃ₚ (∼ₚ q)
  let target := (p ∧ₚ q) ⊃ₚ r
  have line1a := PM.FirstEdition.Volume1.Star2.star_2_05
    (p ∧ₚ (∼ₚ r)) ((∼ₚ r) ∧ₚ p) (∼ₚ q)
  have line1b := PM.FirstEdition.Volume1.Star2.star_2_04 source
    ((p ∧ₚ (∼ₚ r)) ⊃ₚ ((∼ₚ r) ∧ₚ p)) middle
  have line1c := PM.Derivation.detach line1a line1b
  have line1d := PM.FirstEdition.Volume1.Star3.star_3_22 p (∼ₚ r)
  have line1 := PM.Derivation.detach line1d line1c
  have line2a := PM.FirstEdition.Volume1.Star4.star_4_14 p q r
  have line2b := PM.FirstEdition.Volume1.Star3.star_3_27
    (target ⊃ₚ middle) (middle ⊃ₚ target)
  have line2 := PM.Derivation.detach line2a line2b
  have line3 := PM.FirstEdition.Volume1.Star2.star_2_05 source middle target
  exact PM.Derivation.detach line1 (PM.Derivation.detach line2 line3)

private abbrev Star13FiveContext : PM.RealContext :=
  [.elementaryProposition, .elementaryProposition, .elementaryProposition,
    .elementaryProposition, .elementaryProposition]

private def star13_fiveA : PM.Elementary Star13FiveContext := .var .zero
private def star13_fiveE : PM.Elementary Star13FiveContext :=
  .var (.succ .zero)
private def star13_fiveQ : PM.Elementary Star13FiveContext :=
  .var (.succ (.succ .zero))
private def star13_fiveC : PM.Elementary Star13FiveContext :=
  .var (.succ (.succ (.succ .zero)))
private def star13_fiveR : PM.Elementary Star13FiveContext :=
  .var (.succ (.succ (.succ (.succ .zero))))

private def star13_fiveBridgeElement : PM.Elementary Star13FiveContext :=
  (star13_fiveA ⊃ₚ star13_fiveE) ⊃ₚ
    ((star13_fiveA ⊃ₚ star13_fiveC) ⊃ₚ
      ((star13_fiveE ⊃ₚ star13_fiveQ) ⊃ₚ
        (((star13_fiveQ ∧ₚ star13_fiveC) ⊃ₚ star13_fiveR) ⊃ₚ
          (star13_fiveA ⊃ₚ star13_fiveR))))

private theorem star13_elementaryFiveBridge :
    PM.Derivation star13_fiveBridgeElement := by
  let syll : ∀ p q r : PM.Elementary Star13FiveContext,
      PM.Derivation (p ⊃ₚ q) → PM.Derivation (q ⊃ₚ r) →
        PM.Derivation (p ⊃ₚ r) := by
    intro p q r line1 line2
    exact PM.Derivation.detach line1
      (PM.Derivation.detach line2
        (PM.FirstEdition.Volume1.Star2.star_2_05 p q r))
  let mapUnder : ∀ p q r : PM.Elementary Star13FiveContext,
      PM.Derivation (q ⊃ₚ r) →
        PM.Derivation ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)) := by
    intro p q r line1
    exact PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star2.star_2_05 p q r)
  let aq := star13_fiveA ⊃ₚ star13_fiveQ
  let ac := star13_fiveA ⊃ₚ star13_fiveC
  let ar := star13_fiveA ⊃ₚ star13_fiveR
  let qc := star13_fiveQ ∧ₚ star13_fiveC
  let aeq := star13_fiveA ⊃ₚ star13_fiveE
  let eq := star13_fiveE ⊃ₚ star13_fiveQ
  let qr := qc ⊃ₚ star13_fiveR
  have line1a := PM.FirstEdition.Volume1.Star2.star_2_05 star13_fiveA
    star13_fiveE star13_fiveQ
  have line1b := PM.FirstEdition.Volume1.Star2.star_2_04 eq aeq aq
  have line1 := PM.Derivation.detach line1a line1b
  have line2a := PM.FirstEdition.Volume1.Star3.star_3_2 aq ac
  have line2b := PM.FirstEdition.Volume1.Star4.star_4_76
    star13_fiveA star13_fiveQ star13_fiveC
  have line2c := PM.FirstEdition.Volume1.Star3.star_3_26
    ((aq ∧ₚ ac) ⊃ₚ (star13_fiveA ⊃ₚ qc))
    ((star13_fiveA ⊃ₚ qc) ⊃ₚ (aq ∧ₚ ac))
  have line2d := PM.Derivation.detach line2b line2c
  have line2e := mapUnder ac (aq ∧ₚ ac)
    (star13_fiveA ⊃ₚ qc) line2d
  have line2f := mapUnder aq (ac ⊃ₚ (aq ∧ₚ ac))
    (ac ⊃ₚ (star13_fiveA ⊃ₚ qc)) line2e
  have line2 := PM.Derivation.detach line2a line2f
  have line3a := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_fiveA qc star13_fiveR
  have line3b := PM.FirstEdition.Volume1.Star2.star_2_04 qr
    (star13_fiveA ⊃ₚ qc) ar
  have line3 := PM.Derivation.detach line3a line3b
  have line4a := mapUnder ac (star13_fiveA ⊃ₚ qc)
    (qr ⊃ₚ ar) line3
  have line4 := syll aq (ac ⊃ₚ (star13_fiveA ⊃ₚ qc))
    (ac ⊃ₚ (qr ⊃ₚ ar)) line2 line4a
  have line5a := mapUnder eq aq (ac ⊃ₚ (qr ⊃ₚ ar)) line4
  have line5 := syll aeq (eq ⊃ₚ aq)
    (eq ⊃ₚ (ac ⊃ₚ (qr ⊃ₚ ar))) line1 line5a
  have line6a := PM.FirstEdition.Volume1.Star2.star_2_04 eq ac
    (qr ⊃ₚ ar)
  have line6 := mapUnder aeq
    (eq ⊃ₚ (ac ⊃ₚ (qr ⊃ₚ ar)))
    (ac ⊃ₚ (eq ⊃ₚ (qr ⊃ₚ ar))) line6a
  unfold star13_fiveBridgeElement
  exact PM.Derivation.detach line5 line6

private def star13_fiveSupport :
    PM.RealVar Star13FiveContext .elementaryProposition →
      MixedOrder.TernarySupport
  | .zero => .p
  | .succ .zero => .q
  | .succ (.succ .zero) => .q
  | .succ (.succ (.succ .zero)) => .r
  | .succ (.succ (.succ (.succ .zero))) => .r

private def star13_fiveValuation
    (negation : MixedOrder.TernaryNegations signature)
    (a : Formula signature real [] negation.pOrder)
    (e q : Formula signature real [] negation.qOrder)
    (c r : Formula signature real [] negation.rOrder) :
    ∀ v : PM.RealVar Star13FiveContext .elementaryProposition,
      Formula signature real [] (negation.order (star13_fiveSupport v))
  | .zero => a
  | .succ .zero => e
  | .succ (.succ .zero) => q
  | .succ (.succ (.succ .zero)) => c
  | .succ (.succ (.succ (.succ .zero))) => r

private def star13_fiveInterpret
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e q : Formula signature real [] negation.qOrder)
    (c r : Formula signature real [] negation.rOrder)
    (proposition : PM.Elementary Star13FiveContext) :=
  MixedOrder.interpret MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_fiveSupport (star13_fiveValuation negation a e q c r)
    proposition

private theorem star13_ramifiedFiveBridge
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e q : Formula signature real [] negation.qOrder)
    (c r : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveA ⊃ₚ star13_fiveE))
    (line2 : ⊢ᵣ star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveA ⊃ₚ star13_fiveC))
    (line3 : ⊢ᵣ star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveE ⊃ₚ star13_fiveQ))
    (line4 : ⊢ᵣ star13_fiveInterpret negation disjunction a e q c r
      ((star13_fiveQ ∧ₚ star13_fiveC) ⊃ₚ star13_fiveR)) :
    ⊢ᵣ star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveA ⊃ₚ star13_fiveR) := by
  have bridge := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_fiveSupport (star13_fiveValuation negation a e q c r)
    star13_elementaryFiveBridge
  change ⊢ᵣ star13_fiveInterpret negation disjunction a e q c r
    star13_fiveBridgeElement at bridge
  have line5 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pqr)
    negation.pq disjunction.pqr
    (star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveA ⊃ₚ star13_fiveE))
    (star13_fiveInterpret negation disjunction a e q c r
      ((star13_fiveA ⊃ₚ star13_fiveC) ⊃ₚ
        ((star13_fiveE ⊃ₚ star13_fiveQ) ⊃ₚ
          (((star13_fiveQ ∧ₚ star13_fiveC) ⊃ₚ star13_fiveR) ⊃ₚ
            (star13_fiveA ⊃ₚ star13_fiveR))))) line1 bridge
  have line6 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pr .pqr)
    negation.pr disjunction.pqr
    (star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveA ⊃ₚ star13_fiveC))
    (star13_fiveInterpret negation disjunction a e q c r
      ((star13_fiveE ⊃ₚ star13_fiveQ) ⊃ₚ
        (((star13_fiveQ ∧ₚ star13_fiveC) ⊃ₚ star13_fiveR) ⊃ₚ
          (star13_fiveA ⊃ₚ star13_fiveR)))) line2 line5
  have line7 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .q .pqr)
    negation.q disjunction.pqr
    (star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveE ⊃ₚ star13_fiveQ))
    (star13_fiveInterpret negation disjunction a e q c r
      (((star13_fiveQ ∧ₚ star13_fiveC) ⊃ₚ star13_fiveR) ⊃ₚ
        (star13_fiveA ⊃ₚ star13_fiveR))) line3 line6
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .pr)
    negation.qr disjunction.pqr
    (star13_fiveInterpret negation disjunction a e q c r
      ((star13_fiveQ ∧ₚ star13_fiveC) ⊃ₚ star13_fiveR))
    (star13_fiveInterpret negation disjunction a e q c r
      (star13_fiveA ⊃ₚ star13_fiveR)) line4 line7

private theorem star13_ramifiedReverseSubstitution
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ MixedOrder.ternaryInterpret negation disjunction p q r
      (((∼ₚ MixedOrder.ternaryR) ∧ₚ MixedOrder.ternaryP) ⊃ₚ
        (∼ₚ MixedOrder.ternaryQ))) :
    ⊢ᵣ MixedOrder.ternaryInterpret negation disjunction p q r
      ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryQ) ⊃ₚ
        MixedOrder.ternaryR) := by
  have line2 := MixedOrder.ternaryTransport negation disjunction p q r
    (star13_elementaryReverseSubstitution MixedOrder.ternaryP
      MixedOrder.ternaryQ MixedOrder.ternaryR)
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pqr .pqr)
    negation.pqr disjunction.pqr
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (((∼ₚ MixedOrder.ternaryR) ∧ₚ MixedOrder.ternaryP) ⊃ₚ
        (∼ₚ MixedOrder.ternaryQ)))
    (MixedOrder.ternaryInterpret negation disjunction p q r
      ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryQ) ⊃ₚ
        MixedOrder.ternaryR)) line1 line2

private theorem star13_ramified13ReverseSubstitution
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z0 w0 z w : Formula signature real [] negation.rOrder)
    (xEquality : x = .neg negation.r w)
    (yEquality : y = .neg negation.r z)
    (line1 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z0 w0 star13_13_targetElement) :
    ⊢ᵣ star13_normalizedDisjunction
      (MixedOrder.maxRightAbsorb negation.qOrder negation.rOrder)
      disjunction.qr
      (.neg negation.qr
        (mixedConjunction negation.q negation.r negation.qr
          disjunction.qr e z)) w := by
  rw [xEquality, yEquality] at line1
  have line2 := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_bridgeSupport
    (star13_bridgeValuation negation a e (.neg negation.r w)
      (.neg negation.r z) z w)
    (star13_elementaryReverseSubstitution star13_bridgeE
      star13_bridgeZ star13_bridgeW)
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e (.neg negation.r w) (.neg negation.r z) z w
    ((((∼ₚ star13_bridgeW) ∧ₚ star13_bridgeE) ⊃ₚ
      (∼ₚ star13_bridgeZ))) at line1
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e (.neg negation.r w) (.neg negation.r z) z w
    (((((∼ₚ star13_bridgeW) ∧ₚ star13_bridgeE) ⊃ₚ
        (∼ₚ star13_bridgeZ))) ⊃ₚ
      ((star13_bridgeE ∧ₚ star13_bridgeZ) ⊃ₚ
        star13_bridgeW)) at line2
  have line3 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      a e (.neg negation.r w) (.neg negation.r z) z w
      ((((∼ₚ star13_bridgeW) ∧ₚ star13_bridgeE) ⊃ₚ
        (∼ₚ star13_bridgeZ))))
    (star13_bridgeInterpret negation disjunction
      a e (.neg negation.r w) (.neg negation.r z) z w
      ((star13_bridgeE ∧ₚ star13_bridgeZ) ⊃ₚ star13_bridgeW))
    line1 line2
  change ⊢ᵣ star13_normalizedDisjunction
    (MixedOrder.maxRightAbsorb negation.qOrder negation.rOrder)
    disjunction.qr
    (.neg negation.qr
      (mixedConjunction negation.q negation.r negation.qr
        disjunction.qr e z)) w at line3
  exact line3

private def star13_193_leftElement : PM.Elementary Star13BridgeContext :=
  star13_bridgeX ∧ₚ star13_bridgeE

private def star13_193_rightElement : PM.Elementary Star13BridgeContext :=
  star13_bridgeY ∧ₚ star13_bridgeE

private def star13_193_line1Element : PM.Elementary Star13BridgeContext :=
  star13_193_leftElement ⊃ₚ star13_bridgeE

private def star13_193_line2Element : PM.Elementary Star13BridgeContext :=
  star13_193_leftElement ⊃ₚ star13_bridgeY

private def star13_193_line3Element : PM.Elementary Star13BridgeContext :=
  star13_193_leftElement ⊃ₚ star13_193_rightElement

private def star13_193_reverseSourceElement :
    PM.Elementary Star13BridgeContext :=
  (((∼ₚ star13_bridgeX) ∧ₚ star13_bridgeE) ⊃ₚ
    (∼ₚ star13_bridgeY))

private def star13_193_line4Element : PM.Elementary Star13BridgeContext :=
  star13_193_rightElement ⊃ₚ star13_193_leftElement

private def star13_193_formulaElement : PM.Elementary Star13BridgeContext :=
  star13_193_line3Element ∧ₚ star13_193_line4Element

private theorem star13_elementary193Forward :
    PM.Derivation
      (star13_193_line1Element ⊃ₚ
        (star13_193_line2Element ⊃ₚ star13_193_line3Element)) := by
  let pair := star13_193_line2Element ∧ₚ star13_193_line1Element
  have line1a := PM.FirstEdition.Volume1.Star3.star_3_2
    star13_193_line2Element star13_193_line1Element
  have line1b := PM.FirstEdition.Volume1.Star2.star_2_04
    star13_193_line2Element star13_193_line1Element pair
  have line1 := PM.Derivation.detach line1a line1b
  have line2a := PM.FirstEdition.Volume1.Star4.star_4_76
    star13_193_leftElement star13_bridgeY star13_bridgeE
  have line2b := PM.FirstEdition.Volume1.Star3.star_3_26
    (pair ⊃ₚ star13_193_line3Element)
    (star13_193_line3Element ⊃ₚ pair)
  have line2 := PM.Derivation.detach line2a line2b
  have line3a := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_193_line2Element pair star13_193_line3Element
  have line3 := PM.Derivation.detach line2 line3a
  have line4 := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_193_line1Element
    (star13_193_line2Element ⊃ₚ pair)
    (star13_193_line2Element ⊃ₚ star13_193_line3Element)
  exact PM.Derivation.detach line1 (PM.Derivation.detach line3 line4)

private theorem star13_elementary193Reverse :
    PM.Derivation
      (star13_193_reverseSourceElement ⊃ₚ star13_193_line4Element) := by
  let middle :=
    (star13_bridgeE ∧ₚ star13_bridgeY) ⊃ₚ star13_bridgeX
  let rightToX := star13_193_rightElement ⊃ₚ star13_bridgeX
  let rightToE := star13_193_rightElement ⊃ₚ star13_bridgeE
  let pair := rightToX ∧ₚ rightToE
  have line1 := star13_elementaryReverseSubstitution star13_bridgeE
    star13_bridgeY star13_bridgeX
  have line2a := PM.FirstEdition.Volume1.Star3.star_3_22
    star13_bridgeY star13_bridgeE
  have line2b := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_193_rightElement
    (star13_bridgeE ∧ₚ star13_bridgeY) star13_bridgeX
  have line2c := PM.FirstEdition.Volume1.Star2.star_2_04
    middle
    (star13_193_rightElement ⊃ₚ
      (star13_bridgeE ∧ₚ star13_bridgeY)) rightToX
  have line2d := PM.Derivation.detach line2b line2c
  have line2 := PM.Derivation.detach line2a line2d
  have line3a := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_193_reverseSourceElement middle rightToX
  have line3 := PM.Derivation.detach line1
    (PM.Derivation.detach line2 line3a)
  have line4a := PM.FirstEdition.Volume1.Star3.star_3_27
    star13_bridgeY star13_bridgeE
  have line4b := PM.FirstEdition.Volume1.Star3.star_3_2 rightToX rightToE
  have line4c := PM.FirstEdition.Volume1.Star2.star_2_04
    rightToX rightToE pair
  have line4d := PM.Derivation.detach line4b line4c
  have line4 := PM.Derivation.detach line4a line4d
  have line5a := PM.FirstEdition.Volume1.Star4.star_4_76
    star13_193_rightElement star13_bridgeX star13_bridgeE
  have line5b := PM.FirstEdition.Volume1.Star3.star_3_26
    (pair ⊃ₚ star13_193_line4Element)
    (star13_193_line4Element ⊃ₚ pair)
  have line5 := PM.Derivation.detach line5a line5b
  have line6a := PM.FirstEdition.Volume1.Star2.star_2_05
    rightToX pair star13_193_line4Element
  have line6 := PM.Derivation.detach line4
    (PM.Derivation.detach line5 line6a)
  have line7 := PM.FirstEdition.Volume1.Star2.star_2_05
    star13_193_reverseSourceElement rightToX star13_193_line4Element
  exact PM.Derivation.detach line3 (PM.Derivation.detach line6 line7)

private theorem star13_ramified193Forward
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z w : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line1Element)
    (line2 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line2Element) :
    ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line3Element := by
  have bridge := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_bridgeSupport (star13_bridgeValuation negation a e x y z w)
    star13_elementary193Forward
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w
    (star13_193_line1Element ⊃ₚ
      (star13_193_line2Element ⊃ₚ star13_193_line3Element)) at bridge
  have line3 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line1Element)
    (star13_bridgeInterpret negation disjunction
      a e x y z w
      (star13_193_line2Element ⊃ₚ star13_193_line3Element))
    line1 bridge
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line2Element)
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line3Element) line2 line3

private theorem star13_ramified193Reverse
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z w : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e (.neg negation.r x) (.neg negation.r y)
      (.neg negation.r x) (.neg negation.r y)
      star13_13_targetElement) :
    ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line4Element := by
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w star13_193_reverseSourceElement at line1
  have bridge := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_bridgeSupport (star13_bridgeValuation negation a e x y z w)
    star13_elementary193Reverse
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w
    (star13_193_reverseSourceElement ⊃ₚ star13_193_line4Element)
    at bridge
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_reverseSourceElement)
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line4Element) line1 bridge

private theorem star13_ramified193Join
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z w : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line3Element)
    (line2 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line4Element) :
    ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_formulaElement := by
  have bridge := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_bridgeSupport (star13_bridgeValuation negation a e x y z w)
    (PM.FirstEdition.Volume1.Star3.star_3_2
      star13_193_line3Element star13_193_line4Element)
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w
    (star13_193_line3Element ⊃ₚ
      (star13_193_line4Element ⊃ₚ star13_193_formulaElement))
    at bridge
  have line3 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line3Element)
    (star13_bridgeInterpret negation disjunction
      a e x y z w
      (star13_193_line4Element ⊃ₚ star13_193_formulaElement))
    line1 bridge
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_line4Element)
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_193_formulaElement) line2 line3

private def star13_195_pointElement : PM.Elementary Star13BridgeContext :=
  (star13_bridgeE ∧ₚ star13_bridgeX) ⊃ₚ star13_bridgeY

private theorem star13_elementary195Point :
    PM.Derivation
      (star13_13_targetElement ⊃ₚ star13_195_pointElement) := by
  let source := star13_bridgeX ∧ₚ star13_bridgeE
  let target := star13_bridgeE ∧ₚ star13_bridgeX
  have line1 := PM.FirstEdition.Volume1.Star3.star_3_22
    star13_bridgeE star13_bridgeX
  have line2a := PM.FirstEdition.Volume1.Star2.star_2_05 target source
    star13_bridgeY
  have line2b := PM.FirstEdition.Volume1.Star2.star_2_04
    star13_13_targetElement (target ⊃ₚ source)
    star13_195_pointElement
  have line2 := PM.Derivation.detach line2a line2b
  exact PM.Derivation.detach line1 line2

private theorem star13_ramified195Point
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (a : Formula signature real [] negation.pOrder)
    (e : Formula signature real [] negation.qOrder)
    (x y z w : Formula signature real [] negation.rOrder)
    (line1 : ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_13_targetElement) :
    ⊢ᵣ star13_bridgeInterpret negation disjunction
      a e x y z w star13_195_pointElement := by
  have bridge := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => a)
    star13_bridgeSupport (star13_bridgeValuation negation a e x y z w)
    star13_elementary195Point
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    a e x y z w
    (star13_13_targetElement ⊃ₚ star13_195_pointElement) at bridge
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .qr)
    negation.qr disjunction.qr
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_13_targetElement)
    (star13_bridgeInterpret negation disjunction
      a e x y z w star13_195_pointElement) line1 bridge

private theorem star13_reflexiveEquivalence
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (line1 : ⊢ᵣ p) :
    ⊢ᵣ implication negation disjunction
      (equivalence negation disjunction p q) q := by
  have line2 := star_5_501 negation disjunction p q
  have line3 := star13_detach negation disjunction p
    (equivalence negation disjunction q
      (equivalence negation disjunction p q)) line1 line2
  have line4 := star_3_27 negation disjunction
    (implication negation disjunction q
      (equivalence negation disjunction p q))
    (implication negation disjunction
      (equivalence negation disjunction p q) q)
  have line5 := star13_detach negation disjunction
    (equivalence negation disjunction q
      (equivalence negation disjunction p q))
    (implication negation disjunction
      (equivalence negation disjunction p q) q) line3 line4
  exact line5

def star_13_192_identityMatrix
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (b : Term signature real [] sort) :
    Formula signature real [sort, sort]
      (bindOrder order (.function [sort] order 0)) :=
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let c : Term signature real [sort, sort] sort := .apparent (.succ .zero)
  equivalence identityNegation identityOrderDisjunction
    (star_13_01 vocabulary x b.weaken.weaken)
    (star_13_01 vocabulary x c)

def star_13_192_body
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityUniversal : signature.Universal sort
      (bindOrder order (.function [sort] order 0)))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (equalityScopeNegation : signature.Negation
      (bindOrder (bindOrder order (.function [sort] order 0)) sort))
    (memberNegation : signature.Negation
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (memberDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (psi : Formula signature real [sort] order)
    (b : Term signature real [] sort) :
    Formula signature real [sort]
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order) :=
  mixedConjunction equalityScopeNegation vocabulary.negation memberNegation
    memberDisjunction
    (.always identityUniversal
      (star_13_192_identityMatrix vocabulary identityNegation
        identityOrderDisjunction b)) psi

def star_13_192_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityUniversal : signature.Universal sort
      (bindOrder order (.function [sort] order 0)))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (equalityScopeNegation : signature.Negation
      (bindOrder (bindOrder order (.function [sort] order 0)) sort))
    (memberNegation : signature.Negation
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (memberDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (existentialDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (implicationUniversal : signature.Universal sort
      (max
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) order))
    (resultNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (resultDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (psi : Formula signature real [sort] order)
    (b : Term signature real [] sort) :=
  let identityOrder := bindOrder order (.function [sort] order 0)
  let equalityScopeOrder := bindOrder identityOrder sort
  let memberOrder := max equalityScopeOrder order
  let body := star_13_192_body vocabulary identityUniversal identityNegation
    identityOrderDisjunction equalityScopeNegation memberNegation
    memberDisjunction psi b
  let existentialMember := Formula.sometimes existential body
  let psiB := psi.instantiate b
  let memberPsiEquality := MixedOrder.maxRightAbsorb equalityScopeOrder order
  let memberPsiDisjunction := Eq.mp (congrArg signature.Disjunction
    memberPsiEquality.symm) memberDisjunction
  let forwardEquality := congrArg (fun matrixOrder =>
    bindOrder matrixOrder sort) memberPsiEquality
  let forward := Eq.mp (congrArg (Formula signature real []) forwardEquality)
    (star_10_23_right existential existential.universal implicationUniversal
      memberNegation memberPsiDisjunction body psiB)
  let reverseEquality := Eq.trans
    (bindOrderMaxLeft order memberOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightLeftAbsorb equalityScopeOrder order))
  let reverse := star13_normalizedDisjunction reverseEquality
    existentialDisjunction (.neg vocabulary.negation psiB) existentialMember
  conjunction resultNegation resultDisjunction forward reverse

/-- Audited scope reading of ✱13·192. -/
def star_13_192_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityUniversal : signature.Universal sort
      (bindOrder order (.function [sort] order 0)))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (equalityScopeNegation : signature.Negation
      (bindOrder (bindOrder order (.function [sort] order 0)) sort))
    (memberNegation : signature.Negation
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (memberDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (existentialDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (implicationUniversal : signature.Universal sort
      (max
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) order))
    (resultNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (resultDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (psi : Formula signature real [sort] order)
    (b : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ :: (∃c) : x = b .≡x . x = c : ψc : ≡ . ψb"
  parsed := .assertion (star_13_192_formula vocabulary identityUniversal
    identityNegation identityOrderDisjunction equalityScopeNegation
    memberNegation memberDisjunction existential existentialDisjunction
    implicationUniversal resultNegation resultDisjunction psi b)

set_option maxHeartbeats 1000000 in
/-- ✱13·192, following PM's three printed lines.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_192
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityUniversal : signature.Universal sort
      (bindOrder order (.function [sort] order 0)))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (equalityScopeNegation : signature.Negation
      (bindOrder (bindOrder order (.function [sort] order 0)) sort))
    (equalityScopeDisjunction : signature.Disjunction
      (bindOrder (bindOrder order (.function [sort] order 0)) sort))
    (memberNegation : signature.Negation
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (memberDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
        order))
    (existentialDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (implicationUniversal : signature.Universal sort
      (max
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) order))
    (resultNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (resultDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order (.function [sort] order 0)) sort)
          order) sort))
    (psi : Formula signature real [sort] order)
    (b : Term signature real [] sort)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (substitutionResultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction (bindOrder order sort))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (substitutionResultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order))) :
    Derivation (star_13_192_reading vocabulary identityUniversal
      identityNegation identityOrderDisjunction equalityScopeNegation
      memberNegation memberDisjunction existential existentialDisjunction
      implicationUniversal resultNegation resultDisjunction psi b).parsed := by
  let identityOrder := bindOrder order (.function [sort] order 0)
  let equalityScopeOrder := bindOrder identityOrder sort
  let memberOrder := max equalityScopeOrder order
  let resultOrder := bindOrder memberOrder sort
  let body := star_13_192_body vocabulary identityUniversal identityNegation
    identityOrderDisjunction equalityScopeNegation memberNegation
    memberDisjunction psi b
  let existentialMember := Formula.sometimes existential body
  let psiB := psi.instantiate b
  let reflexiveBody : Formula signature real [sort] identityOrder :=
    equivalence identityNegation identityOrderDisjunction
      (star_13_01 vocabulary (.apparent (.zero : Var [sort] sort)) b.weaken)
      (star_13_01 vocabulary (.apparent (.zero : Var [sort] sort)) b.weaken)
  let xValue : Term signature (sort :: real) [] sort := .real .zero
  let bValue := b.weakenReal (fresh := sort)
  let identityXB := star_13_01 vocabulary xValue bValue
  have line1a0 := star_4_2 identityNegation identityOrderDisjunction identityXB
  have identityAt :
      (star_13_01 vocabulary
        (.apparent (.zero : Var [sort] sort)) b.weaken).weakenReal.instantiate
          xValue = identityXB := by
    rw [star13_identity_weakenReal]
    unfold identityXB star_13_01
    rw [Formula.instantiate, substitute_always, implication_substitute]
    cases b <;> rfl
  have reflexiveAt : reflexiveBody.weakenReal.instantiate xValue =
      equivalence identityNegation identityOrderDisjunction
        identityXB identityXB := by
    unfold reflexiveBody
    rw [star13_equivalence_weakenReal, Formula.instantiate,
      star13_equivalence_substitute]
    change equivalence identityNegation identityOrderDisjunction
      ((star_13_01 vocabulary
        (.apparent (.zero : Var [sort] sort)) b.weaken).weakenReal.instantiate
          xValue)
      ((star_13_01 vocabulary
        (.apparent (.zero : Var [sort] sort)) b.weaken).weakenReal.instantiate
          xValue) = _
    rw [identityAt]
  have line1a := star_10_11 identityUniversal reflexiveBody
    (Derivation.castAssertion reflexiveAt line1a0)
  let bodyNegation : MixedOrder.BinaryNegations signature := {
    leftOrder := equalityScopeOrder
    rightOrder := order
    left := equalityScopeNegation
    right := vocabulary.negation
    both := memberNegation
  }
  let bodyDisjunction : MixedOrder.BinaryDisjunctions signature
      bodyNegation := {
    left := equalityScopeDisjunction
    right := vocabulary.disjunction
    both := memberDisjunction
  }
  have line1b := star13_binaryPairUnderRight bodyNegation bodyDisjunction
    (Formula.always identityUniversal reflexiveBody) psiB line1a
  have bodyAtB : body.instantiate b =
      mixedConjunction equalityScopeNegation vocabulary.negation
        memberNegation memberDisjunction
        (Formula.always identityUniversal reflexiveBody) psiB := by
    unfold body star_13_192_body
    rw [star13_mixedConjunction_instantiate]
    unfold star_13_192_identityMatrix reflexiveBody
    rw [Formula.instantiate, substitute_always,
      star13_equivalence_substitute]
    unfold star_13_01
    rw [substitute_always, implication_substitute,
      substitute_always, implication_substitute]
    cases b <;> rfl
  let orderOM := MixedOrder.maxRightLeftAbsorb equalityScopeOrder order
  let orderMS := Eq.trans (bindOrderMaxLeft memberOrder memberOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (natMaxSelf memberOrder))
  let orderOS := Eq.trans (bindOrderMaxLeft order memberOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort) orderOM)
  let orderOMS := Eq.trans (congrArg (max order) orderMS) orderOS
  let bodyExistentialDisjunction := Eq.mp (congrArg signature.Disjunction
    orderMS.symm) existentialDisjunction
  have line1c := star_10_24 existential memberNegation
    bodyExistentialDisjunction body b
  let line1Negation : MixedOrder.TernaryNegations signature := {
    pOrder := order
    qOrder := memberOrder
    rOrder := resultOrder
    p := vocabulary.negation
    q := memberNegation
    r := resultNegation
    pq := Eq.mp (congrArg signature.Negation orderOM.symm) memberNegation
    pr := Eq.mp (congrArg signature.Negation orderOS.symm) resultNegation
    qr := Eq.mp (congrArg signature.Negation orderMS.symm) resultNegation
    pqr := Eq.mp (congrArg signature.Negation orderOMS.symm) resultNegation
  }
  let line1Disjunction : MixedOrder.TernaryDisjunctions signature
      line1Negation := {
    p := vocabulary.disjunction
    q := memberDisjunction
    r := resultDisjunction
    pq := Eq.mp (congrArg signature.Disjunction orderOM.symm)
      memberDisjunction
    pr := Eq.mp (congrArg signature.Disjunction orderOS.symm)
      existentialDisjunction
    qr := bodyExistentialDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction orderOMS.symm)
      resultDisjunction
  }
  have line1bEquality :
      Eq.mp (congrArg (Formula signature real []) orderOM)
        (MixedOrder.ternaryInterpret line1Negation line1Disjunction
          psiB (body.instantiate b) existentialMember
          (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)) =
      MixedOrder.binaryInterpret bodyNegation bodyDisjunction
        (Formula.always identityUniversal reflexiveBody) psiB
        (MixedOrder.binaryQ ⊃ₚ
          (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) := by
    rw [bodyAtB]
    rfl
  have line1bCast := Derivation.castAssertion line1bEquality line1b
  have line1b' := star13_uncastAssertionOrder orderOM
    (MixedOrder.ternaryInterpret line1Negation line1Disjunction
      psiB (body.instantiate b) existentialMember
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)) line1bCast
  change ⊢ᵣ MixedOrder.ternaryInterpret line1Negation line1Disjunction
    psiB (body.instantiate b) existentialMember
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR) at line1c
  have line1 := star13_ternarySyll line1Negation line1Disjunction
    psiB (body.instantiate b) existentialMember line1b' line1c
  let orderEI := Eq.trans (bindOrderMaxRight identityOrder identityOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (natMaxSelf identityOrder))
  let orderME := MixedOrder.maxLeftRightAbsorb equalityScopeOrder order
  let orderMI := Eq.trans
    (MixedOrder.maxAssoc equalityScopeOrder order identityOrder)
    (Eq.trans
      (congrArg (max equalityScopeOrder)
        (MixedOrder.maxComm order identityOrder))
      (Eq.trans
        (MixedOrder.maxAssoc equalityScopeOrder identityOrder order).symm
        (congrArg (fun leftOrder => max leftOrder order) orderEI)))
  let orderMO := MixedOrder.maxRightAbsorb equalityScopeOrder order
  let orderMIO := Eq.trans
    (congrArg (max memberOrder)
      (MixedOrder.maxComm identityOrder order))
    (Eq.trans
      (MixedOrder.maxAssoc memberOrder order identityOrder).symm
      (Eq.trans (congrArg (fun leftOrder => max leftOrder identityOrder)
        orderMO) orderMI))
  let cValue : Term signature (sort :: real) [] sort := .real .zero
  let psiC := (psi.weakenReal (fresh := sort)).instantiate cValue
  let psiB' := (psi.weakenReal (fresh := sort)).instantiate bValue
  let equalityMatrixC : Formula signature (sort :: real) [sort]
      identityOrder :=
    equivalence identityNegation identityOrderDisjunction
      (star_13_01 vocabulary (.apparent (.zero : Var [sort] sort))
        bValue.weaken)
      (star_13_01 vocabulary (.apparent (.zero : Var [sort] sort))
        cValue.weaken)
  let universalEqualityC := Formula.always identityUniversal equalityMatrixC
  let identityBB := star_13_01 vocabulary bValue bValue
  let identityBC := star_13_01 vocabulary bValue cValue
  let equalityBBC := equivalence identityNegation identityOrderDisjunction
    identityBB identityBC
  have universalAtC :
      (Formula.always identityUniversal
        (star_13_192_identityMatrix vocabulary identityNegation
          identityOrderDisjunction b)).weakenReal.instantiate cValue =
      universalEqualityC := by
    change (Formula.always identityUniversal
      (star_13_192_identityMatrix vocabulary identityNegation
        identityOrderDisjunction b).weakenReal).instantiate cValue = _
    rw [Formula.instantiate, substitute_always]
    unfold universalEqualityC equalityMatrixC
    unfold star_13_192_identityMatrix
    rw [star13_equivalence_weakenReal, star13_equivalence_substitute,
      star13_identity_weakenReal, star13_identity_weakenReal]
    unfold star_13_01
    rw [substitute_always, implication_substitute,
      substitute_always, implication_substitute]
    cases b <;> rfl
  have bodyAtC : body.weakenReal.instantiate cValue =
      mixedConjunction equalityScopeNegation vocabulary.negation
        memberNegation memberDisjunction universalEqualityC psiC := by
    unfold body star_13_192_body psiC
    rw [star13_mixedConjunction_weakenReal,
      star13_mixedConjunction_instantiate]
    rw [universalAtC]
  have line2a := MixedOrder.star_3_26 bodyNegation bodyDisjunction
    universalEqualityC psiC
  let equalitySpecializationDisjunction := Eq.mp
    (congrArg signature.Disjunction orderEI.symm) equalityScopeDisjunction
  have line2b0 := star_10_1 identityUniversal equalityScopeNegation
    equalitySpecializationDisjunction equalityMatrixC bValue
  have equalityAtB : equalityMatrixC.instantiate bValue = equalityBBC := by
    unfold equalityMatrixC equalityBBC identityBB identityBC
    rw [Formula.instantiate, star13_equivalence_substitute]
    unfold star_13_01
    rw [substitute_always, implication_substitute,
      substitute_always, implication_substitute]
    cases b <;> rfl
  have line2b := Derivation.castAssertion
    (congrArg (fun consequent => mixedImplication equalityScopeNegation
      equalitySpecializationDisjunction universalEqualityC consequent)
      equalityAtB).symm line2b0
  let specializationNegation : MixedOrder.TernaryNegations signature := {
    pOrder := memberOrder
    qOrder := equalityScopeOrder
    rOrder := identityOrder
    p := memberNegation
    q := equalityScopeNegation
    r := identityNegation
    pq := Eq.mp (congrArg signature.Negation orderME.symm) memberNegation
    pr := Eq.mp (congrArg signature.Negation orderMI.symm) memberNegation
    qr := Eq.mp (congrArg signature.Negation orderEI.symm)
      equalityScopeNegation
    pqr := Eq.mp (congrArg signature.Negation
      (Eq.trans (congrArg (max memberOrder) orderEI) orderME).symm)
      memberNegation
  }
  let specializationDisjunction : MixedOrder.TernaryDisjunctions signature
      specializationNegation := {
    p := memberDisjunction
    q := equalityScopeDisjunction
    r := identityOrderDisjunction
    pq := Eq.mp (congrArg signature.Disjunction orderME.symm)
      memberDisjunction
    pr := Eq.mp (congrArg signature.Disjunction orderMI.symm)
      memberDisjunction
    qr := equalitySpecializationDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (Eq.trans (congrArg (max memberOrder) orderEI) orderME).symm)
      memberDisjunction
  }
  have line2aEquality :
      Eq.mp (congrArg (Formula signature (sort :: real) []) orderME)
        (MixedOrder.ternaryInterpret specializationNegation
          specializationDisjunction
          (body.weakenReal.instantiate cValue) universalEqualityC equalityBBC
          (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)) =
      MixedOrder.binaryInterpret bodyNegation bodyDisjunction
        universalEqualityC psiC
        ((MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ) ⊃ₚ
          MixedOrder.binaryP) := by
    rw [bodyAtC]
    rfl
  have line2aCast := Derivation.castAssertion line2aEquality line2a
  have line2a' := star13_uncastAssertionOrder orderME
    (MixedOrder.ternaryInterpret specializationNegation
      specializationDisjunction
      (body.weakenReal.instantiate cValue) universalEqualityC equalityBBC
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)) line2aCast
  change ⊢ᵣ MixedOrder.ternaryInterpret specializationNegation
    specializationDisjunction
    (body.weakenReal.instantiate cValue) universalEqualityC equalityBBC
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR) at line2b
  have line2c := star13_ternarySyll specializationNegation
    specializationDisjunction (body.weakenReal.instantiate cValue)
    universalEqualityC equalityBBC line2a' line2b
  have line2d0 := star_13_15 vocabulary identityNegation
    identityOrderDisjunction bValue
  have line2d := star13_reflexiveEquivalence identityNegation
    identityOrderDisjunction identityBB identityBC line2d0
  have line2e := MixedOrder.star_3_27 bodyNegation bodyDisjunction
    universalEqualityC psiC
  let line2fNegation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseNegation
  }
  let line2fDisjunction : MixedOrder.TernaryDisjunctions signature
      line2fNegation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseDisjunction
  }
  let negPsiB : Formula signature (sort :: real) [] order :=
    (Formula.neg vocabulary.negation
      (psi.weakenReal (fresh := sort))).instantiate
      bValue
  let negPsiC : Formula signature (sort :: real) [] order :=
    (Formula.neg vocabulary.negation
      (psi.weakenReal (fresh := sort))).instantiate
      cValue
  have line2f0 := star_13_13 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation substitutionResultNegation
    reducibilityDisjunction identityOrderDisjunction
    reducibilityIdentityDisjunction reducibilityBaseDisjunction
    substitutionResultDisjunction reducibilityScopeUniversal
    reducibilityScopeNegation reducibilityScopeDisjunction
    existentialTargetDisjunction
    (.neg vocabulary.negation (psi.weakenReal (fresh := sort))) bValue cValue
  change ⊢ᵣ star_13_13_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    (.neg vocabulary.negation (psi.weakenReal (fresh := sort)))
    bValue cValue at line2f0
  unfold star_13_13_formula at line2f0
  change ⊢ᵣ star13_bridgeInterpret line2fNegation line2fDisjunction
    identityBC identityBC negPsiB negPsiC negPsiB negPsiC
    star13_13_targetElement at line2f0
  have negPsiBEquality : negPsiB = .neg vocabulary.negation psiB' := by
    rfl
  have negPsiCEquality : negPsiC = .neg vocabulary.negation psiC := by
    rfl
  have line2f := star13_ramified13ReverseSubstitution
    line2fNegation line2fDisjunction identityBC identityBC
    negPsiB negPsiC negPsiB negPsiC psiC psiB'
    negPsiBEquality negPsiCEquality line2f0
  let line2Negation : MixedOrder.TernaryNegations signature := {
    pOrder := memberOrder
    qOrder := identityOrder
    rOrder := order
    p := memberNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation orderMI.symm) memberNegation
    pr := Eq.mp (congrArg signature.Negation orderMO.symm) memberNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation orderMIO.symm) memberNegation
  }
  let line2Disjunction : MixedOrder.TernaryDisjunctions signature
      line2Negation := {
    p := memberDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction orderMI.symm)
      memberDisjunction
    pr := Eq.mp (congrArg signature.Disjunction orderMO.symm)
      memberDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction orderMIO.symm)
      memberDisjunction
  }
  change ⊢ᵣ star13_fiveInterpret line2Negation line2Disjunction
    (body.weakenReal.instantiate cValue) equalityBBC identityBC psiC psiB'
    (star13_fiveA ⊃ₚ star13_fiveE) at line2c
  have line2eEquality :
      Eq.mp (congrArg (Formula signature (sort :: real) []) orderMO)
        (star13_fiveInterpret line2Negation line2Disjunction
          (body.weakenReal.instantiate cValue) equalityBBC identityBC psiC psiB'
          (star13_fiveA ⊃ₚ star13_fiveC)) =
      MixedOrder.binaryInterpret bodyNegation bodyDisjunction
        universalEqualityC psiC
        ((MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ) ⊃ₚ
          MixedOrder.binaryQ) := by
    rw [bodyAtC]
    rfl
  have line2eCast := Derivation.castAssertion line2eEquality line2e
  have line2e' := star13_uncastAssertionOrder orderMO
    (star13_fiveInterpret line2Negation line2Disjunction
      (body.weakenReal.instantiate cValue) equalityBBC identityBC psiC psiB'
      (star13_fiveA ⊃ₚ star13_fiveC)) line2eCast
  change ⊢ᵣ star13_fiveInterpret line2Negation line2Disjunction
    (body.weakenReal.instantiate cValue) equalityBBC identityBC psiC psiB'
    (star13_fiveE ⊃ₚ star13_fiveQ) at line2d
  have line2fEquality :
      star13_fiveInterpret line2Negation line2Disjunction
        (body.weakenReal.instantiate cValue) equalityBBC identityBC psiC psiB'
        ((star13_fiveQ ∧ₚ star13_fiveC) ⊃ₚ star13_fiveR) =
      star13_normalizedDisjunction
        (MixedOrder.maxRightAbsorb identityOrder order)
        identityBaseDisjunction
        (.neg identityBaseNegation
          (mixedConjunction identityNegation vocabulary.negation
            identityBaseNegation identityBaseDisjunction identityBC psiC))
        psiB' := by
    rfl
  have line2f' := Derivation.castAssertion line2fEquality.symm line2f
  have line2 := star13_ramifiedFiveBridge line2Negation line2Disjunction
    (body.weakenReal.instantiate cValue) equalityBBC identityBC psiC psiB'
    line2c line2e' line2d line2f'
  let memberPsiDisjunction := Eq.mp (congrArg signature.Disjunction
    orderMO.symm) memberDisjunction
  have line2Equality :
      star13_fiveInterpret line2Negation line2Disjunction
        (body.weakenReal.instantiate cValue) equalityBBC identityBC psiC psiB'
        (star13_fiveA ⊃ₚ star13_fiveR) =
      mixedImplication memberNegation memberPsiDisjunction
        (body.weakenReal.instantiate cValue) psiB' := by
    rfl
  have line2' := Derivation.castAssertion line2Equality line2
  let pointwise := mixedImplication memberNegation memberPsiDisjunction
    body (psiB.rename (fun v => .succ v))
  have pointwiseAt : pointwise.weakenReal.instantiate cValue =
      mixedImplication memberNegation memberPsiDisjunction
        (body.weakenReal.instantiate cValue) psiB' := by
    unfold pointwise
    rw [star13_mixedImplication_weakenReal,
      star13_mixedImplication_instantiate,
      Formula.closed_weakenReal_instantiate]
    unfold psiB psiB' bValue
    rw [star13_instantiate_weakenReal]
  have line3a := star_10_11 implicationUniversal pointwise
    (Derivation.castAssertion pointwiseAt line2')
  let forwardEquality := congrArg
    (fun matrixOrder => bindOrder matrixOrder sort) orderMO
  let forwardNegation := Eq.mp (congrArg signature.Negation
    forwardEquality.symm) resultNegation
  let forwardDisjunction := Eq.mp (congrArg signature.Disjunction
    forwardEquality.symm) resultDisjunction
  let leftMember := star_10_23_left implicationUniversal memberNegation
    memberPsiDisjunction body psiB
  let rightMember := star_10_23_right existential existential.universal
    implicationUniversal memberNegation memberPsiDisjunction body psiB
  have line3b0 := star_10_23 existential existential.universal
    implicationUniversal memberNegation memberPsiDisjunction
    forwardNegation forwardDisjunction body psiB
  change ⊢ᵣ star_4_01 forwardNegation forwardDisjunction
    leftMember rightMember at line3b0
  have line3b1 := star_3_26 forwardNegation forwardDisjunction
    (implication forwardNegation forwardDisjunction leftMember rightMember)
    (implication forwardNegation forwardDisjunction rightMember leftMember)
  have line3b := star13_detach forwardNegation forwardDisjunction
    (star_4_01 forwardNegation forwardDisjunction leftMember rightMember)
    (implication forwardNegation forwardDisjunction leftMember rightMember)
    line3b0 line3b1
  change ⊢ᵣ leftMember at line3a
  have line3c := star13_detach forwardNegation forwardDisjunction
    leftMember rightMember line3a line3b
  have line3 := star13_castAssertionOrder forwardEquality rightMember line3c
  have line1Cast := star13_castAssertionOrder orderOS
    (MixedOrder.ternaryInterpret line1Negation line1Disjunction
      psiB (body.instantiate b) existentialMember
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)) line1
  have line1Equality :
      Eq.mp (congrArg (Formula signature real []) orderOS)
        (MixedOrder.ternaryInterpret line1Negation line1Disjunction
          psiB (body.instantiate b) existentialMember
          (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)) =
      star13_normalizedDisjunction orderOS existentialDisjunction
        (.neg vocabulary.negation psiB) existentialMember := by
    rfl
  have line1' := Derivation.castAssertion line1Equality line1Cast
  let forward := Eq.mp (congrArg (Formula signature real []) forwardEquality)
    rightMember
  let reverse := star13_normalizedDisjunction orderOS
    existentialDisjunction (.neg vocabulary.negation psiB) existentialMember
  change ⊢ᵣ forward at line3
  change ⊢ᵣ reverse at line1'
  have line4a := star_3_2 resultNegation resultDisjunction forward reverse
  have line4b := star13_detach resultNegation resultDisjunction forward
    (implication resultNegation resultDisjunction reverse
      (conjunction resultNegation resultDisjunction forward reverse))
    line3 line4a
  have line4 := star13_detach resultNegation resultDisjunction reverse
    (conjunction resultNegation resultDisjunction forward reverse)
    line1' line4b
  change ⊢ᵣ star_13_192_formula vocabulary identityUniversal
    identityNegation identityOrderDisjunction equalityScopeNegation
    memberNegation memberDisjunction existential existentialDisjunction
    implicationUniversal resultNegation resultDisjunction psi b
  unfold star_13_192_formula
  exact line4

def star_13_193_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :=
  let identityOrder := bindOrder order (.function [sort] order 0)
  let identity := star_13_01 vocabulary x y
  let psiX := psi.instantiate x
  let psiY := psi.instantiate y
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseDisjunction
  }
  star13_bridgeInterpret negation disjunction identity identity
    psiX psiY psiX psiY star13_193_formulaElement

/-- Audited scope reading of ✱13·193. -/
def star_13_193_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : φx . x = y .≡ . φy . x = y"
  parsed := .assertion (star_13_193_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    psi x y)

/-- ✱13·193, following PM's four printed lines.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_193
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (substitutionResultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction (bindOrder order sort))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (substitutionResultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Derivation (star_13_193_reading vocabulary identityNegation
      identityOrderDisjunction identityBaseNegation
      identityBaseDisjunction psi x y).parsed := by
  let identityOrder := bindOrder order (.function [sort] order 0)
  let identity := star_13_01 vocabulary x y
  let psiX := psi.instantiate x
  let psiY := psi.instantiate y
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseDisjunction
  }
  have line1 := MixedOrder.transport MixedOrder.TernarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (MixedOrder.ternaryTautology negation disjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => identity)
    star13_bridgeSupport
    (star13_bridgeValuation negation identity identity
      psiX psiY psiX psiY)
    (PM.FirstEdition.Volume1.Star3.star_3_27
      star13_bridgeX star13_bridgeE)
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    identity identity psiX psiY psiX psiY star13_193_line1Element at line1
  have line2 := star_13_13 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation
    substitutionResultNegation reducibilityDisjunction
    identityOrderDisjunction reducibilityIdentityDisjunction
    reducibilityBaseDisjunction substitutionResultDisjunction
    reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction psi x y
  change ⊢ᵣ star_13_13_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    psi x y at line2
  unfold star_13_13_formula at line2
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    identity identity psiX psiY psiX psiY star13_193_line2Element at line2
  have line3 := star13_ramified193Forward negation disjunction
    identity identity psiX psiY psiX psiY line1 line2
  let negPsiX := (Formula.neg vocabulary.negation psi).instantiate x
  let negPsiY := (Formula.neg vocabulary.negation psi).instantiate y
  have line4a := star_13_13 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation
    substitutionResultNegation reducibilityDisjunction
    identityOrderDisjunction reducibilityIdentityDisjunction
    reducibilityBaseDisjunction substitutionResultDisjunction
    reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction
    (Formula.neg vocabulary.negation psi) x y
  change ⊢ᵣ star_13_13_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    (Formula.neg vocabulary.negation psi) x y at line4a
  unfold star_13_13_formula at line4a
  change ⊢ᵣ star13_bridgeInterpret negation disjunction
    identity identity negPsiX negPsiY negPsiX negPsiY
    star13_13_targetElement at line4a
  have negPsiXEquality : negPsiX = .neg vocabulary.negation psiX := by
    rfl
  have negPsiYEquality : negPsiY = .neg vocabulary.negation psiY := by
    rfl
  rw [negPsiXEquality, negPsiYEquality] at line4a
  have line4 := star13_ramified193Reverse negation disjunction
    identity identity psiX psiY psiX psiY line4a
  have result := star13_ramified193Join negation disjunction
    identity identity psiX psiY psiX psiY line3 line4
  change ⊢ᵣ star_13_193_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    psi x y
  unfold star_13_193_formula
  exact result

/-- Audited scope reading of ✱13·194. -/
def star_13_194_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort)
    : ClaimReading signature real :=
  let identityOrder := bindOrder order (.function [sort] order 0)
  let identity := star_13_01 vocabulary x y
  let psiX := psi.instantiate x
  let psiY := psi.instantiate y
  let ternaryNegation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseNegation
  }
  let ternaryDisjunction : MixedOrder.TernaryDisjunctions signature
      ternaryNegation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseDisjunction
  }
  let leftElement := star13_bridgeX ∧ₚ star13_bridgeE
  let rightElement := star13_bridgeX ∧ₚ
    (star13_bridgeY ∧ₚ star13_bridgeE)
  let targetElement := leftElement ≡ₚ
    rightElement
  {
    printed := "⊢ : φx . x = y .≡ . φx . φy . x = y"
    parsed := .assertion (star13_bridgeInterpret ternaryNegation
      ternaryDisjunction identity identity psiX psiY psiX psiY
      targetElement)
  }

/-- ✱13·194, by the printed `✱13·13 . ✱4·71` citation.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_194
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (substitutionResultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction (bindOrder order sort))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (substitutionResultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Derivation (star_13_194_reading vocabulary identityNegation
      identityOrderDisjunction identityBaseNegation identityBaseDisjunction
      psi x y).parsed := by
  let identityOrder := bindOrder order (.function [sort] order 0)
  let identity := star_13_01 vocabulary x y
  let psiX := psi.instantiate x
  let psiY := psi.instantiate y
  let ternaryNegation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseNegation
  }
  let ternaryDisjunction : MixedOrder.TernaryDisjunctions signature
      ternaryNegation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseDisjunction
  }
  let leftElement := star13_bridgeX ∧ₚ star13_bridgeE
  let sourceElement := leftElement ⊃ₚ star13_bridgeY
  let directRightElement := leftElement ∧ₚ star13_bridgeY
  let rightElement := star13_bridgeX ∧ₚ
    (star13_bridgeY ∧ₚ star13_bridgeE)
  let directTargetElement := leftElement ≡ₚ directRightElement
  let targetElement := leftElement ≡ₚ rightElement
  have line1 := star_13_13 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation
    substitutionResultNegation reducibilityDisjunction
    identityOrderDisjunction reducibilityIdentityDisjunction
    reducibilityBaseDisjunction substitutionResultDisjunction
    reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction psi x y
  change ⊢ᵣ star_13_13_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    psi x y at line1
  unfold star_13_13_formula at line1
  change ⊢ᵣ star13_bridgeInterpret ternaryNegation ternaryDisjunction
    identity identity psiX psiY psiX psiY sourceElement at line1
  have line2a := MixedOrder.transport MixedOrder.TernarySupport.combine
    ternaryNegation.toVocabulary ternaryDisjunction.toVocabulary
    (MixedOrder.ternaryTautology ternaryNegation ternaryDisjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => identity)
    star13_bridgeSupport
    (star13_bridgeValuation ternaryNegation identity identity
      psiX psiY psiX psiY)
    (PM.FirstEdition.Volume1.Star4.star_4_71
      leftElement star13_bridgeY)
  change ⊢ᵣ star13_bridgeInterpret ternaryNegation ternaryDisjunction
    identity identity psiX psiY psiX psiY
    (sourceElement ≡ₚ directTargetElement) at line2a
  have line2b := MixedOrder.transport MixedOrder.TernarySupport.combine
    ternaryNegation.toVocabulary ternaryDisjunction.toVocabulary
    (MixedOrder.ternaryTautology ternaryNegation ternaryDisjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => identity)
    star13_bridgeSupport
    (star13_bridgeValuation ternaryNegation identity identity
      psiX psiY psiX psiY)
    (PM.FirstEdition.Volume1.Star3.star_3_26
      (sourceElement ⊃ₚ directTargetElement)
      (directTargetElement ⊃ₚ sourceElement))
  change ⊢ᵣ star13_bridgeInterpret ternaryNegation ternaryDisjunction
    identity identity psiX psiY psiX psiY
    ((sourceElement ≡ₚ directTargetElement) ⊃ₚ
      (sourceElement ⊃ₚ directTargetElement)) at line2b
  have line2 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine ternaryNegation .qr .qr)
    ternaryNegation.qr ternaryDisjunction.qr
    (star13_bridgeInterpret ternaryNegation ternaryDisjunction
      identity identity psiX psiY psiX psiY
      (sourceElement ≡ₚ directTargetElement))
    (star13_bridgeInterpret ternaryNegation ternaryDisjunction
      identity identity psiX psiY psiX psiY
      (sourceElement ⊃ₚ directTargetElement)) line2a line2b
  have line3 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine ternaryNegation .qr .qr)
    ternaryNegation.qr ternaryDisjunction.qr
    (star13_bridgeInterpret ternaryNegation ternaryDisjunction
      identity identity psiX psiY psiX psiY sourceElement)
    (star13_bridgeInterpret ternaryNegation ternaryDisjunction
      identity identity psiX psiY psiX psiY directTargetElement)
    line1 line2
  have line4aElementary :
      PM.Derivation (directTargetElement ⊃ₚ targetElement) := by
    let syll : ∀ p q r : PM.Elementary Star13BridgeContext,
        PM.Derivation (p ⊃ₚ q) → PM.Derivation (q ⊃ₚ r) →
          PM.Derivation (p ⊃ₚ r) := by
      intro p q r lineA lineB
      exact PM.Derivation.detach lineA
        (PM.Derivation.detach lineB
          (PM.FirstEdition.Volume1.Star2.star_2_05 p q r))
    let joinUnder : ∀ h p q : PM.Elementary Star13BridgeContext,
        PM.Derivation (h ⊃ₚ p) → PM.Derivation (h ⊃ₚ q) →
          PM.Derivation (h ⊃ₚ (p ∧ₚ q)) := by
      intro h p q lineA lineB
      have lineC := PM.Derivation.detach lineB
        (PM.Derivation.detach lineA
          (PM.FirstEdition.Volume1.Star3.star_3_2
            (h ⊃ₚ p) (h ⊃ₚ q)))
      have lineD := PM.Derivation.detach
        (PM.FirstEdition.Volume1.Star4.star_4_76 h p q)
        (PM.FirstEdition.Volume1.Star3.star_3_26 _ _)
      exact PM.Derivation.detach lineC lineD
    have line4a1a := PM.FirstEdition.Volume1.Star3.star_3_26
      leftElement star13_bridgeY
    have line4a1b := syll directRightElement leftElement star13_bridgeX
      line4a1a (PM.FirstEdition.Volume1.Star3.star_3_26
        star13_bridgeX star13_bridgeE)
    have line4a1c := syll directRightElement leftElement star13_bridgeE
      line4a1a (PM.FirstEdition.Volume1.Star3.star_3_27
        star13_bridgeX star13_bridgeE)
    have line4a1d := PM.FirstEdition.Volume1.Star3.star_3_27
      leftElement star13_bridgeY
    have line4a1e := joinUnder directRightElement star13_bridgeY
      star13_bridgeE line4a1d line4a1c
    have line4a1 := joinUnder directRightElement star13_bridgeX
      (star13_bridgeY ∧ₚ star13_bridgeE) line4a1b line4a1e
    have line4a2a := PM.FirstEdition.Volume1.Star3.star_3_26
      star13_bridgeX (star13_bridgeY ∧ₚ star13_bridgeE)
    have line4a2b := PM.FirstEdition.Volume1.Star3.star_3_27
      star13_bridgeX (star13_bridgeY ∧ₚ star13_bridgeE)
    have line4a2c := syll rightElement
      (star13_bridgeY ∧ₚ star13_bridgeE) star13_bridgeY line4a2b
      (PM.FirstEdition.Volume1.Star3.star_3_26
        star13_bridgeY star13_bridgeE)
    have line4a2d := syll rightElement
      (star13_bridgeY ∧ₚ star13_bridgeE) star13_bridgeE line4a2b
      (PM.FirstEdition.Volume1.Star3.star_3_27
        star13_bridgeY star13_bridgeE)
    have line4a2e := joinUnder rightElement star13_bridgeX
      star13_bridgeE line4a2a line4a2d
    have line4a2 := joinUnder rightElement leftElement
      star13_bridgeY line4a2e line4a2c
    have line4a3 := PM.Derivation.detach line4a2
      (PM.Derivation.detach line4a1
        (PM.FirstEdition.Volume1.Star3.star_3_2
          (directRightElement ⊃ₚ rightElement)
          (rightElement ⊃ₚ directRightElement)))
    have line4a4 := PM.Derivation.detach line4a3
      (PM.FirstEdition.Volume1.Star3.star_3_21
        directTargetElement
        (directRightElement ≡ₚ rightElement))
    have line4a5 := PM.FirstEdition.Volume1.Star4.star_4_22
      leftElement directRightElement rightElement
    exact PM.Derivation.detach line4a4
      (PM.Derivation.detach line4a5
        (PM.FirstEdition.Volume1.Star2.star_2_05 directTargetElement
          (directTargetElement ∧ₚ
            (directRightElement ≡ₚ rightElement)) targetElement))
  have line4a := MixedOrder.transport MixedOrder.TernarySupport.combine
    ternaryNegation.toVocabulary ternaryDisjunction.toVocabulary
    (MixedOrder.ternaryTautology ternaryNegation ternaryDisjunction)
    (fun _ => MixedOrder.TernarySupport.p) (fun _ => identity)
    star13_bridgeSupport
    (star13_bridgeValuation ternaryNegation identity identity
      psiX psiY psiX psiY) line4aElementary
  change ⊢ᵣ star13_bridgeInterpret ternaryNegation ternaryDisjunction
    identity identity psiX psiY psiX psiY
    (directTargetElement ⊃ₚ targetElement) at line4a
  have line4 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine ternaryNegation .qr .qr)
    ternaryNegation.qr ternaryDisjunction.qr
    (star13_bridgeInterpret ternaryNegation ternaryDisjunction
      identity identity psiX psiY psiX psiY directTargetElement)
    (star13_bridgeInterpret ternaryNegation ternaryDisjunction
      identity identity psiX psiY psiX psiY targetElement)
    line3 line4a
  exact line4

def star_13_195_body
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x : Term signature real [] sort) :=
  let y : Term signature real [sort] sort := .apparent .zero
  mixedConjunction identityNegation vocabulary.negation
    identityBaseNegation identityBaseDisjunction
    (star_13_01 vocabulary y x.weaken) psi

def star_13_195_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder order (.function [sort] order 0)) order))
    (implicationUniversal : signature.Universal sort
      (max (max (bindOrder order (.function [sort] order 0)) order) order))
    (resultNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (resultDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (psi : Formula signature real [sort] order)
    (x : Term signature real [] sort) :=
  let identityOrder := bindOrder order (.function [sort] order 0)
  let memberOrder := max identityOrder order
  let body := star_13_195_body vocabulary identityNegation
    identityBaseNegation identityBaseDisjunction psi x
  let existentialMember := Formula.sometimes existential body
  let psiX := psi.instantiate x
  let memberPsiEquality := MixedOrder.maxRightAbsorb identityOrder order
  let memberPsiDisjunction := Eq.mp (congrArg signature.Disjunction
    memberPsiEquality.symm) identityBaseDisjunction
  let forwardEquality := congrArg
    (fun matrixOrder => bindOrder matrixOrder sort) memberPsiEquality
  let forward := Eq.mp (congrArg (Formula signature real []) forwardEquality)
    (star_10_23_right existential existential.universal implicationUniversal
      identityBaseNegation memberPsiDisjunction body psiX)
  let reverseEquality := Eq.trans (bindOrderMaxLeft order memberOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightLeftAbsorb identityOrder order))
  let reverse := star13_normalizedDisjunction reverseEquality
    resultDisjunction (.neg vocabulary.negation psiX) existentialMember
  conjunction resultNegation resultDisjunction forward reverse

/-- Audited scope reading of ✱13·195. -/
def star_13_195_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder order (.function [sort] order 0)) order))
    (implicationUniversal : signature.Universal sort
      (max (max (bindOrder order (.function [sort] order 0)) order) order))
    (resultNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (resultDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (psi : Formula signature real [sort] order)
    (x : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : (∃y). y = x . φy .≡ . φx"
  parsed := .assertion (star_13_195_formula vocabulary identityNegation
    identityBaseNegation identityBaseDisjunction existential
    implicationUniversal resultNegation resultDisjunction psi x)

/-- ✱13·195, following PM's two printed lines.
`assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_195
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityOrderDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (identityBaseNegation : signature.Negation
      (max (bindOrder order (.function [sort] order 0)) order))
    (identityBaseDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder order (.function [sort] order 0)) order))
    (implicationUniversal : signature.Universal sort
      (max (max (bindOrder order (.function [sort] order 0)) order) order))
    (resultNegation : signature.Negation
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (resultDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order (.function [sort] order 0)) order) sort))
    (psi : Formula signature real [sort] order)
    (x : Term signature real [] sort)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (reducibilityNegation : signature.Negation (bindOrder order sort))
    (reducibilityIdentityNegation : signature.Negation
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseNegation : signature.Negation
      (max (bindOrder order sort) order))
    (substitutionResultNegation : signature.Negation
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityDisjunction : signature.Disjunction (bindOrder order sort))
    (reducibilityIdentityDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (bindOrder order (.function [sort] order 0))))
    (reducibilityBaseDisjunction : signature.Disjunction
      (max (bindOrder order sort) order))
    (substitutionResultDisjunction : signature.Disjunction
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeUniversal : signature.Universal
      (.function [sort] order 0)
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order)))
    (reducibilityScopeNegation : signature.Negation
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (reducibilityScopeDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder order sort)
          (max (bindOrder order (.function [sort] order 0)) order))
        (.function [sort] order 0)))
    (existentialTargetDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order))) :
    Derivation (star_13_195_reading vocabulary identityNegation
      identityBaseNegation identityBaseDisjunction existential implicationUniversal
      resultNegation resultDisjunction psi x).parsed := by
  let identityOrder := bindOrder order (.function [sort] order 0)
  let memberOrder := max identityOrder order
  let resultOrder := bindOrder memberOrder sort
  let body := star_13_195_body vocabulary identityNegation
    identityBaseNegation identityBaseDisjunction psi x
  let existentialMember := Formula.sometimes existential body
  let psiX := psi.instantiate x
  let identityXX := star_13_01 vocabulary x x
  let bodyNegation : MixedOrder.BinaryNegations signature := {
    leftOrder := identityOrder
    rightOrder := order
    left := identityNegation
    right := vocabulary.negation
    both := identityBaseNegation
  }
  let bodyDisjunction : MixedOrder.BinaryDisjunctions signature
      bodyNegation := {
    left := identityOrderDisjunction
    right := vocabulary.disjunction
    both := identityBaseDisjunction
  }
  have line1a0 := star_13_15 vocabulary identityNegation
    identityOrderDisjunction x
  have line1a := star13_binaryPairUnderRight bodyNegation bodyDisjunction
    identityXX psiX line1a0
  have bodyAtX : body.instantiate x =
      mixedConjunction identityNegation vocabulary.negation
        identityBaseNegation identityBaseDisjunction identityXX psiX := by
    unfold body star_13_195_body identityXX psiX
    rw [star13_mixedConjunction_instantiate]
    unfold star_13_01
    rw [Formula.instantiate, substitute_always, implication_substitute]
    cases x <;> rfl
  let orderOM := MixedOrder.maxRightLeftAbsorb identityOrder order
  let orderMS := Eq.trans (bindOrderMaxLeft memberOrder memberOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (natMaxSelf memberOrder))
  let orderOS := Eq.trans (bindOrderMaxLeft order memberOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort) orderOM)
  let orderOMS := Eq.trans (congrArg (max order) orderMS) orderOS
  let bodyExistentialDisjunction := Eq.mp (congrArg signature.Disjunction
    orderMS.symm) resultDisjunction
  have line1b := star_10_24 existential identityBaseNegation
    bodyExistentialDisjunction body x
  let line1Negation : MixedOrder.TernaryNegations signature := {
    pOrder := order
    qOrder := memberOrder
    rOrder := resultOrder
    p := vocabulary.negation
    q := identityBaseNegation
    r := resultNegation
    pq := Eq.mp (congrArg signature.Negation orderOM.symm)
      identityBaseNegation
    pr := Eq.mp (congrArg signature.Negation orderOS.symm) resultNegation
    qr := Eq.mp (congrArg signature.Negation orderMS.symm) resultNegation
    pqr := Eq.mp (congrArg signature.Negation orderOMS.symm) resultNegation
  }
  let line1Disjunction : MixedOrder.TernaryDisjunctions signature
      line1Negation := {
    p := vocabulary.disjunction
    q := identityBaseDisjunction
    r := resultDisjunction
    pq := Eq.mp (congrArg signature.Disjunction orderOM.symm)
      identityBaseDisjunction
    pr := Eq.mp (congrArg signature.Disjunction orderOS.symm)
      resultDisjunction
    qr := bodyExistentialDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction orderOMS.symm)
      resultDisjunction
  }
  have line1aEquality :
      Eq.mp (congrArg (Formula signature real []) orderOM)
        (MixedOrder.ternaryInterpret line1Negation line1Disjunction
          psiX (body.instantiate x) existentialMember
          (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)) =
      MixedOrder.binaryInterpret bodyNegation bodyDisjunction identityXX psiX
        (MixedOrder.binaryQ ⊃ₚ
          (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ)) := by
    rw [bodyAtX]
    rfl
  have line1aCast := Derivation.castAssertion line1aEquality line1a
  have line1a' := star13_uncastAssertionOrder orderOM
    (MixedOrder.ternaryInterpret line1Negation line1Disjunction
      psiX (body.instantiate x) existentialMember
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)) line1aCast
  change ⊢ᵣ MixedOrder.ternaryInterpret line1Negation line1Disjunction
    psiX (body.instantiate x) existentialMember
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR) at line1b
  have line1 := star13_ternarySyll line1Negation line1Disjunction
    psiX (body.instantiate x) existentialMember line1a' line1b
  let yValue : Term signature (sort :: real) [] sort := .real .zero
  let xValue := x.weakenReal (fresh := sort)
  let identityYX := star_13_01 vocabulary yValue xValue
  let psiY := (psi.weakenReal (fresh := sort)).instantiate yValue
  let psiX' := (psi.weakenReal (fresh := sort)).instantiate xValue
  let pointNegation : MixedOrder.TernaryNegations signature := {
    pOrder := identityOrder
    qOrder := identityOrder
    rOrder := order
    p := identityNegation
    q := identityNegation
    r := vocabulary.negation
    pq := Eq.mp (congrArg signature.Negation
      (natMaxSelf identityOrder).symm) identityNegation
    pr := identityBaseNegation
    qr := identityBaseNegation
    pqr := Eq.mp (congrArg signature.Negation
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseNegation
  }
  let pointDisjunction : MixedOrder.TernaryDisjunctions signature
      pointNegation := {
    p := identityOrderDisjunction
    q := identityOrderDisjunction
    r := vocabulary.disjunction
    pq := Eq.mp (congrArg signature.Disjunction
      (natMaxSelf identityOrder).symm) identityOrderDisjunction
    pr := identityBaseDisjunction
    qr := identityBaseDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (MixedOrder.maxLeftAbsorb identityOrder order).symm)
      identityBaseDisjunction
  }
  have line2a := star_13_13 vocabulary reducibilityExistential
    argumentUniversal identityNegation identityBaseDisjunction
    reducibilityNegation reducibilityIdentityNegation
    reducibilityBaseNegation identityBaseNegation
    substitutionResultNegation reducibilityDisjunction
    identityOrderDisjunction reducibilityIdentityDisjunction
    reducibilityBaseDisjunction substitutionResultDisjunction
    reducibilityScopeUniversal reducibilityScopeNegation
    reducibilityScopeDisjunction existentialTargetDisjunction
    (psi.weakenReal (fresh := sort)) yValue xValue
  change ⊢ᵣ star_13_13_formula vocabulary identityNegation
    identityOrderDisjunction identityBaseNegation identityBaseDisjunction
    (psi.weakenReal (fresh := sort)) yValue xValue at line2a
  unfold star_13_13_formula at line2a
  change ⊢ᵣ star13_bridgeInterpret pointNegation pointDisjunction
    identityYX identityYX psiY psiX' psiY psiX'
    star13_13_targetElement at line2a
  have line2b := star13_ramified195Point pointNegation pointDisjunction
    identityYX identityYX psiY psiX' psiY psiX' line2a
  have bodyAtY : body.weakenReal.instantiate yValue =
      mixedConjunction identityNegation vocabulary.negation
        identityBaseNegation identityBaseDisjunction identityYX psiY := by
    unfold body star_13_195_body identityYX psiY
    rw [star13_mixedConjunction_weakenReal,
      star13_mixedConjunction_instantiate]
    rw [star13_identity_weakenReal]
    unfold star_13_01
    rw [Formula.instantiate, substitute_always, implication_substitute]
    cases x <;> rfl
  let memberPsiEquality := MixedOrder.maxRightAbsorb identityOrder order
  let memberPsiDisjunction := Eq.mp (congrArg signature.Disjunction
    memberPsiEquality.symm) identityBaseDisjunction
  let pointFormula := mixedImplication identityBaseNegation
    memberPsiDisjunction (body.weakenReal.instantiate yValue) psiX'
  have line2bEquality :
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        memberPsiEquality) pointFormula =
      star13_bridgeInterpret pointNegation pointDisjunction
        identityYX identityYX psiY psiX' psiY psiX'
        star13_195_pointElement := by
    unfold pointFormula
    rw [bodyAtY]
    rfl
  have line2bCast := Derivation.castAssertion line2bEquality line2b
  have line2c := star13_uncastAssertionOrder memberPsiEquality
    pointFormula line2bCast
  let pointwise := mixedImplication identityBaseNegation
    memberPsiDisjunction body (psiX.rename (fun v => .succ v))
  have pointwiseAt : pointwise.weakenReal.instantiate yValue = pointFormula := by
    unfold pointwise pointFormula
    rw [star13_mixedImplication_weakenReal,
      star13_mixedImplication_instantiate,
      Formula.closed_weakenReal_instantiate]
    unfold psiX psiX' xValue
    rw [star13_instantiate_weakenReal]
  have line2d := star_10_11 implicationUniversal pointwise
    (Derivation.castAssertion pointwiseAt line2c)
  let forwardEquality := congrArg
    (fun matrixOrder => bindOrder matrixOrder sort) memberPsiEquality
  let forwardNegation := Eq.mp (congrArg signature.Negation
    forwardEquality.symm) resultNegation
  let forwardDisjunction := Eq.mp (congrArg signature.Disjunction
    forwardEquality.symm) resultDisjunction
  let leftMember := star_10_23_left implicationUniversal
    identityBaseNegation memberPsiDisjunction body psiX
  let rightMember := star_10_23_right existential existential.universal
    implicationUniversal identityBaseNegation memberPsiDisjunction body psiX
  have line2e0 := star_10_23 existential existential.universal
    implicationUniversal identityBaseNegation memberPsiDisjunction
    forwardNegation forwardDisjunction body psiX
  change ⊢ᵣ star_4_01 forwardNegation forwardDisjunction
    leftMember rightMember at line2e0
  have line2e1 := star_3_26 forwardNegation forwardDisjunction
    (implication forwardNegation forwardDisjunction leftMember rightMember)
    (implication forwardNegation forwardDisjunction rightMember leftMember)
  have line2e := star13_detach forwardNegation forwardDisjunction
    (star_4_01 forwardNegation forwardDisjunction leftMember rightMember)
    (implication forwardNegation forwardDisjunction leftMember rightMember)
    line2e0 line2e1
  change ⊢ᵣ leftMember at line2d
  have line2f := star13_detach forwardNegation forwardDisjunction
    leftMember rightMember line2d line2e
  have line2Canonical := star13_castAssertionOrder forwardEquality
    rightMember line2f
  have line1Canonical := star13_castAssertionOrder orderOS
    (MixedOrder.ternaryInterpret line1Negation line1Disjunction
      psiX (body.instantiate x) existentialMember
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)) line1
  have line1Equality :
      Eq.mp (congrArg (Formula signature real []) orderOS)
        (MixedOrder.ternaryInterpret line1Negation line1Disjunction
          psiX (body.instantiate x) existentialMember
          (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)) =
      star13_normalizedDisjunction orderOS resultDisjunction
        (.neg vocabulary.negation psiX) existentialMember := by
    rfl
  have line1' := Derivation.castAssertion line1Equality line1Canonical
  let forward := Eq.mp (congrArg (Formula signature real []) forwardEquality)
    rightMember
  let reverse := star13_normalizedDisjunction orderOS
    resultDisjunction (.neg vocabulary.negation psiX) existentialMember
  change ⊢ᵣ forward at line2Canonical
  change ⊢ᵣ reverse at line1'
  have line3a := star_3_2 resultNegation resultDisjunction forward reverse
  have line3b := star13_detach resultNegation resultDisjunction forward
    (implication resultNegation resultDisjunction reverse
      (conjunction resultNegation resultDisjunction forward reverse))
    line2Canonical line3a
  have result := star13_detach resultNegation resultDisjunction reverse
    (conjunction resultNegation resultDisjunction forward reverse)
    line1' line3b
  change ⊢ᵣ star_13_195_formula vocabulary identityNegation
    identityBaseNegation identityBaseDisjunction existential
    implicationUniversal resultNegation resultDisjunction psi x
  unfold star_13_195_formula
  exact result

/-- Audited scope reading of ✱13·3. -/
def star_13_3_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (phiA phiX : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (x a : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢::φ a∨∼φ a.⊃:.φ x∨∼φ x.≡:x=a.∨.x≠ a"
  parsed := .assertion (implication negation disjunction
    (sameDisjunction disjunction phiA (.neg negation phiA))
    (star_4_01 negation disjunction
      (sameDisjunction disjunction phiX (.neg negation phiX))
      (sameDisjunction disjunction (star_13_01 vocabulary x a)
        (.neg negation (star_13_01 vocabulary x a)))))

/-- ✱13·3, reconstructed propositionally from excluded middle on each side.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_3
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (phiA phiX : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (x a : Term signature real [] sort) :
    Derivation (star_13_3_reading vocabulary negation disjunction
      phiA phiX x a).parsed := by
  let left := sameDisjunction disjunction phiX (.neg negation phiX)
  let equality := star_13_01 vocabulary x a
  let right := sameDisjunction disjunction equality (.neg negation equality)
  have leftProof : ⊢ᵣ left := star_2_11 negation disjunction phiX
  have rightProof : ⊢ᵣ right := star_2_11 negation disjunction equality
  have leftToRight : ⊢ᵣ implication negation disjunction left right :=
    star13_detach negation disjunction right
      (implication negation disjunction left right) rightProof
      (star_2_02 negation disjunction left right)
  have rightToLeft : ⊢ᵣ implication negation disjunction right left :=
    star13_detach negation disjunction left
      (implication negation disjunction right left) leftProof
      (star_2_02 negation disjunction right left)
  have joined := star13_detach negation disjunction _ _ leftToRight
    (star_3_2 negation disjunction
      (implication negation disjunction left right)
      (implication negation disjunction right left))
  have equivalenceProof : ⊢ᵣ star_4_01 negation disjunction left right :=
    star13_detach negation disjunction _ _ rightToLeft joined
  exact star13_detach negation disjunction _ _ equivalenceProof
    (star_2_02 negation disjunction
      (sameDisjunction disjunction phiA (.neg negation phiA))
      (star_4_01 negation disjunction left right))

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_13_1
#print axioms PM.RamifiedSyntax.star_13_101
#print axioms PM.RamifiedSyntax.star_13_15
#print axioms PM.RamifiedSyntax.star_13_11
#print axioms PM.RamifiedSyntax.star_13_12
#print axioms PM.RamifiedSyntax.star_13_13
#print axioms PM.RamifiedSyntax.star_13_16
#print axioms PM.RamifiedSyntax.star_13_17
#print axioms PM.RamifiedSyntax.star_13_171
#print axioms PM.RamifiedSyntax.star_13_18
#print axioms PM.RamifiedSyntax.star_13_181
#print axioms PM.RamifiedSyntax.star_13_19
#print axioms PM.RamifiedSyntax.star_13_191
#print axioms PM.RamifiedSyntax.star_13_192
#print axioms PM.RamifiedSyntax.star_13_193
#print axioms PM.RamifiedSyntax.star_13_194
#print axioms PM.RamifiedSyntax.star_13_195
#print axioms PM.RamifiedSyntax.star_13_3
