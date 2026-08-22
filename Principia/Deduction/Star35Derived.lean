import Principia.Deduction.Star34Derived
import Principia.FirstEdition.Volume1.Star35Source

namespace PM.RamifiedSyntax

/-- Conjunction at one ramified order, PM's ✱3·01 abbreviation. -/
private def star35Conjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation (sameDisjunction disjunction
    (.neg negation left) (.neg negation right))

/-- The eliminable application `x(α↿R)y` from the definition ✱35·01. -/
def star_35_01
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order classExcess))
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  star35Conjunction negation disjunction
    (applyUnary alpha x) (applyBinary relation x y)

theorem star_35_01_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order classExcess))
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (x y : Term signature real apparent .individual) :
    star_35_01 negation disjunction alpha relation x y =
      .neg negation (sameDisjunction disjunction
        (.neg negation (applyUnary alpha x))
        (.neg negation (applyBinary relation x y))) := rfl

/-- The eliminable application `x(R↾β)y` from the definition ✱35·02. -/
def star_35_02
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (beta : Term signature real apparent (classSort order classExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  star35Conjunction negation disjunction
    (applyBinary relation x y) (applyUnary beta y)

theorem star_35_02_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (beta : Term signature real apparent (classSort order classExcess))
    (x y : Term signature real apparent .individual) :
    star_35_02 negation disjunction relation beta x y =
      .neg negation (sameDisjunction disjunction
        (.neg negation (applyBinary relation x y))
        (.neg negation (applyUnary beta y))) := rfl

/-- The eliminable application `x(α↿R↾β)y` from the definition ✱35·03. -/
def star_35_03
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order leftClassExcess))
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (beta : Term signature real apparent (classSort order rightClassExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  star35Conjunction negation disjunction (applyUnary alpha x)
    (star35Conjunction negation disjunction
      (applyBinary relation x y) (applyUnary beta y))

theorem star_35_03_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order leftClassExcess))
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (beta : Term signature real apparent (classSort order rightClassExcess))
    (x y : Term signature real apparent .individual) :
    star_35_03 negation disjunction alpha relation beta x y =
      .neg negation (sameDisjunction disjunction
        (.neg negation (applyUnary alpha x))
        (.neg negation (.neg negation (sameDisjunction disjunction
          (.neg negation (applyBinary relation x y))
          (.neg negation (applyUnary beta y)))))) := rfl

/-- The eliminable application `x(α↑β)y` from the definition ✱35·04. -/
def star_35_04
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order leftClassExcess))
    (beta : Term signature real apparent (classSort order rightClassExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  star35Conjunction negation disjunction (applyUnary alpha x) (applyUnary beta y)

theorem star_35_04_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order leftClassExcess))
    (beta : Term signature real apparent (classSort order rightClassExcess))
    (x y : Term signature real apparent .individual) :
    star_35_04 negation disjunction alpha beta x y =
      .neg negation (sameDisjunction disjunction
        (.neg negation (applyUnary alpha x))
        (.neg negation (applyUnary beta y))) := rfl

/-! # Derived propositions of PM I, ✱35 -/

def star_35_1_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (x y : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:x(α↿ R)y.≡.x∈ α.xRy [*21·3.(*35·01)]"
  scopeReading := "The incomplete left restriction has the scope of the displayed application equivalence."
  parsed := .assertion (star_21_3_formula vocabulary.abstractionExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_35_01 negation disjunction alpha.weaken.weaken
      relation.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y)

/-- ✱35·1, exactly the printed ✱21·3 instance of ✱35·01.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_35_1
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star21EliminationHypothesis vocabulary
      (star_35_01 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y) :
    Derivation (.assertion (star_21_3_formula
      vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_35_01 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y)) := by
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction
    (star_35_01 negation disjunction alpha.weaken.weaken
      relation.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y
    star_10_35_hypothesis
  exact line1

def star_35_101_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation : Term signature real []
      (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order classExcess))
    (x y : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:x(R↾ β)y.≡.xRy.y∈ β"
  scopeReading := "The incomplete right restriction has the scope of the displayed application equivalence."
  parsed := .assertion (star_21_3_formula vocabulary.abstractionExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_35_02 negation disjunction relation.weaken.weaken
      beta.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y)

/-- ✱35·101, reconstructed from ✱35·02 and ✱21·3.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_35_101
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation : Term signature real []
      (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order classExcess))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star21EliminationHypothesis vocabulary
      (star_35_02 negation disjunction relation.weaken.weaken
        beta.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y) :
    Derivation (.assertion (star_21_3_formula
      vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_35_02 negation disjunction relation.weaken.weaken
        beta.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y)) := by
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction
    (star_35_02 negation disjunction relation.weaken.weaken
      beta.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x y
    star_10_35_hypothesis
  exact line1

def star_35_102_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:x(α↿ R↾ β)y.≡.x∈ α.xRy.y∈ β"
  scopeReading := "The incomplete two-sided restriction has the scope of the displayed application equivalence."
  parsed := .assertion (star_21_3_formula vocabulary.abstractionExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_35_03 negation disjunction alpha.weaken.weaken
      relation.weaken.weaken beta.weaken.weaken (.apparent .zero)
      (.apparent (.succ .zero))) x y)

/-- ✱35·102, reconstructed from ✱35·03 and ✱21·3.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_35_102
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star21EliminationHypothesis vocabulary
      (star_35_03 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken beta.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))) x y) :
    Derivation (.assertion (star_21_3_formula
      vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_35_03 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken beta.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))) x y)) := by
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction
    (star_35_03 negation disjunction alpha.weaken.weaken
      relation.weaken.weaken beta.weaken.weaken (.apparent .zero)
      (.apparent (.succ .zero))) x y star_10_35_hypothesis
  exact line1

def star_35_103_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:x(α↑ β)y.≡.x∈ α.y∈ β"
  scopeReading := "The incomplete class product has the scope of the displayed application equivalence."
  parsed := .assertion (star_21_3_formula vocabulary.abstractionExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_35_04 negation disjunction alpha.weaken.weaken beta.weaken.weaken
      (.apparent .zero) (.apparent (.succ .zero))) x y)

/-- ✱35·103, reconstructed from ✱35·04 and ✱21·3.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_35_103
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star21EliminationHypothesis vocabulary
      (star_35_04 negation disjunction alpha.weaken.weaken beta.weaken.weaken
        (.apparent .zero) (.apparent (.succ .zero))) x y) :
    Derivation (.assertion (star_21_3_formula
      vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_35_04 negation disjunction alpha.weaken.weaken beta.weaken.weaken
        (.apparent .zero) (.apparent (.succ .zero))) x y)) := by
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction
    (star_35_04 negation disjunction alpha.weaken.weaken beta.weaken.weaken
      (.apparent .zero) (.apparent (.succ .zero))) x y
    star_10_35_hypothesis
  exact line1

/-! ## What ✱35·1 to ✱35·103 still waits for

The four propositions above assert the equivalence between an application of a
restricted relation — an incomplete symbol introduced by ✱35·01–·04 — and its
defining matrix.  Each is therefore an instance of ✱21·3, and each keeps the
named reducibility-scope premise `star_10_35_hypothesis`.  ✱35·11, ✱35·12 and
✱35·13 below do not: they compare two matrices already in eliminated form, and
the printed demonstrations that connect them are propositional.
-/

/-! ## The propositions of ✱35 whose two sides are already eliminated

✱35·01–·04 expand the four restricted relations into matrices of one and the
same assigned order: `x ∈ α`, `xRy` and `y ∈ β` are applications, and the dots
between them are ✱3·01.  ✱35·11, ✱35·12 and ✱35·13 therefore compare two such
matrices, and their printed demonstrations are propositional throughout.

What the printed demonstrations add beyond that is only the passage from the
displayed equivalence of the two applications to the displayed identity of the
two relations, which is ✱11·11 followed by ✱21·43.  ✱21·43 rests on ✱21·3 and
so is still conditional; the equivalence of the applications, which is the line
each demonstration actually derives, is not.  It is that line which is asserted
here.
-/

namespace Star35Scope

/-- Detachment at one assigned order, by ✱1·1 or ✱1·11 according to the
real-variable context. -/
private theorem detachHere
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature real [] order} :
    (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons head tail => exact Derivation.star_1_11_same negation disjunction

/-- PM's ✱3·2: two asserted propositions may be conjoined. -/
private theorem pairHere
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature real [] order}
    (hp : ⊢ᵣ p) (hq : ⊢ᵣ q) :
    ⊢ᵣ conjunction negation disjunction p q :=
  detachHere negation disjunction hq
    (detachHere negation disjunction hp (star_3_2 negation disjunction p q))

/-- PM's ✱2·05 (`Syll`) used as a rule on two asserted implications. -/
private theorem syllHere
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q r : Formula signature real [] order}
    (hpq : ⊢ᵣ implication negation disjunction p q)
    (hqr : ⊢ᵣ implication negation disjunction q r) :
    ⊢ᵣ implication negation disjunction p r :=
  detachHere negation disjunction hpq
    (detachHere negation disjunction hqr (star_2_05 negation disjunction p q r))

/-- PM's ✱3·43 (`Comp`) used as a rule on two asserted implications. -/
private theorem compHere
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q r : Formula signature real [] order}
    (hpq : ⊢ᵣ implication negation disjunction p q)
    (hpr : ⊢ᵣ implication negation disjunction p r) :
    ⊢ᵣ implication negation disjunction p
      (conjunction negation disjunction q r) :=
  detachHere negation disjunction (pairHere negation disjunction hpq hpr)
    (star_3_43 negation disjunction p q r)

/-- ✱4·01: two asserted implications make the equivalence. -/
private theorem equivHere
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature real [] order}
    (hpq : ⊢ᵣ implication negation disjunction p q)
    (hqp : ⊢ᵣ implication negation disjunction q p) :
    ⊢ᵣ star_4_01 negation disjunction p q :=
  pairHere negation disjunction hpq hqp

/-- `⊢ : a . b . c : ≡ : a . b : b . c`.  This is the propositional content of
PM's `[✱4·24]` step at ✱35·11: the middle member is used twice, which the two
printed projections ✱3·26 and ✱3·27 and the printed composition ✱3·43 supply
directly. -/
theorem duplicateMiddle
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (a b c : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (conjunction negation disjunction a
        (conjunction negation disjunction b c))
      (conjunction negation disjunction
        (conjunction negation disjunction a b)
        (conjunction negation disjunction b c)) := by
  have line1 := star_3_26 negation disjunction a
    (conjunction negation disjunction b c)
  have line2 := star_3_27 negation disjunction a
    (conjunction negation disjunction b c)
  have line3 := syllHere negation disjunction line2
    (star_3_26 negation disjunction b c)
  have forward := compHere negation disjunction
    (compHere negation disjunction line1 line3) line2
  have line4 := star_3_26 negation disjunction
    (conjunction negation disjunction a b)
    (conjunction negation disjunction b c)
  have line5 := star_3_27 negation disjunction
    (conjunction negation disjunction a b)
    (conjunction negation disjunction b c)
  have line6 := syllHere negation disjunction line4
    (star_3_26 negation disjunction a b)
  have backward := compHere negation disjunction line6 line5
  exact equivHere negation disjunction forward backward

/-- `⊢ : a . b : c . d : ≡ : a : b . c . d`. -/
theorem regroupMiddle
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (a b c d : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (conjunction negation disjunction
        (conjunction negation disjunction a b)
        (conjunction negation disjunction c d))
      (conjunction negation disjunction a
        (conjunction negation disjunction
          (conjunction negation disjunction b c) d)) := by
  have line1 := star_3_26 negation disjunction
    (conjunction negation disjunction a b)
    (conjunction negation disjunction c d)
  have line2 := star_3_27 negation disjunction
    (conjunction negation disjunction a b)
    (conjunction negation disjunction c d)
  have forwardA := syllHere negation disjunction line1
    (star_3_26 negation disjunction a b)
  have forwardB := syllHere negation disjunction line1
    (star_3_27 negation disjunction a b)
  have forwardC := syllHere negation disjunction line2
    (star_3_26 negation disjunction c d)
  have forwardD := syllHere negation disjunction line2
    (star_3_27 negation disjunction c d)
  have forward := compHere negation disjunction forwardA
    (compHere negation disjunction
      (compHere negation disjunction forwardB forwardC) forwardD)
  have line3 := star_3_26 negation disjunction a
    (conjunction negation disjunction
      (conjunction negation disjunction b c) d)
  have line4 := star_3_27 negation disjunction a
    (conjunction negation disjunction
      (conjunction negation disjunction b c) d)
  have line5 := syllHere negation disjunction line4
    (star_3_26 negation disjunction (conjunction negation disjunction b c) d)
  have backwardD := syllHere negation disjunction line4
    (star_3_27 negation disjunction (conjunction negation disjunction b c) d)
  have backwardB := syllHere negation disjunction line5
    (star_3_26 negation disjunction b c)
  have backwardC := syllHere negation disjunction line5
    (star_3_27 negation disjunction b c)
  have backward := compHere negation disjunction
    (compHere negation disjunction line3 backwardB)
    (compHere negation disjunction backwardC backwardD)
  exact equivHere negation disjunction forward backward

/-- `⊢ : a . b : c . d : ≡ : a . c : b . d`. -/
theorem exchangeMiddle
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (a b c d : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (conjunction negation disjunction
        (conjunction negation disjunction a b)
        (conjunction negation disjunction c d))
      (conjunction negation disjunction
        (conjunction negation disjunction a c)
        (conjunction negation disjunction b d)) := by
  have line1 := star_3_26 negation disjunction
    (conjunction negation disjunction a b)
    (conjunction negation disjunction c d)
  have line2 := star_3_27 negation disjunction
    (conjunction negation disjunction a b)
    (conjunction negation disjunction c d)
  have forwardA := syllHere negation disjunction line1
    (star_3_26 negation disjunction a b)
  have forwardB := syllHere negation disjunction line1
    (star_3_27 negation disjunction a b)
  have forwardC := syllHere negation disjunction line2
    (star_3_26 negation disjunction c d)
  have forwardD := syllHere negation disjunction line2
    (star_3_27 negation disjunction c d)
  have forward := compHere negation disjunction
    (compHere negation disjunction forwardA forwardC)
    (compHere negation disjunction forwardB forwardD)
  have line3 := star_3_26 negation disjunction
    (conjunction negation disjunction a c)
    (conjunction negation disjunction b d)
  have line4 := star_3_27 negation disjunction
    (conjunction negation disjunction a c)
    (conjunction negation disjunction b d)
  have backwardA := syllHere negation disjunction line3
    (star_3_26 negation disjunction a c)
  have backwardC := syllHere negation disjunction line3
    (star_3_27 negation disjunction a c)
  have backwardB := syllHere negation disjunction line4
    (star_3_26 negation disjunction b d)
  have backwardD := syllHere negation disjunction line4
    (star_3_27 negation disjunction b d)
  have backward := compHere negation disjunction
    (compHere negation disjunction backwardA backwardB)
    (compHere negation disjunction backwardC backwardD)
  exact equivHere negation disjunction forward backward

end Star35Scope

/-! ### ✱35·11 -/

/-- The printed left member of ✱35·11, `x(α↿ R↾ β)y`, i.e. ✱35·03. -/
def star_35_11_left
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] order :=
  star_35_03 negation disjunction alpha relation beta x y

/-- The printed right member of ✱35·11, `x(α↿ R)y . x(R↾ β)y`, i.e. the ✱23·33
expansion of `x{(α↿ R)∩̇(R↾ β)}y`, built from ✱35·01 and ✱35·02. -/
def star_35_11_right
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] order :=
  conjunction negation disjunction
    (star_35_01 negation disjunction alpha relation x y)
    (star_35_02 negation disjunction relation beta x y)

def star_35_11_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱35·11. ⊢:x(α↿ R↾ β)y. ≡.x(α↿ R)y.x(R↾ β)y"
  scopeReading :=
    "Both restricted relations are incomplete symbols whose scope is the displayed application, and ∩̇ is eliminated by ✱23·33; what is asserted is the equivalence of applications the printed demonstration derives, the displayed relation identity requiring ✱11·11 and ✱21·43."
  parsed := .assertion (star_4_01 negation disjunction
    (star_35_11_left negation disjunction alpha relation beta x y)
    (star_35_11_right negation disjunction alpha relation beta x y))

/-- ✱35·11, at the line its printed demonstration reaches.  PM's `[✱4·24]` is
the one substantive step — the middle member `xRy` occurs twice on the right —
and it is written here through the printed projections ✱3·26 and ✱3·27 and the
printed composition ✱3·43, PM's ✱4·32 not being available in the ramified ✱4.
The final passage to the displayed relation identity is ✱11·11 with ✱21·43 and
is not asserted, ✱21·43 still resting on ✱21·3.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_35_11
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    Derivation (star_35_11_reading negation disjunction alpha relation beta
      x y).parsed := by
  exact Star35Scope.duplicateMiddle negation disjunction
    (applyUnary alpha x) (applyBinary relation x y) (applyUnary beta y)

/-! ### ✱35·12 -/

/-- The printed left member of ✱35·12, `x(α↿ R)y . x(S↾ β)y`, i.e. the ✱23·33
expansion of `x{(α↿ R)∩̇(S↾ β)}y`. -/
def star_35_12_left
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] order :=
  conjunction negation disjunction
    (star_35_01 negation disjunction alpha relation x y)
    (star_35_02 negation disjunction other beta x y)

/-- The printed right member of ✱35·12, `x{α↿ (R∩̇S)↾ β}y`: ✱35·03 with the
✱23·33 expansion `xRy . xSy` of `x(R∩̇S)y` in the relation place. -/
def star_35_12_right
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] order :=
  conjunction negation disjunction (applyUnary alpha x)
    (conjunction negation disjunction
      (conjunction negation disjunction
        (applyBinary relation x y) (applyBinary other x y))
      (applyUnary beta y))

def star_35_12_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱35·12. ⊢:x{(α↿ R)∩̇(S↾ β)}y. ≡.x∈ α.x(R∩̇S)y.y∈ β"
  scopeReading :=
    "Each restricted relation is an incomplete symbol whose scope is the displayed application, and ∩̇ is eliminated by ✱23·33 on both sides; what is asserted is the equivalence of applications the printed demonstration derives, the displayed relation identity requiring ✱11·11 and ✱21·43."
  parsed := .assertion (star_4_01 negation disjunction
    (star_35_12_left negation disjunction alpha relation other beta x y)
    (star_35_12_right negation disjunction alpha relation other beta x y))

/-- ✱35·12, at the line its printed demonstration reaches.  PM's route is
✱23·33, then ✱35·1·101, then ✱23·33 again, then ✱35·102; once every incomplete
symbol is eliminated only the regrouping of the four printed members remains,
and that is written here through ✱3·26, ✱3·27 and ✱3·43.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_35_12
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (x y : Term signature real [] .individual) :
    Derivation (star_35_12_reading negation disjunction alpha relation other
      beta x y).parsed := by
  exact Star35Scope.regroupMiddle negation disjunction
    (applyUnary alpha x) (applyBinary relation x y) (applyBinary other x y)
    (applyUnary beta y)

/-! ### ✱35·13 -/

/-- The printed left member of ✱35·13, `x(α↿ R)y . x(β↿ S)y`, i.e. the ✱23·33
expansion of `x{(α↿ R)∩̇(β↿ S)}y`. -/
def star_35_13_left
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] order :=
  conjunction negation disjunction
    (star_35_01 negation disjunction alpha relation x y)
    (star_35_01 negation disjunction beta other x y)

/-- The printed right member of ✱35·13, `x{(α ∩ β)↿ (R∩̇S)}y`: ✱35·01 with the
✱22·33 expansion `x∈ α . x∈ β` in the class place and the ✱23·33 expansion
`xRy . xSy` in the relation place. -/
def star_35_13_right
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] order :=
  conjunction negation disjunction
    (conjunction negation disjunction
      (applyUnary alpha x) (applyUnary beta x))
    (conjunction negation disjunction
      (applyBinary relation x y) (applyBinary other x y))

def star_35_13_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱35·13. ⊢:x{(α↿ R)∩̇(β↿ S)}y. ≡.x∈ (α ∩ β).x(R∩̇S)y"
  scopeReading :=
    "Both left restrictions are incomplete symbols whose scope is the displayed application, and ∩ and ∩̇ are eliminated by ✱22·33 and ✱23·33; what is asserted is the equivalence of applications the printed demonstration derives, the displayed relation identity requiring ✱11·11 and ✱21·43."
  parsed := .assertion (star_4_01 negation disjunction
    (star_35_13_left negation disjunction alpha relation beta other x y)
    (star_35_13_right negation disjunction alpha relation beta other x y))

/-- ✱35·13, at the line its printed demonstration reaches.  PM's route is
✱23·33, then ✱35·1, then `[✱22·33.✱23·33]`, then ✱35·1 again; once every
incomplete symbol is eliminated only the exchange of the two middle printed
members remains, and that is written here through ✱3·26, ✱3·27 and ✱3·43.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_35_13
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order leftClassExcess))
    (relation : Term signature real [] (relationSort order relationExcess))
    (beta : Term signature real [] (classSort order rightClassExcess))
    (other : Term signature real [] (relationSort order otherExcess))
    (x y : Term signature real [] .individual) :
    Derivation (star_35_13_reading negation disjunction alpha relation beta
      other x y).parsed := by
  exact Star35Scope.exchangeMiddle negation disjunction
    (applyUnary alpha x) (applyBinary relation x y) (applyUnary beta x)
    (applyBinary other x y)

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_35_01_unfold
#print axioms PM.RamifiedSyntax.star_35_02_unfold
#print axioms PM.RamifiedSyntax.star_35_03_unfold
#print axioms PM.RamifiedSyntax.star_35_04_unfold
#print axioms PM.RamifiedSyntax.star_35_1
#print axioms PM.RamifiedSyntax.star_35_101
#print axioms PM.RamifiedSyntax.star_35_102
#print axioms PM.RamifiedSyntax.star_35_103
#print axioms PM.RamifiedSyntax.star_35_11
#print axioms PM.RamifiedSyntax.star_35_12
#print axioms PM.RamifiedSyntax.star_35_13
