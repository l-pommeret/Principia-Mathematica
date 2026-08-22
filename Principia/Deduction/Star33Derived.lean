import Principia.Deduction.Star20Derived
import Principia.Deduction.Star21Derived
import Principia.FirstEdition.Volume1.Star33Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-! ## Vocabulary for the ✱21·3 elimination rule now available

The record below only packages the vocabulary already required by ✱21·3.  It
adds no object rule.  The remaining premise is kept under the exact name used
by that theorem.
-/

structure Star21EliminationVocabulary (signature : Signature)
    (resultOrder : Nat) where
  abstractionExistential : ExistentialVocabulary signature
    (relationSort resultOrder 0)
    (max (bindOrder (bindOrder resultOrder .individual) .individual)
      resultOrder)
  reducibilityExistential : ExistentialVocabulary signature
    (relationSort resultOrder 0)
    (bindOrder (bindOrder resultOrder .individual) .individual)
  leftUniversal : signature.Universal .individual resultOrder
  rightUniversal : signature.Universal .individual
    (bindOrder resultOrder .individual)
  equivalenceNegation : signature.Negation resultOrder
  equivalenceDisjunction : signature.Disjunction resultOrder
  leftNegation : signature.Negation
    (bindOrder (bindOrder resultOrder .individual) .individual)
  rightNegation : signature.Negation resultOrder
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder resultOrder .individual) .individual)
      resultOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder resultOrder .individual) .individual)
      resultOrder)
  reducibilityOuterNegation : signature.Negation
    (bindOrder
      (bindOrder (bindOrder resultOrder .individual) .individual)
      (relationSort resultOrder 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder
        (bindOrder (bindOrder resultOrder .individual) .individual)
        (relationSort resultOrder 0))
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          resultOrder)
        (relationSort resultOrder 0)))
  finalNegation : signature.Negation
    (bindOrder
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder)
      (relationSort resultOrder 0))
  finalDisjunction : signature.Disjunction
    (bindOrder
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder)
      (relationSort resultOrder 0))

def Star21EliminationHypothesis
    (vocabulary : Star21EliminationVocabulary signature resultOrder)
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) : Prop :=
  (⊢ᵣ star_21_3_transportFormula vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.conjunctionDisjunction matrix x y) →
  ⊢ᵣ mixedImplication vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction
    (star_12_11_formula vocabulary.reducibilityExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction matrix)
    (star_21_3_formula vocabulary.abstractionExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction matrix x y)

/-! ✱21·3 with the two argument sorts left explicit.  PM's later functional
operators use exactly this already-generic ✱11·1/✱12·11 instance. -/

def binaryAbstraction
    (existential : ExistentialVocabulary signature
      (.function [leftSort, rightSort] resultOrder 0)
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) scopeOrder))
    (leftUniversal : signature.Universal leftSort resultOrder)
    (rightUniversal : signature.Universal rightSort
      (bindOrder resultOrder leftSort))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder leftSort) rightSort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) scopeOrder))
    (matrix : Formula signature real
      (leftSort :: rightSort :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [leftSort, rightSort] resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder (bindOrder resultOrder leftSort) rightSort) scopeOrder)
        (.function [leftSort, rightSort] resultOrder 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      ((equivalence equivalenceNegation equivalenceDisjunction
        (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
          (.apparent (.succ .zero)))
        (matrix.rename (liftRenamingN [leftSort, rightSort]
          (fun v => .succ v)))).always₂ leftUniversal rightUniversal)
      continuation)

def binaryEliminationFunctionMatrix
    (_matrix : Formula signature real [leftSort, rightSort] resultOrder) :
    Formula signature
      (.function [leftSort, rightSort] resultOrder 0 :: real)
      [leftSort, rightSort] resultOrder :=
  applyBinary
    (.real (.zero : Var
      (.function [leftSort, rightSort] resultOrder 0 :: real)
      (.function [leftSort, rightSort] resultOrder 0)))
    (.apparent .zero) (.apparent (.succ .zero))

def binaryEliminationTransport
    (leftUniversal : signature.Universal leftSort resultOrder)
    (rightUniversal : signature.Universal rightSort
      (bindOrder resultOrder leftSort))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (outerNegation : signature.Negation
      (bindOrder (bindOrder resultOrder leftSort) rightSort))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder))
    (matrix : Formula signature real [leftSort, rightSort] resultOrder)
    (left : Term signature real [] leftSort)
    (right : Term signature real [] rightSort) :
    Formula signature
      (.function [leftSort, rightSort] resultOrder 0 :: real) []
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder) :=
  star_11_1_formula leftUniversal rightUniversal outerNegation outerDisjunction
    (equivalence equivalenceNegation equivalenceDisjunction
      (binaryEliminationFunctionMatrix matrix) matrix.weakenReal)
    left.weakenReal right.weakenReal

def binaryEliminationContinuation
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (matrix : Formula signature real [leftSort, rightSort] resultOrder)
    (left : Term signature real [] leftSort)
    (right : Term signature real [] rightSort) :
    Formula signature real
      [.function [leftSort, rightSort] resultOrder 0] resultOrder :=
  equivalence equivalenceNegation equivalenceDisjunction
    (applyBinary (.apparent .zero) left.weaken right.weaken)
    ((matrix.instantiate₂ left right).rename
      (emptyRenaming
        (target := [.function [leftSort, rightSort] resultOrder 0])))

def binaryEliminationFormula
    (existential : ExistentialVocabulary signature
      (.function [leftSort, rightSort] resultOrder 0)
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder))
    (leftUniversal : signature.Universal leftSort resultOrder)
    (rightUniversal : signature.Universal rightSort
      (bindOrder resultOrder leftSort))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder leftSort) rightSort))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder))
    (matrix : Formula signature real [leftSort, rightSort] resultOrder)
    (left : Term signature real [] leftSort)
    (right : Term signature real [] rightSort) :=
  binaryAbstraction existential leftUniversal rightUniversal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix
    (binaryEliminationContinuation equivalenceNegation equivalenceDisjunction
      matrix left right)

structure BinaryEliminationVocabulary (signature : Signature)
    (leftSort rightSort : RSort) (resultOrder : Nat) where
  abstractionExistential : ExistentialVocabulary signature
    (.function [leftSort, rightSort] resultOrder 0)
    (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder)
  reducibilityExistential : ExistentialVocabulary signature
    (.function [leftSort, rightSort] resultOrder 0)
    (bindOrder (bindOrder resultOrder leftSort) rightSort)
  leftUniversal : signature.Universal leftSort resultOrder
  rightUniversal : signature.Universal rightSort
    (bindOrder resultOrder leftSort)
  equivalenceNegation : signature.Negation resultOrder
  equivalenceDisjunction : signature.Disjunction resultOrder
  leftNegation : signature.Negation
    (bindOrder (bindOrder resultOrder leftSort) rightSort)
  rightNegation : signature.Negation resultOrder
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder)
  reducibilityOuterNegation : signature.Negation
    (bindOrder (bindOrder (bindOrder resultOrder leftSort) rightSort)
      (.function [leftSort, rightSort] resultOrder 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder (bindOrder resultOrder leftSort) rightSort)
        (.function [leftSort, rightSort] resultOrder 0))
      (bindOrder
        (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder)
        (.function [leftSort, rightSort] resultOrder 0)))

def BinaryEliminationHypothesis
    (vocabulary : BinaryEliminationVocabulary signature leftSort rightSort
      resultOrder)
    (matrix : Formula signature real [leftSort, rightSort] resultOrder)
    (left : Term signature real [] leftSort)
    (right : Term signature real [] rightSort) : Prop :=
  (⊢ᵣ binaryEliminationTransport vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.conjunctionDisjunction matrix left right) →
  ⊢ᵣ mixedImplication vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction
    (star_12_11_formula vocabulary.reducibilityExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction matrix)
    (binaryEliminationFormula vocabulary.abstractionExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      matrix left right)

theorem binaryElimination
    (vocabulary : BinaryEliminationVocabulary signature leftSort rightSort
      resultOrder)
    (matrix : Formula signature real [leftSort, rightSort] resultOrder)
    (left : Term signature real [] leftSort)
    (right : Term signature real [] rightSort)
    (star_10_35_hypothesis : BinaryEliminationHypothesis vocabulary
      matrix left right) :
    ⊢ᵣ binaryEliminationFormula vocabulary.abstractionExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      matrix left right := by
  have line1 := star_11_1 vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.leftNegation vocabulary.conjunctionDisjunction
    (equivalence vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction
      (binaryEliminationFunctionMatrix matrix) matrix.weakenReal)
    left.weakenReal right.weakenReal
  have line2 := star_10_35_hypothesis line1
  have line3 := star_12_11 vocabulary.reducibilityExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction matrix
  have line4 := Derivation.star_9_12 vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction line3 line2
  exact line4

/-!
# PM I, ✱33 — domains

The operators `D`, `ᗡ`, and `C` return classes.  Since class abstractions are
contextual incomplete symbols in `RamifiedSyntax`, they cannot be manufactured
as `Term`s.  The following abbreviations therefore give their eliminable
membership expansions, i.e. the formulae which PM obtains from ✱33·01–·03.
-/

/-- Membership in `DʻR`, the eliminable expansion printed at ✱33·01. -/
def star_33_01
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  .sometimes existential
    (applyBinary relation.weaken x.weaken (.apparent .zero))

theorem star_33_01_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x : Term signature real apparent .individual) :
    star_33_01 existential relation x =
      .sometimes existential
        (applyBinary relation.weaken x.weaken (.apparent .zero)) := rfl

/-- Membership in `ᗡʻR`, the eliminable expansion printed at ✱33·02. -/
def star_33_02
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (y : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  .sometimes existential
    (applyBinary relation.weaken (.apparent .zero) y.weaken)

theorem star_33_02_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (y : Term signature real apparent .individual) :
    star_33_02 existential relation y =
      .sometimes existential
        (applyBinary relation.weaken (.apparent .zero) y.weaken) := rfl

/-- Membership in `CʻR`, the eliminable expansion printed at ✱33·03. -/
def star_33_03
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  sameDisjunction disjunction
    (star_33_01 existential relation x)
    (star_33_02 existential relation x)

theorem star_33_03_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x : Term signature real apparent .individual) :
    star_33_03 existential disjunction relation x =
      sameDisjunction disjunction
        (.sometimes existential
          (applyBinary relation.weaken x.weaken (.apparent .zero)))
        (.sometimes existential
          (applyBinary relation.weaken (.apparent .zero) x.weaken)) := rfl

/-- `xFR`, the eliminable expansion printed at ✱33·04. -/
abbrev star_33_04 := @star_33_03

theorem star_33_04_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x : Term signature real apparent .individual) :
    star_33_04 existential disjunction relation x =
      sameDisjunction disjunction
        (.sometimes existential
          (applyBinary relation.weaken x.weaken (.apparent .zero)))
        (.sometimes existential
          (applyBinary relation.weaken (.apparent .zero) x.weaken)) := rfl

/-! ## Direct eliminations -/

def star_33_operatorIdentityOrder
    (relationOrder identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder identityBaseOrder
    (.function [classSort (bindOrder relationOrder .individual) 0]
      identityBaseOrder identityExcess)

def star_33_operatorOrder
    (relationOrder identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder
    (max (bindOrder (bindOrder relationOrder .individual) .individual)
      (star_33_operatorIdentityOrder relationOrder identityBaseOrder
        identityExcess))
    (classSort (bindOrder relationOrder .individual) 0)

structure Star33OperatorVocabulary (signature : Signature)
    (relationOrder identityBaseOrder identityExcess : Nat) where
  classExistential : ExistentialVocabulary signature
    (classSort (bindOrder relationOrder .individual) 0)
    (max (bindOrder (bindOrder relationOrder .individual) .individual)
      (star_33_operatorIdentityOrder relationOrder identityBaseOrder
        identityExcess))
  classUniversal : signature.Universal .individual
    (bindOrder relationOrder .individual)
  classEquivalenceNegation : signature.Negation
    (bindOrder relationOrder .individual)
  classEquivalenceDisjunction : signature.Disjunction
    (bindOrder relationOrder .individual)
  classLeftNegation : signature.Negation
    (bindOrder (bindOrder relationOrder .individual) .individual)
  classRightNegation : signature.Negation
    (star_33_operatorIdentityOrder relationOrder identityBaseOrder
      identityExcess)
  classOuterNegation : signature.Negation
    (max (bindOrder (bindOrder relationOrder .individual) .individual)
      (star_33_operatorIdentityOrder relationOrder identityBaseOrder
        identityExcess))
  classConjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder relationOrder .individual) .individual)
      (star_33_operatorIdentityOrder relationOrder identityBaseOrder
        identityExcess))
  identity : IdentityVocabulary signature
    (classSort (bindOrder relationOrder .individual) 0)
    identityBaseOrder identityExcess

private def star_33_operatorMatrix
    (operatorVocabulary : Star33OperatorVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (domainMatrix : Formula signature real
      [.individual, classSort (bindOrder relationOrder .individual) 0,
        relationSort relationOrder relationExcess]
      (bindOrder relationOrder .individual)) :
    Formula signature real
      [classSort (bindOrder relationOrder .individual) 0,
        relationSort relationOrder relationExcess]
      (star_33_operatorOrder relationOrder identityBaseOrder identityExcess) :=
  star_20_01 operatorVocabulary.classExistential
    operatorVocabulary.classUniversal
    operatorVocabulary.classEquivalenceNegation
    operatorVocabulary.classEquivalenceDisjunction
    operatorVocabulary.classLeftNegation operatorVocabulary.classRightNegation
    operatorVocabulary.classOuterNegation
    operatorVocabulary.classConjunctionDisjunction domainMatrix
    (star_13_01 operatorVocabulary.identity
      (.apparent (.succ .zero)) (.apparent .zero))

private def star_33_1_domainMatrix
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder) :
    Formula signature real
      [.individual, classSort (bindOrder relationOrder .individual) 0,
        relationSort relationOrder relationExcess]
      (bindOrder relationOrder .individual) :=
  star_33_01 relationExistential (.apparent (.succ (.succ .zero)))
    (.apparent .zero)

private def star_33_101_domainMatrix
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder) :
    Formula signature real
      [.individual, classSort (bindOrder relationOrder .individual) 0,
        relationSort relationOrder relationExcess]
      (bindOrder relationOrder .individual) :=
  star_33_02 relationExistential (.apparent (.succ (.succ .zero)))
    (.apparent .zero)

private def star_33_102_domainMatrix
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual)) :
    Formula signature real
      [.individual, classSort (bindOrder relationOrder .individual) 0,
        relationSort relationOrder relationExcess]
      (bindOrder relationOrder .individual) :=
  star_33_03 relationExistential disjunction
    (.apparent (.succ (.succ .zero))) (.apparent .zero)

def star_33_1_reading
    (operatorVocabulary : Star33OperatorVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (eliminationVocabulary : BinaryEliminationVocabulary signature
      (classSort (bindOrder relationOrder .individual) 0)
      (relationSort relationOrder relationExcess)
      (star_33_operatorOrder relationOrder identityBaseOrder identityExcess))
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder)
    (alpha : Term signature real []
      (classSort (bindOrder relationOrder .individual) 0))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess)) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:αDR.≡.α=x̂{(∃ y).xRy} [*21·3.(*33·01)]"
  scopeReading := "D is expanded contextually by ✱33·01 inside the displayed equivalence."
  parsed := .assertion (binaryEliminationFormula
    eliminationVocabulary.abstractionExistential
    eliminationVocabulary.leftUniversal eliminationVocabulary.rightUniversal
    eliminationVocabulary.equivalenceNegation
    eliminationVocabulary.equivalenceDisjunction
    eliminationVocabulary.leftNegation eliminationVocabulary.rightNegation
    eliminationVocabulary.outerNegation
    eliminationVocabulary.conjunctionDisjunction
    (star_33_operatorMatrix operatorVocabulary
      (star_33_1_domainMatrix relationExistential)) alpha relation)

/-- ✱33·1, the printed heterogeneous ✱21·3 instance of ✱33·01.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_33_1
    (operatorVocabulary : Star33OperatorVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (eliminationVocabulary : BinaryEliminationVocabulary signature
      (classSort (bindOrder relationOrder .individual) 0)
      (relationSort relationOrder relationExcess)
      (star_33_operatorOrder relationOrder identityBaseOrder identityExcess))
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder)
    (alpha : Term signature real []
      (classSort (bindOrder relationOrder .individual) 0))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (star_10_35_hypothesis : PM.RamifiedSyntax.BinaryEliminationHypothesis
      eliminationVocabulary
      (star_33_operatorMatrix operatorVocabulary
        (star_33_1_domainMatrix relationExistential)) alpha relation) :
    Derivation (.assertion (binaryEliminationFormula
      eliminationVocabulary.abstractionExistential
      eliminationVocabulary.leftUniversal eliminationVocabulary.rightUniversal
      eliminationVocabulary.equivalenceNegation
      eliminationVocabulary.equivalenceDisjunction
      eliminationVocabulary.leftNegation eliminationVocabulary.rightNegation
      eliminationVocabulary.outerNegation
      eliminationVocabulary.conjunctionDisjunction
      (star_33_operatorMatrix operatorVocabulary
        (star_33_1_domainMatrix relationExistential)) alpha relation)) := by
  have line1 := binaryElimination eliminationVocabulary
    (star_20_01 operatorVocabulary.classExistential
      operatorVocabulary.classUniversal
      operatorVocabulary.classEquivalenceNegation
      operatorVocabulary.classEquivalenceDisjunction
      operatorVocabulary.classLeftNegation
      operatorVocabulary.classRightNegation
      operatorVocabulary.classOuterNegation
      operatorVocabulary.classConjunctionDisjunction
      (star_33_01 relationExistential (.apparent (.succ (.succ .zero)))
        (.apparent .zero))
      (star_13_01 operatorVocabulary.identity
        (.apparent (.succ .zero)) (.apparent .zero)))
    alpha relation star_10_35_hypothesis
  exact line1

def star_33_101_reading
    (operatorVocabulary : Star33OperatorVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (eliminationVocabulary : BinaryEliminationVocabulary signature
      (classSort (bindOrder relationOrder .individual) 0)
      (relationSort relationOrder relationExcess)
      (star_33_operatorOrder relationOrder identityBaseOrder identityExcess))
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder)
    (beta : Term signature real []
      (classSort (bindOrder relationOrder .individual) 0))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess)) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:βᗡR.≡.β=ŷ{(∃ x).xRy}"
  scopeReading := "ᗡ is expanded contextually by ✱33·02 inside the displayed equivalence."
  parsed := .assertion (binaryEliminationFormula
    eliminationVocabulary.abstractionExistential
    eliminationVocabulary.leftUniversal eliminationVocabulary.rightUniversal
    eliminationVocabulary.equivalenceNegation
    eliminationVocabulary.equivalenceDisjunction
    eliminationVocabulary.leftNegation eliminationVocabulary.rightNegation
    eliminationVocabulary.outerNegation
    eliminationVocabulary.conjunctionDisjunction
    (star_33_operatorMatrix operatorVocabulary
      (star_33_101_domainMatrix relationExistential)) beta relation)

/-- ✱33·101, reconstructed from ✱33·02 and heterogeneous ✱21·3.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_33_101
    (operatorVocabulary : Star33OperatorVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (eliminationVocabulary : BinaryEliminationVocabulary signature
      (classSort (bindOrder relationOrder .individual) 0)
      (relationSort relationOrder relationExcess)
      (star_33_operatorOrder relationOrder identityBaseOrder identityExcess))
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder)
    (beta : Term signature real []
      (classSort (bindOrder relationOrder .individual) 0))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (star_10_35_hypothesis : PM.RamifiedSyntax.BinaryEliminationHypothesis
      eliminationVocabulary
      (star_33_operatorMatrix operatorVocabulary
        (star_33_101_domainMatrix relationExistential)) beta relation) :
    Derivation (.assertion (binaryEliminationFormula
      eliminationVocabulary.abstractionExistential
      eliminationVocabulary.leftUniversal eliminationVocabulary.rightUniversal
      eliminationVocabulary.equivalenceNegation
      eliminationVocabulary.equivalenceDisjunction
      eliminationVocabulary.leftNegation eliminationVocabulary.rightNegation
      eliminationVocabulary.outerNegation
      eliminationVocabulary.conjunctionDisjunction
      (star_33_operatorMatrix operatorVocabulary
        (star_33_101_domainMatrix relationExistential)) beta relation)) := by
  have line1 := binaryElimination eliminationVocabulary
    (star_33_operatorMatrix operatorVocabulary
      (star_33_101_domainMatrix relationExistential)) beta relation
    star_10_35_hypothesis
  exact line1

def star_33_102_reading
    (operatorVocabulary : Star33OperatorVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (eliminationVocabulary : BinaryEliminationVocabulary signature
      (classSort (bindOrder relationOrder .individual) 0)
      (relationSort relationOrder relationExcess)
      (star_33_operatorOrder relationOrder identityBaseOrder identityExcess))
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (gamma : Term signature real []
      (classSort (bindOrder relationOrder .individual) 0))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess)) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:γ CR.≡.γ=x̂{(∃ y):xRy.∨ .yRx}"
  scopeReading := "C is expanded contextually by ✱33·03 inside the displayed equivalence."
  parsed := .assertion (binaryEliminationFormula
    eliminationVocabulary.abstractionExistential
    eliminationVocabulary.leftUniversal eliminationVocabulary.rightUniversal
    eliminationVocabulary.equivalenceNegation
    eliminationVocabulary.equivalenceDisjunction
    eliminationVocabulary.leftNegation eliminationVocabulary.rightNegation
    eliminationVocabulary.outerNegation
    eliminationVocabulary.conjunctionDisjunction
    (star_33_operatorMatrix operatorVocabulary
      (star_33_102_domainMatrix relationExistential disjunction)) gamma relation)

/-- ✱33·102, reconstructed from ✱33·03 and heterogeneous ✱21·3.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_33_102
    (operatorVocabulary : Star33OperatorVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (eliminationVocabulary : BinaryEliminationVocabulary signature
      (classSort (bindOrder relationOrder .individual) 0)
      (relationSort relationOrder relationExcess)
      (star_33_operatorOrder relationOrder identityBaseOrder identityExcess))
    (relationExistential : ExistentialVocabulary signature .individual
      relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (gamma : Term signature real []
      (classSort (bindOrder relationOrder .individual) 0))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (star_10_35_hypothesis : PM.RamifiedSyntax.BinaryEliminationHypothesis
      eliminationVocabulary
      (star_33_operatorMatrix operatorVocabulary
        (star_33_102_domainMatrix relationExistential disjunction)) gamma relation) :
    Derivation (.assertion (binaryEliminationFormula
      eliminationVocabulary.abstractionExistential
      eliminationVocabulary.leftUniversal eliminationVocabulary.rightUniversal
      eliminationVocabulary.equivalenceNegation
      eliminationVocabulary.equivalenceDisjunction
      eliminationVocabulary.leftNegation eliminationVocabulary.rightNegation
      eliminationVocabulary.outerNegation
      eliminationVocabulary.conjunctionDisjunction
      (star_33_operatorMatrix operatorVocabulary
        (star_33_102_domainMatrix relationExistential disjunction))
      gamma relation)) := by
  have line1 := binaryElimination eliminationVocabulary
    (star_33_operatorMatrix operatorVocabulary
      (star_33_102_domainMatrix relationExistential disjunction)) gamma relation
    star_10_35_hypothesis
  exact line1

private def star_33_103_matrix
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual)) :
    Formula signature real
      [.individual, relationSort relationOrder relationExcess]
      (bindOrder relationOrder .individual) :=
  star_33_04 existential disjunction (.apparent (.succ .zero))
    (.apparent .zero)

def star_33_103_reading
    (vocabulary : BinaryEliminationVocabulary signature .individual
      (relationSort relationOrder relationExcess)
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (x : Term signature real [] .individual)
    (relation : Term signature real []
      (relationSort relationOrder relationExcess)) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:. xFR.≡:(∃ y):xRy.∨ .yRx"
  scopeReading := "F is expanded contextually by ✱33·04 inside the displayed equivalence."
  parsed := .assertion (binaryEliminationFormula
    vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_33_103_matrix existential disjunction) x relation)

/-- ✱33·103, the heterogeneous ✱21·3 instance obtained after ✱33·04.
PM prints no demonstration for this item.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_33_103
    (vocabulary : BinaryEliminationVocabulary signature .individual
      (relationSort relationOrder relationExcess)
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (disjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (x : Term signature real [] .individual)
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (star_10_35_hypothesis : PM.RamifiedSyntax.BinaryEliminationHypothesis vocabulary
      (star_33_103_matrix existential disjunction) x relation) :
    Derivation (.assertion (binaryEliminationFormula
      vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_33_103_matrix existential disjunction) x relation)) := by
  have line1 := binaryElimination vocabulary
    (star_33_103_matrix existential disjunction) x relation
    star_10_35_hypothesis
  exact line1

/-! ## What the rest of ✱33·1 to ✱33·17 still waits for

* ✱33·11, ✱33·111, ✱33·112 assert the identity of `DʻR`, `ᗡʻR`, `CʻR` with a
  class abstraction.  PM cites `[✱33·1.✱30·3.✱20·59]`.  ✱33·1 above is already
  conditional, and `Principia/Deduction/Star30Derived.lean` declares no
  `star_30_3`: the descriptive-function identity is not available.

* ✱33·12, ✱33·121, ✱33·122 assert `E!DʻR` and its companions from
  `[✱33·11.✱14·21]`, so they inherit the previous obstruction.

* ✱33·123, ✱33·124, ✱33·125 are `[✱30·4.✱33·12]`; same inheritance.

* ✱33·13, ✱33·131, ✱33·132 read `x∈ DʻR .≡. (∃ y).xRy`.  Once ✱33·01 has been
  eliminated, both displayed members are the SAME tree,
  `.neg n (.always u (.neg n' (.apply R (x, ·))))`, and asserting one expression
  against itself is what `scripts/verify_two_sided_readings.py` exists to
  reject.  The proposition is faithful only as the CONSEQUENCE of ✱33·11 and
  ✱20·3·57, each member being built from its own printed form; ✱33·11 is not
  available, so the item is not asserted here.

* ✱33·15 and ✱33·152 are stated with the descriptive relations `R⃗` and `R⃖` of
  ✱32·01–·02; `Principia/Deduction/Star32Derived.lean` declares no theorem.

* ✱33·16 asserts the class identity `CʻR=DʻR∪ ᗡʻR`.  After ✱22·34 both members
  of the pointwise equivalence PM derives are, in eliminated form, the one tree
  `sameDisjunction d ((∃ y).xRy) ((∃ y).yRx)`: the same collapse as ✱33·13, and
  it is faithful only through ✱33·13·131, which are not available.

* ✱33·161 is `DʻR⊂ CʻR . ᗡʻR⊂ CʻR`.  Its pointwise content is ✱2·2 and ✱1·3 —
  and is used, in that form, inside `star_33_17` below.  What is missing is only
  the inclusion sign: ✱22·01 expands `α ⊂ β` with `star_20_02`, i.e. with a
  class TERM in the membership place, and `DʻR` is not a term but a description
  waiting on ✱33·11.
-/

/-! ## The two propositions of ✱33 that pass through no contextual abstraction

`DʻR`, `ᗡʻR` and `CʻR` occur in ✱33·14 and ✱33·17 under the membership sign
only, and ✱33·01–·03 expand that membership directly into the quantified
matrices `star_33_01`, `star_33_02` and `star_33_03` printed above.  No class
abstraction has to be eliminated there, so neither proposition needs ✱20·3 or
✱21·3 and neither carries a reducibility-scope premise.

The antecedent `xRy` carries the order of the relation's values, while every
member of the consequent is an existential closure one binder higher.  PM's
typical ambiguity therefore assigns the two sides independently, and the
propositional steps printed in the demonstrations are transported to those two
orders by `MixedOrder.transport`, which replays them through the ✱1 primitives
alone.
-/

namespace Star33Scope

open PM.RamifiedSyntax.MixedOrder

/-- The real-variable context of the printed elementary steps: one variable for
the antecedent and two for the members of the consequent. -/
abbrev elementaryContext : PM.RealContext :=
  [.elementaryProposition, .elementaryProposition, .elementaryProposition]

/-- `p`, the antecedent of the printed elementary steps. -/
def elementaryP : PM.Elementary elementaryContext := .var .zero

/-- `q`, the first member of the printed consequent. -/
def elementaryQ : PM.Elementary elementaryContext := .var (.succ .zero)

/-- `r`, the second member of the printed consequent. -/
def elementaryR : PM.Elementary elementaryContext := .var (.succ (.succ .zero))

/-- `p` is assigned the lower order, `q` and `r` the higher one. -/
def support :
    PM.RealVar elementaryContext .elementaryProposition → BinarySupport
  | .zero => .left
  | .succ .zero => .right
  | .succ (.succ .zero) => .right

/-- The valuation carrying the three ramified formulae at those orders. -/
def valuation
    (negation : BinaryNegations signature)
    (antecedent : Formula signature real [] negation.leftOrder)
    (first second : Formula signature real [] negation.rightOrder) :
    ∀ v : PM.RealVar elementaryContext .elementaryProposition,
      Formula signature real [] (negation.order (support v))
  | .zero => antecedent
  | .succ .zero => first
  | .succ (.succ .zero) => second

/-- Detachment at one assigned order, by ✱1·1 or ✱1·11 according to the
real-variable context. -/
private theorem detachSameOrder
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature real [] order} :
    (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons head tail => exact Derivation.star_1_11_same negation disjunction

/-- PM's ✱3·43 (`Comp`) in the exported shape printed as its line (2). -/
theorem elementaryComp {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ⊃ₚ r) ⊃ₚ (p ⊃ₚ (PM.Elementary.conj q r)))) := by
  have line1 : ⊢ₚ (q ⊃ₚ (r ⊃ₚ (PM.Elementary.conj q r))) :=
    PM.FirstEdition.Volume1.Star3.star_3_2 q r
  have line2 : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ (r ⊃ₚ (PM.Elementary.conj q r)))) :=
    PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star2.star_2_05 p q
        (r ⊃ₚ (PM.Elementary.conj q r)))
  exact PM.Derivation.detach line2
    (PM.Derivation.detach
      (PM.FirstEdition.Volume1.Star2.star_2_77 p r (PM.Elementary.conj q r))
      (PM.FirstEdition.Volume1.Star2.star_2_05 (p ⊃ₚ q)
        (p ⊃ₚ (r ⊃ₚ (PM.Elementary.conj q r)))
        ((p ⊃ₚ r) ⊃ₚ (p ⊃ₚ (PM.Elementary.conj q r)))))

/-- ✱3·43 (`Comp`) with the antecedent and the two members of the consequent at
independently assigned orders. -/
theorem compAtTwoOrders
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (antecedent : Formula signature real [] negation.leftOrder)
    (first second : Formula signature real [] negation.rightOrder)
    (line1 : ⊢ᵣ mixedImplication negation.left disjunction.both
      antecedent first)
    (line2 : ⊢ᵣ mixedImplication negation.left disjunction.both
      antecedent second) :
    ⊢ᵣ mixedImplication negation.left disjunction.both antecedent
      (conjunction negation.right disjunction.right first second) := by
  have printedStep := MixedOrder.transport BinarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (binaryTautology negation disjunction)
    (fun _ => BinarySupport.left) (fun _ => antecedent) support
    (valuation negation antecedent first second)
    (elementaryComp elementaryP elementaryQ elementaryR)
  exact detachSameOrder negation.both disjunction.both line2
    (detachSameOrder negation.both disjunction.both line1 printedStep)

/-- ✱2·06 (`Syll`) with the antecedent at the lower assigned order and the two
remaining members at the higher one. -/
theorem syllAtTwoOrders
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (antecedent : Formula signature real [] negation.leftOrder)
    (first second : Formula signature real [] negation.rightOrder)
    (line1 : ⊢ᵣ mixedImplication negation.left disjunction.both
      antecedent first)
    (line2 : ⊢ᵣ implication negation.right disjunction.right first second) :
    ⊢ᵣ mixedImplication negation.left disjunction.both antecedent second := by
  have printedStep := MixedOrder.transport BinarySupport.combine
    negation.toVocabulary disjunction.toVocabulary
    (binaryTautology negation disjunction)
    (fun _ => BinarySupport.left) (fun _ => antecedent) support
    (valuation negation antecedent first second)
    (PM.FirstEdition.Volume1.Star2.star_2_06 elementaryP elementaryQ
      elementaryR)
  have step := detachSameOrder negation.both disjunction.both line1 printedStep
  exact MixedOrder.detach
    (MixedOrder.binaryOrderCombine negation .right .both)
    negation.right disjunction.both _ _ line2 step

/-- The relation applied to the two real individuals, as it stands in the
antecedent of ✱33·14 and ✱33·17. -/
def applied
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] relationOrder :=
  applyBinary relation x y

/-- The right-hand argument of ✱33·01 is the apparent variable, so the printed
specialization returns the antecedent unchanged. -/
theorem appliedFromRightBinder
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    (applyBinary relation.weaken x.weaken
        (.apparent (.zero : Var [RSort.individual] RSort.individual))).instantiate y
      = applied relation x y := by
  cases relation with
  | real v =>
      cases x with
      | real w => rfl
      | apparent w => exact nomatch w
      | symbol payload => rfl
  | apparent v => exact nomatch v
  | symbol payload =>
      cases x with
      | real w => rfl
      | apparent w => exact nomatch w
      | symbol other => rfl

/-- The left-hand argument of ✱33·02 is the apparent variable, so the printed
specialization returns the antecedent unchanged. -/
theorem appliedFromLeftBinder
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    (applyBinary relation.weaken
        (.apparent (.zero : Var [RSort.individual] RSort.individual))
        y.weaken).instantiate x
      = applied relation x y := by
  cases relation with
  | real v =>
      cases y with
      | real w => rfl
      | apparent w => exact nomatch w
      | symbol payload => rfl
  | apparent v => exact nomatch v
  | symbol payload =>
      cases y with
      | real w => rfl
      | apparent w => exact nomatch w
      | symbol other => rfl

/-- The vocabulary of the two assigned orders of ✱33·14 and ✱33·17. -/
def orders
    (matrixNegation : signature.Negation relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (mixedNegation : signature.Negation
      (max relationOrder (bindOrder relationOrder .individual))) :
    BinaryNegations signature where
  leftOrder := relationOrder
  rightOrder := bindOrder relationOrder .individual
  left := matrixNegation
  right := scopeNegation
  both := mixedNegation

/-- The disjunction meanings of those two assigned orders. -/
def orderDisjunctions
    (matrixNegation : signature.Negation relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (mixedNegation : signature.Negation
      (max relationOrder (bindOrder relationOrder .individual)))
    (matrixDisjunction : signature.Disjunction relationOrder)
    (scopeDisjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (mixedDisjunction : signature.Disjunction
      (max relationOrder (bindOrder relationOrder .individual))) :
    BinaryDisjunctions signature
      (orders matrixNegation scopeNegation mixedNegation) where
  left := matrixDisjunction
  right := scopeDisjunction
  both := mixedDisjunction

end Star33Scope

/-- The printed antecedent of ✱33·14, `xRy`. -/
def star_33_14_left
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] relationOrder :=
  Star33Scope.applied relation x y

/-- The printed consequent of ✱33·14, `x ∈ DʻR . y ∈ ᗡʻR`, built from the two
eliminable expansions ✱33·01 and ✱33·02. -/
def star_33_14_right
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (scopeDisjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] (bindOrder relationOrder .individual) :=
  conjunction scopeNegation scopeDisjunction
    (star_33_01 existential relation x) (star_33_02 existential relation y)

def star_33_14_reading
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (matrixNegation : signature.Negation relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (scopeDisjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (mixedDisjunction : signature.Disjunction
      (max relationOrder (bindOrder relationOrder .individual)))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱33·14. ⊢:xRy.⊃.x∈ DʻR.y∈ ᗡʻR"
  scopeReading :=
    "Each apparent variable of the consequent is bound inside its own member; the antecedent keeps the order of the relation's values."
  parsed := .assertion (mixedImplication matrixNegation mixedDisjunction
    (star_33_14_left relation x y)
    (star_33_14_right existential scopeNegation scopeDisjunction
      relation x y))

/-- ✱33·14, following the printed `⊢.✱10·24` line and its composition.
PM's two printed applications of ✱10·24 give the two members separately; the
printed layout `⊃:(∃ y).xRy:(∃ x).xRy` conjoins them, which is ✱3·43.
Membership in `DʻR` and in `ᗡʻR` appears in the eliminated form supplied by
✱33·01 and ✱33·02, exactly as the bracket `[✱33·13]` of the printed
demonstration licenses.
`demonstration_provenance: follows-printed`. -/
theorem star_33_14
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (matrixNegation : signature.Negation relationOrder)
    (matrixDisjunction : signature.Disjunction relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (scopeDisjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (mixedNegation : signature.Negation
      (max relationOrder (bindOrder relationOrder .individual)))
    (mixedDisjunction : signature.Disjunction
      (max relationOrder (bindOrder relationOrder .individual)))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    Derivation (star_33_14_reading existential matrixNegation scopeNegation
      scopeDisjunction mixedDisjunction relation x y).parsed := by
  have line1 := star_10_24 existential matrixNegation mixedDisjunction
    (applyBinary relation.weaken x.weaken (.apparent .zero)) y
  have line2 := star_10_24 existential matrixNegation mixedDisjunction
    (applyBinary relation.weaken (.apparent .zero) y.weaken) x
  change ⊢ᵣ mixedImplication matrixNegation mixedDisjunction
    ((applyBinary relation.weaken x.weaken (.apparent .zero)).instantiate y)
    (star_33_01 existential relation x) at line1
  change ⊢ᵣ mixedImplication matrixNegation mixedDisjunction
    ((applyBinary relation.weaken (.apparent .zero) y.weaken).instantiate x)
    (star_33_02 existential relation y) at line2
  rw [Star33Scope.appliedFromRightBinder] at line1
  rw [Star33Scope.appliedFromLeftBinder] at line2
  exact Star33Scope.compAtTwoOrders
    (Star33Scope.orders matrixNegation scopeNegation mixedNegation)
    (Star33Scope.orderDisjunctions matrixNegation scopeNegation mixedNegation
      matrixDisjunction scopeDisjunction mixedDisjunction)
    (Star33Scope.applied relation x y)
    (star_33_01 existential relation x) (star_33_02 existential relation y)
    line1 line2

/-- The printed antecedent of ✱33·17, `xRy`. -/
def star_33_17_left
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] relationOrder :=
  Star33Scope.applied relation x y

/-- The printed consequent of ✱33·17, `x,y ∈ CʻR`, i.e. the product of the two
eliminable expansions of ✱33·03. -/
def star_33_17_right
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (scopeDisjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    Formula signature real [] (bindOrder relationOrder .individual) :=
  conjunction scopeNegation scopeDisjunction
    (star_33_03 existential scopeDisjunction relation x)
    (star_33_03 existential scopeDisjunction relation y)

def star_33_17_reading
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (matrixNegation : signature.Negation relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (scopeDisjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (mixedDisjunction : signature.Disjunction
      (max relationOrder (bindOrder relationOrder .individual)))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱33·17. ⊢:xRy.⊃.x,y∈ CʻR"
  scopeReading :=
    "Both members of the consequent bind their own apparent variable inside ✱33·03; the antecedent keeps the order of the relation's values."
  parsed := .assertion (mixedImplication matrixNegation mixedDisjunction
    (star_33_17_left relation x y)
    (star_33_17_right existential scopeNegation scopeDisjunction
      relation x y))

/-- ✱33·17.  PM writes `[✱33·14·161]`.  ✱33·161 is a class inclusion, and
class inclusion is not yet available unconditionally, so its pointwise content
is used directly: the two printed propositions that carry it are ✱2·2 for the
first member of ✱33·03 and ✱1·3 for the second.  The rest is the ✱10·24 pair
of ✱33·14 followed by ✱2·06 and the ✱3·43 composition.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_33_17
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (matrixNegation : signature.Negation relationOrder)
    (matrixDisjunction : signature.Disjunction relationOrder)
    (scopeNegation : signature.Negation (bindOrder relationOrder .individual))
    (scopeDisjunction : signature.Disjunction
      (bindOrder relationOrder .individual))
    (mixedNegation : signature.Negation
      (max relationOrder (bindOrder relationOrder .individual)))
    (mixedDisjunction : signature.Disjunction
      (max relationOrder (bindOrder relationOrder .individual)))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) :
    Derivation (star_33_17_reading existential matrixNegation scopeNegation
      scopeDisjunction mixedDisjunction relation x y).parsed := by
  let negations := Star33Scope.orders matrixNegation scopeNegation mixedNegation
  let disjunctions := Star33Scope.orderDisjunctions matrixNegation scopeNegation
    mixedNegation matrixDisjunction scopeDisjunction mixedDisjunction
  have line1 := star_10_24 existential matrixNegation mixedDisjunction
    (applyBinary relation.weaken x.weaken (.apparent .zero)) y
  have line2 := star_10_24 existential matrixNegation mixedDisjunction
    (applyBinary relation.weaken (.apparent .zero) y.weaken) x
  change ⊢ᵣ mixedImplication matrixNegation mixedDisjunction
    ((applyBinary relation.weaken x.weaken (.apparent .zero)).instantiate y)
    (star_33_01 existential relation x) at line1
  change ⊢ᵣ mixedImplication matrixNegation mixedDisjunction
    ((applyBinary relation.weaken (.apparent .zero) y.weaken).instantiate x)
    (star_33_02 existential relation y) at line2
  rw [Star33Scope.appliedFromRightBinder] at line1
  rw [Star33Scope.appliedFromLeftBinder] at line2
  have line3 := star_2_2 scopeNegation scopeDisjunction
    (star_33_01 existential relation x) (star_33_02 existential relation x)
  have line4 := Derivation.star_1_3_same scopeNegation scopeDisjunction
    (star_33_01 existential relation y) (star_33_02 existential relation y)
  have line5 := Star33Scope.syllAtTwoOrders negations disjunctions
    (Star33Scope.applied relation x y)
    (star_33_01 existential relation x)
    (star_33_03 existential scopeDisjunction relation x) line1 line3
  have line6 := Star33Scope.syllAtTwoOrders negations disjunctions
    (Star33Scope.applied relation x y)
    (star_33_02 existential relation y)
    (star_33_03 existential scopeDisjunction relation y) line2 line4
  exact Star33Scope.compAtTwoOrders negations disjunctions
    (Star33Scope.applied relation x y)
    (star_33_03 existential scopeDisjunction relation x)
    (star_33_03 existential scopeDisjunction relation y) line5 line6

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_33_01_unfold
#print axioms PM.RamifiedSyntax.star_33_02_unfold
#print axioms PM.RamifiedSyntax.star_33_03_unfold
#print axioms PM.RamifiedSyntax.star_33_04_unfold
#print axioms PM.RamifiedSyntax.star_33_103
#print axioms PM.RamifiedSyntax.star_33_1
#print axioms PM.RamifiedSyntax.star_33_101
#print axioms PM.RamifiedSyntax.star_33_102
#print axioms PM.RamifiedSyntax.star_33_14
#print axioms PM.RamifiedSyntax.star_33_17
