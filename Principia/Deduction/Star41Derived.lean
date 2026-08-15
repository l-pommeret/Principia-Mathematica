import Principia.Deduction.Star21Derived
import Principia.FirstEdition.Volume1.Star41Source
import Principia.Syntax.Printed

namespace PM.RamifiedSyntax

structure Star41Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-! # Derived propositions of PM I, ✱41 -/

/-- The matrix printed at ✱41·01.  The two apparent individuals are `x,y`;
the bound predicative relation is `R`. -/
def star_41_01_matrix
    (relationUniversal : signature.Universal (relationSort order 0) order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0)) :
    Formula signature real [.individual, .individual]
      (bindOrder order (relationSort order 0)) :=
  let liftedLambda : Term signature real
      [relationSort order 0, .individual, .individual]
      (.function [relationSort order 0] order 0) :=
    lambda.rename (emptyRenaming
      (target := [relationSort order 0, .individual, .individual]))
  let relation : Term signature real
      [relationSort order 0, .individual, .individual]
      (relationSort order 0) := .apparent .zero
  let x : Term signature real
      [relationSort order 0, .individual, .individual] .individual :=
    .apparent (.succ .zero)
  let y : Term signature real
      [relationSort order 0, .individual, .individual] .individual :=
    .apparent (.succ (.succ .zero))
  .always relationUniversal
    (implication negation disjunction
      (applyUnary liftedLambda relation)
      (star_21_02 relation x y))

/-- ✱41·01, with relation abstraction eliminated contextually by ✱21·01. -/
def star_41_01
    (existential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (relationUniversal : signature.Universal (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (continuation : Formula signature real
      [relationSort (bindOrder order (relationSort order 0)) 0] scopeOrder) :=
  star_21_01 existential leftUniversal rightUniversal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction
    (star_41_01_matrix relationUniversal matrixNegation matrixDisjunction lambda)
    continuation

theorem star_41_01_unfold
    (existential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (relationUniversal : signature.Universal (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (continuation : Formula signature real
      [relationSort (bindOrder order (relationSort order 0)) 0] scopeOrder) :
    star_41_01 existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction relationUniversal matrixNegation
      matrixDisjunction lambda continuation =
      star_21_01 existential leftUniversal rightUniversal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction
        (star_41_01_matrix relationUniversal matrixNegation matrixDisjunction lambda)
        continuation := rfl

/-- The matrix printed at ✱41·02. -/
def star_41_02_matrix
    (relationExistential : ExistentialVocabulary signature
      (relationSort order 0) order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0)) :
    Formula signature real [.individual, .individual]
      (bindOrder order (relationSort order 0)) :=
  let liftedLambda : Term signature real
      [relationSort order 0, .individual, .individual]
      (.function [relationSort order 0] order 0) :=
    lambda.rename (emptyRenaming
      (target := [relationSort order 0, .individual, .individual]))
  let relation : Term signature real
      [relationSort order 0, .individual, .individual]
      (relationSort order 0) := .apparent .zero
  let x : Term signature real
      [relationSort order 0, .individual, .individual] .individual :=
    .apparent (.succ .zero)
  let y : Term signature real
      [relationSort order 0, .individual, .individual] .individual :=
    .apparent (.succ (.succ .zero))
  Formula.sometimes (apparent := [.individual, .individual])
    relationExistential
    (show Formula signature real
        [relationSort order 0, .individual, .individual] order from
      .neg negation
        (sameDisjunction disjunction
          (.neg negation (applyUnary liftedLambda relation))
          (.neg negation (star_21_02 relation x y))))

/-- ✱41·02, with relation abstraction eliminated contextually by ✱21·01. -/
def star_41_02
    (existential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (relationExistential : ExistentialVocabulary signature
      (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (continuation : Formula signature real
      [relationSort (bindOrder order (relationSort order 0)) 0] scopeOrder) :=
  star_21_01 existential leftUniversal rightUniversal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction
    (star_41_02_matrix relationExistential matrixNegation matrixDisjunction lambda)
    continuation

theorem star_41_02_unfold
    (existential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        scopeOrder))
    (relationExistential : ExistentialVocabulary signature
      (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (continuation : Formula signature real
      [relationSort (bindOrder order (relationSort order 0)) 0] scopeOrder) :
    star_41_02 existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction relationExistential matrixNegation
      matrixDisjunction lambda continuation =
      star_21_01 existential leftUniversal rightUniversal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction
        (star_41_02_matrix relationExistential matrixNegation
          matrixDisjunction lambda)
        continuation := rfl

/-- The reducibility-scope transport still required by the binary elimination
theorem.  It is distinct from ✱10·35: the two existential vocabularies and
their bodies do not reduce to one another. -/
def Star41ReducibilityScopeTransport
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (reducibilityExistential : ExistentialVocabulary signature
      (relationSort resultOrder 0)
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder resultOrder .individual) .individual)
        (relationSort resultOrder 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder resultOrder .individual) .individual)
          (relationSort resultOrder 0))
        (bindOrder
          (max (bindOrder (bindOrder resultOrder .individual) .individual)
            resultOrder)
          (relationSort resultOrder 0))))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) : Prop :=
  (⊢ᵣ star_21_3_transportFormula leftUniversal rightUniversal
    equivalenceNegation equivalenceDisjunction leftNegation
    conjunctionDisjunction matrix x y) →
  ⊢ᵣ mixedImplication reducibilityOuterNegation bridgeDisjunction
    (star_12_11_formula reducibilityExistential leftUniversal
      rightUniversal equivalenceNegation equivalenceDisjunction matrix)
    (star_21_3_formula abstractionExistential leftUniversal
      rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
      rightNegation outerNegation conjunctionDisjunction matrix x y)

/-- Audited reading of ✱41·1. -/
def star_41_1_reading
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (relationUniversal : signature.Universal (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (x y : Term signature real [] .individual) :
    Star41Reading signature real where
  printed := PM.pmPrinted "✱41·1. ⊢ :. x(ṗʻλ)y .≡: R ∈ λ .⊃_R. xRy"
  parsed := .assertion
    (star_41_01 abstractionExistential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction relationUniversal matrixNegation
      matrixDisjunction lambda
      (star_21_3_continuation equivalenceNegation equivalenceDisjunction
        (star_41_01_matrix relationUniversal matrixNegation matrixDisjunction lambda)
        x y))
  scopeReading := "The incomplete product-relation symbol has the scope of the displayed equivalence."

/-- ✱41·1 by specialization of the eliminative relation theorem ✱21·3.

PM prints no demonstration, so this is an editorial reconstruction.  The
named reducibility-scope transport is inherited from the still-conditional
✱21·3.  `direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_41_1
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (reducibilityExistential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (relationSort (bindOrder order (relationSort order 0)) 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder (bindOrder order (relationSort order 0)) .individual)
            .individual)
          (relationSort (bindOrder order (relationSort order 0)) 0))
        (bindOrder
          (max
            (bindOrder
              (bindOrder (bindOrder order (relationSort order 0)) .individual)
              .individual)
            (bindOrder order (relationSort order 0)))
          (relationSort (bindOrder order (relationSort order 0)) 0))))
    (finalNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder
            (bindOrder (bindOrder order (relationSort order 0)) .individual)
            .individual)
          (bindOrder order (relationSort order 0)))
        (relationSort (bindOrder order (relationSort order 0)) 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder
            (bindOrder (bindOrder order (relationSort order 0)) .individual)
            .individual)
          (bindOrder order (relationSort order 0)))
        (relationSort (bindOrder order (relationSort order 0)) 0)))
    (relationUniversal : signature.Universal (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (x y : Term signature real [] .individual)
    (reducibility_scope_transport : Star41ReducibilityScopeTransport
      abstractionExistential reducibilityExistential leftUniversal
      rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
      rightNegation outerNegation conjunctionDisjunction
      reducibilityOuterNegation bridgeDisjunction
      (star_41_01_matrix relationUniversal matrixNegation matrixDisjunction lambda)
      x y) :
    Derivation (.assertion
      (star_41_01 abstractionExistential leftUniversal rightUniversal
        equivalenceNegation equivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction relationUniversal matrixNegation
        matrixDisjunction lambda
        (star_21_3_continuation equivalenceNegation equivalenceDisjunction
          (star_41_01_matrix relationUniversal matrixNegation matrixDisjunction lambda)
          x y))) := by
  have line1 := star_21_3 abstractionExistential reducibilityExistential
    leftUniversal rightUniversal equivalenceNegation equivalenceDisjunction
    leftNegation rightNegation outerNegation conjunctionDisjunction
    reducibilityOuterNegation bridgeDisjunction finalNegation
    finalDisjunction
    (star_41_01_matrix relationUniversal matrixNegation matrixDisjunction lambda)
    x y reducibility_scope_transport
  change Derivation (.assertion
    (star_41_01 abstractionExistential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction relationUniversal matrixNegation
      matrixDisjunction lambda
      (star_21_3_continuation equivalenceNegation equivalenceDisjunction
        (star_41_01_matrix relationUniversal matrixNegation matrixDisjunction lambda)
        x y))) at line1
  exact line1

/-- Audited reading of ✱41·11. -/
def star_41_11_reading
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (relationExistential : ExistentialVocabulary signature
      (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (x y : Term signature real [] .individual) :
    Star41Reading signature real where
  printed := PM.pmPrinted "✱41·11. ⊢ :x(ṡʻλ)y .≡. (∃ R) . R ∈ λ . xRy"
  parsed := .assertion
    (star_41_02 abstractionExistential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction relationExistential matrixNegation
      matrixDisjunction lambda
      (star_21_3_continuation equivalenceNegation equivalenceDisjunction
        (star_41_02_matrix relationExistential matrixNegation matrixDisjunction lambda)
        x y))
  scopeReading := "The incomplete sum-relation symbol has the scope of the displayed equivalence."

/-- ✱41·11 by specialization of the eliminative relation theorem ✱21·3.

PM prints no demonstration, so this is an editorial reconstruction.  The
named reducibility-scope transport is inherited from the still-conditional
✱21·3.  `direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_41_11
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (reducibilityExistential : ExistentialVocabulary signature
      (relationSort (bindOrder order (relationSort order 0)) 0)
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (relationSort order 0)))
    (rightUniversal : signature.Universal .individual
      (bindOrder (bindOrder order (relationSort order 0)) .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (relationSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (relationSort order 0)) .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (relationSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (bindOrder order (relationSort order 0))))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder (bindOrder order (relationSort order 0)) .individual)
          .individual)
        (relationSort (bindOrder order (relationSort order 0)) 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder (bindOrder order (relationSort order 0)) .individual)
            .individual)
          (relationSort (bindOrder order (relationSort order 0)) 0))
        (bindOrder
          (max
            (bindOrder
              (bindOrder (bindOrder order (relationSort order 0)) .individual)
              .individual)
            (bindOrder order (relationSort order 0)))
          (relationSort (bindOrder order (relationSort order 0)) 0))))
    (finalNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder
            (bindOrder (bindOrder order (relationSort order 0)) .individual)
            .individual)
          (bindOrder order (relationSort order 0)))
        (relationSort (bindOrder order (relationSort order 0)) 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder
            (bindOrder (bindOrder order (relationSort order 0)) .individual)
            .individual)
          (bindOrder order (relationSort order 0)))
        (relationSort (bindOrder order (relationSort order 0)) 0)))
    (relationExistential : ExistentialVocabulary signature
      (relationSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (lambda : Term signature real []
      (.function [relationSort order 0] order 0))
    (x y : Term signature real [] .individual)
    (reducibility_scope_transport : Star41ReducibilityScopeTransport
      abstractionExistential reducibilityExistential leftUniversal
      rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
      rightNegation outerNegation conjunctionDisjunction
      reducibilityOuterNegation bridgeDisjunction
      (star_41_02_matrix relationExistential matrixNegation matrixDisjunction lambda)
      x y) :
    Derivation (.assertion
      (star_41_02 abstractionExistential leftUniversal rightUniversal
        equivalenceNegation equivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction relationExistential matrixNegation
        matrixDisjunction lambda
        (star_21_3_continuation equivalenceNegation equivalenceDisjunction
          (star_41_02_matrix relationExistential matrixNegation matrixDisjunction lambda)
          x y))) := by
  have line1 := star_21_3 abstractionExistential reducibilityExistential
    leftUniversal rightUniversal equivalenceNegation equivalenceDisjunction
    leftNegation rightNegation outerNegation conjunctionDisjunction
    reducibilityOuterNegation bridgeDisjunction finalNegation
    finalDisjunction
    (star_41_02_matrix relationExistential matrixNegation matrixDisjunction lambda)
    x y reducibility_scope_transport
  change Derivation (.assertion
    (star_41_02 abstractionExistential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction relationExistential matrixNegation
      matrixDisjunction lambda
      (star_21_3_continuation equivalenceNegation equivalenceDisjunction
        (star_41_02_matrix relationExistential matrixNegation matrixDisjunction lambda)
        x y))) at line1
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_41_1
#print axioms PM.RamifiedSyntax.star_41_11
