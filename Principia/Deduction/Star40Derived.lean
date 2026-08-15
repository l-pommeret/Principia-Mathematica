import Principia.Deduction.Star20Derived
import Principia.FirstEdition.Volume1.Star40Source
import Principia.Syntax.Printed

namespace PM.RamifiedSyntax

structure Star40Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-! # Derived propositions of PM I, ✱40 -/

/-- The matrix printed at ✱40·01.  The apparent individual is `x`; the
bound predicative class is `α`. -/
def star_40_01_matrix
    (classUniversal : signature.Universal (classSort order 0) order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0)) :
    Formula signature real [.individual]
      (bindOrder order (classSort order 0)) :=
  .always classUniversal
    (implication negation disjunction
      (applyUnary kappa.weaken.weaken (.apparent .zero))
      (star_20_02 (.apparent .zero) (.apparent (.succ .zero))))

/-- ✱40·01, with class abstraction eliminated contextually by ✱20·01. -/
def star_40_01
    (existential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (classUniversal : signature.Universal (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (continuation : Formula signature real
      [classSort (bindOrder order (classSort order 0)) 0] scopeOrder) :=
  star_20_01 existential individualUniversal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction
    (star_40_01_matrix classUniversal matrixNegation matrixDisjunction kappa)
    continuation

theorem star_40_01_unfold
    (existential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (classUniversal : signature.Universal (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (continuation : Formula signature real
      [classSort (bindOrder order (classSort order 0)) 0] scopeOrder) :
    star_40_01 existential individualUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction classUniversal matrixNegation matrixDisjunction
      kappa continuation =
      star_20_01 existential individualUniversal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction
        (star_40_01_matrix classUniversal matrixNegation matrixDisjunction kappa)
        continuation := rfl

/-- The matrix printed at ✱40·02. -/
def star_40_02_matrix
    (classExistential : ExistentialVocabulary signature
      (classSort order 0) order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0)) :
    Formula signature real [.individual]
      (bindOrder order (classSort order 0)) :=
  let liftedKappa : Term signature real [classSort order 0, .individual]
      (.function [classSort order 0] order 0) :=
    kappa.rename (emptyRenaming (target := [classSort order 0, .individual]))
  let alpha : Term signature real [classSort order 0, .individual]
      (classSort order 0) := .apparent .zero
  let x : Term signature real [classSort order 0, .individual] .individual :=
    .apparent (.succ .zero)
  Formula.sometimes (apparent := [.individual]) classExistential
    (show Formula signature real [classSort order 0, .individual] order from
      .neg negation
        (sameDisjunction disjunction
          (.neg negation (applyUnary liftedKappa alpha))
          (.neg negation (star_20_02 alpha x))))

/-- ✱40·02, with class abstraction eliminated contextually by ✱20·01. -/
def star_40_02
    (existential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (classExistential : ExistentialVocabulary signature
      (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (continuation : Formula signature real
      [classSort (bindOrder order (classSort order 0)) 0] scopeOrder) :=
  star_20_01 existential individualUniversal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction
    (star_40_02_matrix classExistential matrixNegation matrixDisjunction kappa)
    continuation

theorem star_40_02_unfold
    (existential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        scopeOrder))
    (classExistential : ExistentialVocabulary signature
      (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (continuation : Formula signature real
      [classSort (bindOrder order (classSort order 0)) 0] scopeOrder) :
    star_40_02 existential individualUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction classExistential matrixNegation
      matrixDisjunction kappa continuation =
      star_20_01 existential individualUniversal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction
        (star_40_02_matrix classExistential matrixNegation matrixDisjunction kappa)
        continuation := rfl

/-- The reducibility-scope transport still required by the unary elimination
theorem.  It is distinct from ✱10·35: the two existential vocabularies and
their bodies do not reduce to one another. -/
def Star40ReducibilityScopeTransport
    (abstractionExistential : ExistentialVocabulary signature
      (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) resultOrder))
    (reducibilityExistential : ExistentialVocabulary signature
      (classSort resultOrder 0) (bindOrder resultOrder .individual))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) resultOrder))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual)
        (classSort resultOrder 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder resultOrder .individual)
          (classSort resultOrder 0))
        (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
          (classSort resultOrder 0))))
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) : Prop :=
  (⊢ᵣ star_20_3_transportFormula universal equivalenceNegation
    equivalenceDisjunction leftNegation conjunctionDisjunction matrix x) →
  ⊢ᵣ mixedImplication reducibilityOuterNegation bridgeDisjunction
    (star_12_1_formula reducibilityExistential universal
      equivalenceNegation equivalenceDisjunction matrix)
    (star_20_3_formula abstractionExistential universal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x)

/-- Audited reading of ✱40·1. -/
def star_40_1_reading
    (abstractionExistential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (classUniversal : signature.Universal (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (x : Term signature real [] .individual) :
    Star40Reading signature real where
  printed := PM.pmPrinted "✱40·1. ⊢ :: x ∈ pʻκ .≡ : α ∈ κ .⊃ₐ. x ∈ α  [✱20·3.(✱40·01)]"
  parsed := .assertion
    (star_40_01 abstractionExistential individualUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction classUniversal matrixNegation
      matrixDisjunction kappa
      (star_20_3_continuation equivalenceNegation equivalenceDisjunction
        (star_40_01_matrix classUniversal matrixNegation matrixDisjunction kappa)
        x))
  scopeReading := "The incomplete product-class symbol has the scope of the displayed equivalence."

/-- ✱40·1 by the printed `[✱20·3.(✱40·01)]` route.

The named reducibility-scope transport is inherited from the still-conditional
✱20·3.  `direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_40_1
    (abstractionExistential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (reducibilityExistential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (classSort (bindOrder order (classSort order 0)) 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (classSort order 0)) .individual)
          (classSort (bindOrder order (classSort order 0)) 0))
        (bindOrder
          (max
            (bindOrder (bindOrder order (classSort order 0)) .individual)
            (bindOrder order (classSort order 0)))
          (classSort (bindOrder order (classSort order 0)) 0))))
    (finalNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder (bindOrder order (classSort order 0)) .individual)
          (bindOrder order (classSort order 0)))
        (classSort (bindOrder order (classSort order 0)) 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder (bindOrder order (classSort order 0)) .individual)
          (bindOrder order (classSort order 0)))
        (classSort (bindOrder order (classSort order 0)) 0)))
    (classUniversal : signature.Universal (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (x : Term signature real [] .individual)
    (reducibility_scope_transport : Star40ReducibilityScopeTransport
      abstractionExistential reducibilityExistential individualUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction reducibilityOuterNegation
      bridgeDisjunction
      (star_40_01_matrix classUniversal matrixNegation matrixDisjunction kappa)
      x) :
    Derivation (.assertion
      (star_40_01 abstractionExistential individualUniversal
        equivalenceNegation equivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction classUniversal matrixNegation
        matrixDisjunction kappa
        (star_20_3_continuation equivalenceNegation equivalenceDisjunction
          (star_40_01_matrix classUniversal matrixNegation matrixDisjunction kappa)
          x))) := by
  have line1 := star_20_3 abstractionExistential reducibilityExistential
    individualUniversal equivalenceNegation equivalenceDisjunction
    leftNegation rightNegation outerNegation conjunctionDisjunction
    reducibilityOuterNegation bridgeDisjunction finalNegation
    finalDisjunction
    (star_40_01_matrix classUniversal matrixNegation matrixDisjunction kappa)
    x reducibility_scope_transport
  change Derivation (.assertion
    (star_40_01 abstractionExistential individualUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction classUniversal matrixNegation
      matrixDisjunction kappa
      (star_20_3_continuation equivalenceNegation equivalenceDisjunction
        (star_40_01_matrix classUniversal matrixNegation matrixDisjunction kappa)
        x))) at line1
  exact line1

/-- Audited reading of ✱40·11. -/
def star_40_11_reading
    (abstractionExistential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (classExistential : ExistentialVocabulary signature
      (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (x : Term signature real [] .individual) :
    Star40Reading signature real where
  printed := PM.pmPrinted "✱40·11. ⊢ : x ∈ sʻκ .≡. (∃α). α ∈ κ . x ∈ α  [✱20·3.(✱40·02)]"
  parsed := .assertion
    (star_40_02 abstractionExistential individualUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction classExistential matrixNegation
      matrixDisjunction kappa
      (star_20_3_continuation equivalenceNegation equivalenceDisjunction
        (star_40_02_matrix classExistential matrixNegation matrixDisjunction kappa)
        x))
  scopeReading := "The incomplete sum-class symbol has the scope of the displayed equivalence."

/-- ✱40·11 by the printed `[✱20·3.(✱40·02)]` route.

The named reducibility-scope transport is inherited from the still-conditional
✱20·3.  `direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_40_11
    (abstractionExistential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (reducibilityExistential : ExistentialVocabulary signature
      (classSort (bindOrder order (classSort order 0)) 0)
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (individualUniversal : signature.Universal .individual
      (bindOrder order (classSort order 0)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order (classSort order 0)) .individual))
    (rightNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (bindOrder order (classSort order 0))))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder order (classSort order 0)) .individual)
        (classSort (bindOrder order (classSort order 0)) 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder (bindOrder order (classSort order 0)) .individual)
          (classSort (bindOrder order (classSort order 0)) 0))
        (bindOrder
          (max
            (bindOrder (bindOrder order (classSort order 0)) .individual)
            (bindOrder order (classSort order 0)))
          (classSort (bindOrder order (classSort order 0)) 0))))
    (finalNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder (bindOrder order (classSort order 0)) .individual)
          (bindOrder order (classSort order 0)))
        (classSort (bindOrder order (classSort order 0)) 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder (bindOrder order (classSort order 0)) .individual)
          (bindOrder order (classSort order 0)))
        (classSort (bindOrder order (classSort order 0)) 0)))
    (classExistential : ExistentialVocabulary signature
      (classSort order 0) order)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (kappa : Term signature real []
      (.function [classSort order 0] order 0))
    (x : Term signature real [] .individual)
    (reducibility_scope_transport : Star40ReducibilityScopeTransport
      abstractionExistential reducibilityExistential individualUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction reducibilityOuterNegation
      bridgeDisjunction
      (star_40_02_matrix classExistential matrixNegation matrixDisjunction kappa)
      x) :
    Derivation (.assertion
      (star_40_02 abstractionExistential individualUniversal
        equivalenceNegation equivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction classExistential matrixNegation
        matrixDisjunction kappa
        (star_20_3_continuation equivalenceNegation equivalenceDisjunction
          (star_40_02_matrix classExistential matrixNegation matrixDisjunction kappa)
          x))) := by
  have line1 := star_20_3 abstractionExistential reducibilityExistential
    individualUniversal equivalenceNegation equivalenceDisjunction
    leftNegation rightNegation outerNegation conjunctionDisjunction
    reducibilityOuterNegation bridgeDisjunction finalNegation
    finalDisjunction
    (star_40_02_matrix classExistential matrixNegation matrixDisjunction kappa)
    x reducibility_scope_transport
  change Derivation (.assertion
    (star_40_02 abstractionExistential individualUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction classExistential matrixNegation
      matrixDisjunction kappa
      (star_20_3_continuation equivalenceNegation equivalenceDisjunction
        (star_40_02_matrix classExistential matrixNegation matrixDisjunction kappa)
        x))) at line1
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_40_1
#print axioms PM.RamifiedSyntax.star_40_11
