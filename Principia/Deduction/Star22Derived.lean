import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star10Derived
import Principia.Deduction.Star20Derived
import Principia.FirstEdition.Volume1.Star22Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱22

The class-forming signs of this number are incomplete symbols.  The four
class-valued operations below therefore take a continuation and expand by
✱20·01; they do not manufacture class terms.  Membership is ✱20·02.
-/

/-- The vocabulary needed by one predicative class abstraction ✱20·01. -/
structure Star22ClassVocabulary (signature : Signature)
    (order scopeOrder : Nat) where
  existential : ExistentialVocabulary signature (classSort order 0)
    (max (bindOrder order .individual) scopeOrder)
  universal : signature.Universal .individual order
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation (bindOrder order .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder order .individual) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder order .individual) scopeOrder)

/-- ✱22·01: inclusion, expanded as universal pointwise implication. -/
def star_22_01
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    Formula signature real [] (bindOrder order .individual) :=
  .always universal
    (implication negation disjunction
      (star_20_02 alpha.weaken (.apparent .zero))
      (star_20_02 beta.weaken (.apparent .zero)))

theorem star_22_01_unfold
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    star_22_01 universal negation disjunction alpha beta =
      .always universal
        (implication negation disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 beta.weaken (.apparent .zero))) := rfl

/-- ✱22·02: intersection, as the contextual abstraction ✱20·01. -/
def star_22_02 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (sameDisjunction disjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      (.neg negation (star_20_02 beta.weaken (.apparent .zero))))) continuation

theorem star_22_02_unfold
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_22_02 vocabulary negation disjunction alpha beta continuation =
      star_20_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (.neg negation (sameDisjunction disjunction
          (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
          (.neg negation (star_20_02 beta.weaken (.apparent .zero)))))
        continuation := rfl

/-- ✱22·03: union, as the contextual abstraction ✱20·01. -/
def star_22_03 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (sameDisjunction disjunction
      (star_20_02 alpha.weaken (.apparent .zero))
      (star_20_02 beta.weaken (.apparent .zero))) continuation

theorem star_22_03_unfold
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_22_03 vocabulary disjunction alpha beta continuation =
      star_20_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (sameDisjunction disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 beta.weaken (.apparent .zero))) continuation := rfl

/-- ✱22·04: complement, as the contextual abstraction ✱20·01. -/
def star_22_04 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (alpha : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (star_20_02 alpha.weaken (.apparent .zero))) continuation

theorem star_22_04_unfold
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (alpha : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_22_04 vocabulary negation alpha continuation =
      star_20_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
        continuation := rfl

/-- ✱22·05: difference, with ✱22·02 and ✱22·04 fully eliminated. -/
def star_22_05 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (sameDisjunction disjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      (.neg negation (.neg negation
        (star_20_02 beta.weaken (.apparent .zero)))))) continuation

theorem star_22_05_unfold
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_22_05 vocabulary negation disjunction alpha beta continuation =
      star_20_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (.neg negation (sameDisjunction disjunction
          (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
          (.neg negation (.neg negation
            (star_20_02 beta.weaken (.apparent .zero)))))) continuation := rfl

/-! ### Definitional class-operation assertions -/

/-- Audited contextual reading of ✱22·2. -/
def star_22_2_reading
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . α ∩ β = ẑx(x ε α . x ε β)"
  scopeReading := "Both incomplete class abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_22_02 vocabulary negation disjunction alpha beta continuation)
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.neg negation (sameDisjunction disjunction
        (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
        (.neg negation (star_20_02 beta.weaken (.apparent .zero)))))
      continuation))

/-- ✱22·2, following PM's printed `[✱20·2.(✱22·02)]` route.  After
eliminating ✱22·02, the required ✱20·2 instance is reflexivity of the same
contextual abstraction.
`demonstration_provenance: follows-printed`. -/
theorem star_22_2
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    Derivation (star_22_2_reading vocabulary negation disjunction
      finalNegation finalDisjunction alpha beta continuation).parsed := by
  have line1 := star_22_02_unfold vocabulary negation disjunction alpha beta
    continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.neg negation (sameDisjunction disjunction
        (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
        (.neg negation (star_20_02 beta.weaken (.apparent .zero)))))
      continuation)
  unfold star_22_2_reading
  rw [line1]
  exact line2

/-- Audited contextual reading of ✱22·3. -/
def star_22_3_reading
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . α ∪ β = ẑx(x ε α .∨. x ε β)"
  scopeReading := "Both incomplete class abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_22_03 vocabulary disjunction alpha beta continuation)
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (sameDisjunction disjunction
        (star_20_02 alpha.weaken (.apparent .zero))
        (star_20_02 beta.weaken (.apparent .zero))) continuation))

/-- ✱22·3, following PM's printed `[✱20·2.(✱22·03)]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_3
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    Derivation (star_22_3_reading vocabulary disjunction finalNegation
      finalDisjunction alpha beta continuation).parsed := by
  have line1 := star_22_03_unfold vocabulary disjunction alpha beta
    continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (sameDisjunction disjunction
        (star_20_02 alpha.weaken (.apparent .zero))
        (star_20_02 beta.weaken (.apparent .zero))) continuation)
  unfold star_22_3_reading
  rw [line1]
  exact line2

/-- Audited contextual reading of ✱22·31. -/
def star_22_31_reading
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . −α = ẑx(x ∼ε α)"
  scopeReading := "Both incomplete class abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_22_04 vocabulary negation alpha continuation)
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      continuation))

/-- ✱22·31, following PM's printed `[✱20·2.(✱22·04)]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_31
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    Derivation (star_22_31_reading vocabulary negation finalNegation
      finalDisjunction alpha continuation).parsed := by
  have line1 := star_22_04_unfold vocabulary negation alpha continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      continuation)
  unfold star_22_31_reading
  rw [line1]
  exact line2

/-- Audited contextual reading of ✱22·32. -/
def star_22_32_reading
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . α − β = ẑx(x ε α . x ∼ε β)"
  scopeReading := "Both incomplete class abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_22_05 vocabulary negation disjunction alpha beta continuation)
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.neg negation (sameDisjunction disjunction
        (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
        (.neg negation (.neg negation
          (star_20_02 beta.weaken (.apparent .zero)))))) continuation))

/-- ✱22·32, following PM's printed
`[✱20·2.(✱22·05).*22·2.*20·32]` route after all four eliminable
definitions have been unfolded.
`demonstration_provenance: follows-printed`. -/
theorem star_22_32
    (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder order .individual) scopeOrder)
        (classSort order 0)))
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    Derivation (star_22_32_reading vocabulary negation disjunction
      finalNegation finalDisjunction alpha beta continuation).parsed := by
  have line1 := star_22_05_unfold vocabulary negation disjunction alpha beta
    continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_20_01 vocabulary.existential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.neg negation (sameDisjunction disjunction
        (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
        (.neg negation (.neg negation
          (star_20_02 beta.weaken (.apparent .zero)))))) continuation)
  unfold star_22_32_reading
  rw [line1]
  exact line2

/-- Audited scope reading of ✱22·1. -/
def star_22_1_reading
    (universal : signature.Universal .individual order)
    (inclusionNegation : signature.Negation order)
    (inclusionDisjunction : signature.Disjunction order)
    (equivalenceNegation : signature.Negation (bindOrder order .individual))
    (equivalenceDisjunction : signature.Disjunction (bindOrder order .individual))
    (alpha beta : Term signature real [] (classSort order 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : α ⊂ β .≡ : x ε α .⊃ₓ. x ε β"
  scopeReading := "The individual quantifier covers the pointwise membership implication."
  parsed := .assertion (star_4_01 equivalenceNegation equivalenceDisjunction
    (star_22_01 universal inclusionNegation inclusionDisjunction alpha beta)
    (.always universal
      (implication inclusionNegation inclusionDisjunction
        (star_20_02 alpha.weaken (.apparent .zero))
        (star_20_02 beta.weaken (.apparent .zero)))))

/-- ✱22·1, following PM's printed `[✱4·2.(✱22·01)]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_1
    (universal : signature.Universal .individual order)
    (inclusionNegation : signature.Negation order)
    (inclusionDisjunction : signature.Disjunction order)
    (equivalenceNegation : signature.Negation (bindOrder order .individual))
    (equivalenceDisjunction : signature.Disjunction (bindOrder order .individual))
    (alpha beta : Term signature real [] (classSort order 0)) :
    Derivation (star_22_1_reading universal inclusionNegation
      inclusionDisjunction equivalenceNegation equivalenceDisjunction alpha beta).parsed := by
  have line1 := star_22_01_unfold universal inclusionNegation
    inclusionDisjunction alpha beta
  have line2 := star_4_2 equivalenceNegation equivalenceDisjunction
    (.always universal
      (implication inclusionNegation inclusionDisjunction
        (star_20_02 alpha.weaken (.apparent .zero))
        (star_20_02 beta.weaken (.apparent .zero))))
  unfold star_22_1_reading
  rw [line1]
  exact line2

/-! ### Membership in the three elementary class operations -/

/-- The additional vocabulary carried by the ✱20·3 elimination used in
✱22·33–✱22·35. -/
structure Star22EliminationVocabulary (signature : Signature) (order : Nat)
    where
  classVocabulary : Star22ClassVocabulary signature order order
  reducibilityExistential : ExistentialVocabulary signature
    (classSort order 0) (bindOrder order .individual)
  reducibilityOuterNegation : signature.Negation
    (bindOrder (bindOrder order .individual) (classSort order 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder order .individual) (classSort order 0))
      (bindOrder (max (bindOrder order .individual) order)
        (classSort order 0)))
  finalNegation : signature.Negation
    (bindOrder (max (bindOrder order .individual) order)
      (classSort order 0))
  finalDisjunction : signature.Disjunction
    (bindOrder (max (bindOrder order .individual) order)
      (classSort order 0))

/-- The pointwise matrix defining intersection at ✱22·02. -/
def star_22_33_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    Formula signature real [.individual] order :=
  .neg negation (sameDisjunction disjunction
    (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
    (.neg negation (star_20_02 beta.weaken (.apparent .zero))))

/-- The pointwise matrix defining union at ✱22·03. -/
def star_22_34_matrix
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    Formula signature real [.individual] order :=
  sameDisjunction disjunction
    (star_20_02 alpha.weaken (.apparent .zero))
    (star_20_02 beta.weaken (.apparent .zero))

/-- The pointwise matrix defining complement at ✱22·04. -/
def star_22_35_matrix
    (negation : signature.Negation order)
    (alpha : Term signature real [] (classSort order 0)) :
    Formula signature real [.individual] order :=
  .neg negation (star_20_02 alpha.weaken (.apparent .zero))

/-- The scope transport still assumed by the ✱20·3 elimination route.  It
discharges a derivation in the context extended by a predicative class
representative into an implication from the corresponding reducibility
existential.  This is stronger than the object theorem ✱10·35. -/
def Star22Star10_35Hypothesis
    (vocabulary : Star22EliminationVocabulary signature order)
    (matrix : Formula signature real [.individual] order)
    (x : Term signature real [] .individual) : Prop :=
  Derivation (.assertion (star_20_3_transportFormula
      vocabulary.classVocabulary.universal
      vocabulary.classVocabulary.equivalenceNegation
      vocabulary.classVocabulary.equivalenceDisjunction
      vocabulary.classVocabulary.leftNegation
      vocabulary.classVocabulary.conjunctionDisjunction matrix x)) →
    Derivation (.assertion (mixedImplication vocabulary.reducibilityOuterNegation
      vocabulary.bridgeDisjunction
      (star_12_1_formula vocabulary.reducibilityExistential
        vocabulary.classVocabulary.universal
        vocabulary.classVocabulary.equivalenceNegation
        vocabulary.classVocabulary.equivalenceDisjunction matrix)
      (star_20_3_formula vocabulary.classVocabulary.existential
        vocabulary.classVocabulary.universal
        vocabulary.classVocabulary.equivalenceNegation
        vocabulary.classVocabulary.equivalenceDisjunction
        vocabulary.classVocabulary.leftNegation
        vocabulary.classVocabulary.rightNegation
        vocabulary.classVocabulary.outerNegation
        vocabulary.classVocabulary.conjunctionDisjunction matrix x)))

/-- Audited contextual reading of ✱22·33. -/
def star_22_33_reading
    (vocabulary : Star22EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (x : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : x ε α ∩ β .≡ . x ε α . x ε β"
  scopeReading := "The incomplete intersection has the scope of the displayed membership equivalence."
  parsed := .assertion (star_22_02 vocabulary.classVocabulary negation
    disjunction alpha beta
    (star_20_3_continuation
      vocabulary.classVocabulary.equivalenceNegation
      vocabulary.classVocabulary.equivalenceDisjunction
      (star_22_33_matrix negation disjunction alpha beta) x))

/-- ✱22·33, following PM's printed `[✱20·3.*22·2]` route.
`star_10_35_hypothesis` is the named reducibility-scope premise inherited
from the current conditional reconstruction of ✱20·3; it is not ✱10·35.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_22_33
    (vocabulary : Star22EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (x : Term signature real [] .individual)
    (star_10_35_hypothesis :
      Star22Star10_35Hypothesis vocabulary
        (star_22_33_matrix negation disjunction alpha beta) x) :
    Derivation (star_22_33_reading vocabulary negation disjunction alpha beta
      x).parsed := by
  let matrix := star_22_33_matrix negation disjunction alpha beta
  let continuation := star_20_3_continuation
    vocabulary.classVocabulary.equivalenceNegation
    vocabulary.classVocabulary.equivalenceDisjunction matrix x
  let target := star_22_02 vocabulary.classVocabulary negation disjunction
    alpha beta continuation
  unfold Star22Star10_35Hypothesis at star_10_35_hypothesis
  have line1 := star_20_3 vocabulary.classVocabulary.existential
    vocabulary.reducibilityExistential
    vocabulary.classVocabulary.universal
    vocabulary.classVocabulary.equivalenceNegation
    vocabulary.classVocabulary.equivalenceDisjunction
    vocabulary.classVocabulary.leftNegation
    vocabulary.classVocabulary.rightNegation
    vocabulary.classVocabulary.outerNegation
    vocabulary.classVocabulary.conjunctionDisjunction
    vocabulary.reducibilityOuterNegation vocabulary.bridgeDisjunction
    vocabulary.finalNegation vocabulary.finalDisjunction matrix x
    star_10_35_hypothesis
  change ⊢ᵣ target at line1 ⊢
  have line2 := star_22_2 vocabulary.classVocabulary negation disjunction
    vocabulary.finalNegation vocabulary.finalDisjunction alpha beta continuation
  change ⊢ᵣ star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction
    target target at line2
  have line3 := star_3_03 vocabulary.finalNegation
    vocabulary.finalDisjunction target
    (star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction target target)
    line1 line2
  exact Derivation.star_9_12_same vocabulary.finalNegation
    vocabulary.finalDisjunction line3
    (star_3_26 vocabulary.finalNegation vocabulary.finalDisjunction target
      (star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction
        target target))

/-- Audited contextual reading of ✱22·34. -/
def star_22_34_reading
    (vocabulary : Star22EliminationVocabulary signature order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (x : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : x ε α ∪ β .≡ : x ε α .∨. x ε β"
  scopeReading := "The incomplete union has the scope of the displayed membership equivalence."
  parsed := .assertion (star_22_03 vocabulary.classVocabulary disjunction
    alpha beta
    (star_20_3_continuation
      vocabulary.classVocabulary.equivalenceNegation
      vocabulary.classVocabulary.equivalenceDisjunction
      (star_22_34_matrix disjunction alpha beta) x))

/-- ✱22·34, following PM's printed `[✱20·3.*22·3]` route.
`star_10_35_hypothesis` is the named reducibility-scope premise inherited
from the current conditional reconstruction of ✱20·3; it is not ✱10·35.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_22_34
    (vocabulary : Star22EliminationVocabulary signature order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (x : Term signature real [] .individual)
    (star_10_35_hypothesis :
      Star22Star10_35Hypothesis vocabulary
        (star_22_34_matrix disjunction alpha beta) x) :
    Derivation (star_22_34_reading vocabulary disjunction alpha beta x).parsed := by
  let matrix := star_22_34_matrix disjunction alpha beta
  let continuation := star_20_3_continuation
    vocabulary.classVocabulary.equivalenceNegation
    vocabulary.classVocabulary.equivalenceDisjunction matrix x
  let target := star_22_03 vocabulary.classVocabulary disjunction alpha beta
    continuation
  unfold Star22Star10_35Hypothesis at star_10_35_hypothesis
  have line1 := star_20_3 vocabulary.classVocabulary.existential
    vocabulary.reducibilityExistential
    vocabulary.classVocabulary.universal
    vocabulary.classVocabulary.equivalenceNegation
    vocabulary.classVocabulary.equivalenceDisjunction
    vocabulary.classVocabulary.leftNegation
    vocabulary.classVocabulary.rightNegation
    vocabulary.classVocabulary.outerNegation
    vocabulary.classVocabulary.conjunctionDisjunction
    vocabulary.reducibilityOuterNegation vocabulary.bridgeDisjunction
    vocabulary.finalNegation vocabulary.finalDisjunction matrix x
    star_10_35_hypothesis
  change ⊢ᵣ target at line1 ⊢
  have line2 := star_22_3 vocabulary.classVocabulary disjunction
    vocabulary.finalNegation vocabulary.finalDisjunction alpha beta continuation
  change ⊢ᵣ star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction
    target target at line2
  have line3 := star_3_03 vocabulary.finalNegation
    vocabulary.finalDisjunction target
    (star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction target target)
    line1 line2
  exact Derivation.star_9_12_same vocabulary.finalNegation
    vocabulary.finalDisjunction line3
    (star_3_26 vocabulary.finalNegation vocabulary.finalDisjunction target
      (star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction
        target target))

/-- Audited contextual reading of ✱22·35. -/
def star_22_35_reading
    (vocabulary : Star22EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (alpha : Term signature real [] (classSort order 0))
    (x : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : x ε −α .≡ . x ∼ε α"
  scopeReading := "The incomplete complement has the scope of the displayed membership equivalence."
  parsed := .assertion
    (star_22_04 vocabulary.classVocabulary negation alpha
      (star_20_3_continuation
        vocabulary.classVocabulary.equivalenceNegation
        vocabulary.classVocabulary.equivalenceDisjunction
        (star_22_35_matrix negation alpha) x))

/-- ✱22·35, following PM's printed `[✱20·3.*22·31]` route.
`star_10_35_hypothesis` is the named reducibility-scope premise inherited
from the current conditional reconstruction of ✱20·3; it is not ✱10·35.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: follows-printed`. -/
theorem star_22_35
    (vocabulary : Star22EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (alpha : Term signature real [] (classSort order 0))
    (x : Term signature real [] .individual)
    (star_10_35_hypothesis :
      Star22Star10_35Hypothesis vocabulary
        (star_22_35_matrix negation alpha) x) :
    Derivation (star_22_35_reading vocabulary negation alpha x).parsed := by
  let matrix := star_22_35_matrix negation alpha
  let continuation := star_20_3_continuation
    vocabulary.classVocabulary.equivalenceNegation
    vocabulary.classVocabulary.equivalenceDisjunction matrix x
  let target := star_22_04 vocabulary.classVocabulary negation alpha continuation
  unfold Star22Star10_35Hypothesis at star_10_35_hypothesis
  have line1 := star_20_3 vocabulary.classVocabulary.existential
    vocabulary.reducibilityExistential
    vocabulary.classVocabulary.universal
    vocabulary.classVocabulary.equivalenceNegation
    vocabulary.classVocabulary.equivalenceDisjunction
    vocabulary.classVocabulary.leftNegation
    vocabulary.classVocabulary.rightNegation
    vocabulary.classVocabulary.outerNegation
    vocabulary.classVocabulary.conjunctionDisjunction
    vocabulary.reducibilityOuterNegation vocabulary.bridgeDisjunction
    vocabulary.finalNegation vocabulary.finalDisjunction matrix x
    star_10_35_hypothesis
  change ⊢ᵣ target at line1 ⊢
  have line2 := star_22_31 vocabulary.classVocabulary negation
    vocabulary.finalNegation vocabulary.finalDisjunction alpha continuation
  change ⊢ᵣ star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction
    target target at line2
  have line3 := star_3_03 vocabulary.finalNegation
    vocabulary.finalDisjunction target
    (star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction target target)
    line1 line2
  exact Derivation.star_9_12_same vocabulary.finalNegation
    vocabulary.finalDisjunction line3
    (star_3_26 vocabulary.finalNegation vocabulary.finalDisjunction target
      (star_4_01 vocabulary.finalNegation vocabulary.finalDisjunction
        target target))

/-- Audited scope reading of ✱22·42. -/
def star_22_42_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . α ⊂ α"
  scopeReading := "The individual variable in inclusion is universally bound."
  parsed := .assertion (star_22_01 universal negation disjunction alpha alpha)

/-- ✱22·42, following PM's printed `[Id.*10·11]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_42
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order 0)) :
    Derivation (star_22_42_reading universal negation disjunction alpha).parsed := by
  let body := star_20_02 alpha.weaken (.apparent .zero)
  let value : Term signature (.individual :: real) [] .individual :=
    .real (.zero : Var (.individual :: real) .individual)
  have line1 : Derivation (.assertion
      ((implication negation disjunction body body).weakenReal.instantiate value)) := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    exact star_2_08 negation disjunction (body.weakenReal.instantiate value)
  have line2 := Derivation.star_10_11 universal
    (implication negation disjunction body body) line1
  exact line2

/-! ### Full-scope inclusion consequences -/

/- The ✱10 rules used below act on one full-scope matrix. -/

private theorem conjunction_weakenReal
    {fresh : RSort}
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (conjunction negation disjunction left right).weakenReal (fresh := fresh) =
      conjunction negation disjunction
        (left.weakenReal (fresh := fresh))
        (right.weakenReal (fresh := fresh)) := by
  unfold conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  rfl

private theorem conjunction_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (conjunction negation disjunction left right).substitute sigma =
      conjunction negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).substitute sigma) = _
  rw [sameDisjunction_substitute]
  rfl

/-- Full-scope formula of PM's ✱10·3. -/
def star_10_3_formula
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [argument] order) :
    Formula signature real [] (bindOrder order argument) :=
  .always universal
    (implication negation disjunction
      (conjunction negation disjunction
        (implication negation disjunction phi psi)
        (implication negation disjunction psi chi))
      (implication negation disjunction phi chi))

/-- Audited full-scope reading of ✱10·3. -/
def star_10_3_reading
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [argument] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted
    "⊢ : .(x).φx⊃ψx : (x).ψx⊃χx : ⊃ .(x).φx⊃χx"
  scopeReading := "The apparent variable has the scope of the whole pointwise syllogism."
  parsed := .assertion
    (star_10_3_formula universal negation disjunction phi psi chi)

/-- ✱10·3.  In the full-scope normal form used here, PM's printed
✱10·22·221, `Syll`, ✱10·27 route reduces to pointwise `Syll` followed by
✱10·11.
`demonstration_provenance: follows-printed`. -/
theorem star_10_3
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [argument] order) :
    Derivation (star_10_3_reading universal negation disjunction
      phi psi chi).parsed := by
  let body := implication negation disjunction
    (conjunction negation disjunction
      (implication negation disjunction phi psi)
      (implication negation disjunction psi chi))
    (implication negation disjunction phi chi)
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 : ⊢ᵣ body.weakenReal.instantiate value := by
    unfold body
    rw [implication_weakenReal, conjunction_weakenReal,
      Formula.instantiate, implication_substitute, conjunction_substitute]
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    exact star_3_33 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/- The projection below is the only theorem-specific ✱10 helper retained for
✱22.  Unlike ✱10·3, it has no independently catalogued proposition name. -/
namespace Star10For22

/-- Full-scope projection used by ✱22·43. -/
def star_10_11_star_3_26_formula
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [argument] order) :
    Formula signature real [] (bindOrder order argument) :=
  .always universal
    (implication negation disjunction
      (conjunction negation disjunction phi psi) phi)

/-- PM's printed ✱3·26, ✱10·11 chain. -/
theorem star_10_11_star_3_26
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [argument] order) :
    ⊢ᵣ star_10_11_star_3_26_formula universal negation disjunction
      phi psi := by
  let body := implication negation disjunction
    (conjunction negation disjunction phi psi) phi
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 : ⊢ᵣ body.weakenReal.instantiate value := by
    unfold body
    rw [implication_weakenReal, conjunction_weakenReal,
      Formula.instantiate, implication_substitute, conjunction_substitute]
    exact star_3_26 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

end Star10For22

/-- Audited full-scope reading of ✱22·43. -/
def star_22_43_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : α ∩ β ⊂ α"
  scopeReading := "The defining individual variable has the scope of the whole pointwise projection."
  parsed := .assertion (Star10For22.star_10_11_star_3_26_formula universal
    negation disjunction
    (star_20_02 alpha.weaken (.apparent .zero))
    (star_20_02 beta.weaken (.apparent .zero)))

/-- ✱22·43, following PM's printed `[✱3·26.*10·11]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_43
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    Derivation (star_22_43_reading universal negation disjunction
      alpha beta).parsed := by
  have line1 := Star10For22.star_10_11_star_3_26 universal negation
    disjunction (star_20_02 alpha.weaken (.apparent .zero))
    (star_20_02 beta.weaken (.apparent .zero))
  exact line1

/-- Audited full-scope reading of ✱22·44. -/
def star_22_44_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta gamma : Term signature real [] (classSort order 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : α ⊂ β . β ⊂ γ .⊃ . α ⊂ γ"
  scopeReading := "The defining individual variable has the scope of the whole pointwise syllogism."
  parsed := .assertion (star_10_3_formula universal negation
    disjunction
    (star_20_02 alpha.weaken (.apparent .zero))
    (star_20_02 beta.weaken (.apparent .zero))
    (star_20_02 gamma.weaken (.apparent .zero)))

/-- ✱22·44, following PM's printed `[✱10·3]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_44
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta gamma : Term signature real [] (classSort order 0)) :
    Derivation (star_22_44_reading universal negation disjunction
      alpha beta gamma).parsed := by
  have line1 := star_10_3 universal negation disjunction
    (star_20_02 alpha.weaken (.apparent .zero))
    (star_20_02 beta.weaken (.apparent .zero))
    (star_20_02 gamma.weaken (.apparent .zero))
  exact line1

/-- Binding an individual does not raise an already positive matrix order. -/
private theorem bindOrder_succ_individual (order : Nat) :
    bindOrder (Nat.succ order) .individual = Nat.succ order := by
  cases order with
  | zero => rfl
  | succ order => rfl

/-- Inclusion at a positive order, with the computed binder order exposed. -/
private def star_22_01_successor
    (universal : signature.Universal .individual (Nat.succ order))
    (negation : signature.Negation (Nat.succ order))
    (disjunction : signature.Disjunction (Nat.succ order))
    (alpha beta : Term signature real [] (classSort (Nat.succ order) 0)) :
    Formula signature real [] (Nat.succ order) :=
  Eq.mp
    (congrArg (Formula signature real []) (bindOrder_succ_individual order))
    (star_22_01 universal negation disjunction alpha beta)

/-- Audited scope reading of ✱22·441. -/
def star_22_441_reading
    (universal : signature.Universal .individual (Nat.succ order))
    (negation : signature.Negation (Nat.succ order))
    (disjunction : signature.Disjunction (Nat.succ order))
    (alpha beta : Term signature real [] (classSort (Nat.succ order) 0))
    (x : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : α ⊂ β . x ε α .⊃ . x ε β"
  parsed := .assertion
    (implication negation disjunction
      (conjunction negation disjunction
        (star_22_01_successor universal negation disjunction alpha beta)
        (star_20_02 alpha x))
      (star_20_02 beta x))
  scopeReading := "The inclusion and antecedent membership form the antecedent of the final implication."

/-- Transport a derivation along the computed equality of two ramified
formula orders.  This is only dependent transport in Lean's metalanguage. -/
private theorem castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

/-- Transport only along literal equality of object formulae. -/
private theorem castAssertionFormula
    {left right : Formula signature real [] order}
    (equality : left = right) :
    Derivation (.assertion right) → Derivation (.assertion left) := by
  cases equality
  exact fun derivation => derivation

/-- Instantiating the displayed membership matrix restores its closed class
argument and replaces exactly the displayed individual variable. -/
private theorem star_20_02_weaken_instantiate
    (predicate : Term signature real [] (classSort resultOrder 0))
    (x : Term signature real [] .individual) :
    (star_20_02 predicate.weaken
      (.apparent (.zero : Var [.individual] .individual))).substitute
        (instantiateSubstitution x) = star_20_02 predicate x := by
  cases predicate <;> rfl

/-- The pointwise implication matrix obtained by unfolding one inclusion. -/
private def star_22_441_body
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (alpha beta : Term signature real [] (classSort resultOrder 0)) :
    Formula signature real [.individual] resultOrder :=
  implication negation disjunction
    (star_20_02 alpha.weaken (.apparent .zero))
    (star_20_02 beta.weaken (.apparent .zero))

private theorem star_22_441_body_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (alpha beta : Term signature real [] (classSort resultOrder 0))
    (x : Term signature real [] .individual) :
    (star_22_441_body negation disjunction alpha beta).instantiate x =
      implication negation disjunction
        (star_20_02 alpha x) (star_20_02 beta x) := by
  unfold star_22_441_body
  rw [Formula.instantiate, implication_substitute]
  rw [star_20_02_weaken_instantiate alpha x,
    star_20_02_weaken_instantiate beta x]

/-- Normalize the order casts forced by instantiating ✱22·01. -/
private theorem normalizeInclusionInstantiation
    {order : Nat}
    (universal : signature.Universal .individual order.succ)
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (alpha beta : Term signature real [] (classSort order.succ 0))
    (x : Term signature real [] .individual)
    (bindEq : bindOrder order.succ .individual = order.succ)
    (resultEq : max (bindOrder order.succ .individual) order.succ = order.succ)
    (line : Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) resultEq)
        (mixedImplication
          (Eq.mp (congrArg signature.Negation bindEq.symm) negation)
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          (.always universal (star_22_441_body negation disjunction alpha beta))
          ((star_22_441_body negation disjunction alpha beta).instantiate x))))) :
    ⊢ᵣ implication negation disjunction
      (star_22_01_successor universal negation disjunction alpha beta)
      ((star_22_441_body negation disjunction alpha beta).instantiate x) := by
  exact castAssertionFormula
    (by
      unfold star_22_01_successor star_22_01 star_22_441_body
      exact (mixedImplication_normalizeSameOrder bindEq rfl negation
        disjunction (.always universal
          (implication negation disjunction
            (star_20_02 alpha.weaken (.apparent .zero))
            (star_20_02 beta.weaken (.apparent .zero))))
        ((implication negation disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 beta.weaken (.apparent .zero))).instantiate x)).symm)
    line

/-- The propositional `Imp` presentation used after ✱10·1. -/
private theorem implicationPresentation
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : ⊢ᵣ implication negation disjunction p
      (implication negation disjunction q r)) :
    ⊢ᵣ implication negation disjunction
      (conjunction negation disjunction p q) r := by
  have line2 := star_3_31 negation disjunction p q r
  have line3 := Derivation.star_9_12_same negation disjunction line1 line2
  exact line3

/-- ✱22·441, following PM's printed `[✱10·1.Imp]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_441
    {order : Nat}
    (universal : signature.Universal .individual order.succ)
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (alpha beta : Term signature real [] (classSort order.succ 0))
    (x : Term signature real [] .individual) :
    Derivation (.assertion
      (implication negation disjunction
        (conjunction negation disjunction
          (star_22_01_successor universal negation disjunction alpha beta)
          (star_20_02 alpha x))
        (star_20_02 beta x))) := by
  let body := star_22_441_body negation disjunction alpha beta
  have bindEq : bindOrder order.succ .individual = order.succ := by
    exact bindOrder_succ_individual order
  have resultEq :
      max (bindOrder order.succ .individual) order.succ = order.succ :=
    natMaxCongr bindEq rfl
  have line1Raw := star_10_1 universal
    (Eq.mp (congrArg signature.Negation bindEq.symm) negation)
    (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction) body x
  have line1Cast := castAssertionOrder resultEq _ line1Raw
  have line1 : ⊢ᵣ implication negation disjunction
      (star_22_01_successor universal negation disjunction alpha beta)
      (body.instantiate x) :=
    normalizeInclusionInstantiation universal negation disjunction alpha beta x
      bindEq resultEq line1Cast
  rw [star_22_441_body_instantiate negation disjunction alpha beta x] at line1
  have line2 : Derivation (.assertion
      (implication negation disjunction
        (conjunction negation disjunction
          (star_22_01_successor universal negation disjunction alpha beta)
          (star_20_02 alpha x))
        (star_20_02 beta x))) :=
    implicationPresentation negation disjunction _ _ _ line1
  exact line2

/-- Audited scope reading of ✱22·46. -/
def star_22_46_reading
    (universal : signature.Universal .individual (Nat.succ order))
    (negation : signature.Negation (Nat.succ order))
    (disjunction : signature.Disjunction (Nat.succ order))
    (alpha beta : Term signature real [] (classSort (Nat.succ order) 0))
    (x : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : x ε α . α ⊂ β .⊃ . x ε β"
  parsed := .assertion
    (implication negation disjunction
      (conjunction negation disjunction
        (star_20_02 alpha x)
        (star_22_01_successor universal negation disjunction alpha beta))
      (star_20_02 beta x))
  scopeReading := "The membership and inclusion form the antecedent of the final implication."

/-- ✱22·46, following PM's printed `[✱22·441.Perm]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_46
    {order : Nat}
    (universal : signature.Universal .individual order.succ)
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (alpha beta : Term signature real [] (classSort order.succ 0))
    (x : Term signature real [] .individual) :
    Derivation (star_22_46_reading universal negation disjunction
      alpha beta x).parsed := by
  let inclusion := star_22_01_successor universal negation disjunction alpha beta
  let membership₁ := star_20_02 alpha x
  let membership₂ := star_20_02 beta x
  have line1 : ⊢ᵣ implication negation disjunction
      (conjunction negation disjunction inclusion membership₁) membership₂ :=
    star_22_441 universal negation disjunction alpha beta x
  have line2 := star_3_22 negation disjunction membership₁ inclusion
  have line3 := star_2_05 negation disjunction
    (conjunction negation disjunction membership₁ inclusion)
    (conjunction negation disjunction inclusion membership₁) membership₂
  have line4 := Derivation.star_9_12_same negation disjunction line1 line3
  exact Derivation.star_9_12_same negation disjunction line2 line4

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_22_441
#print axioms PM.RamifiedSyntax.star_22_46
#print axioms PM.RamifiedSyntax.star_22_42
#print axioms PM.RamifiedSyntax.star_10_3
#print axioms PM.RamifiedSyntax.Star10For22.star_10_11_star_3_26
#print axioms PM.RamifiedSyntax.star_22_43
#print axioms PM.RamifiedSyntax.star_22_44
#print axioms PM.RamifiedSyntax.star_22_1
#print axioms PM.RamifiedSyntax.star_22_2
#print axioms PM.RamifiedSyntax.star_22_3
#print axioms PM.RamifiedSyntax.star_22_31
#print axioms PM.RamifiedSyntax.star_22_32
#print axioms PM.RamifiedSyntax.star_22_33
#print axioms PM.RamifiedSyntax.star_22_34
#print axioms PM.RamifiedSyntax.star_22_35
#print axioms PM.RamifiedSyntax.star_22_01_unfold
#print axioms PM.RamifiedSyntax.star_22_02_unfold
#print axioms PM.RamifiedSyntax.star_22_03_unfold
#print axioms PM.RamifiedSyntax.star_22_04_unfold
#print axioms PM.RamifiedSyntax.star_22_05_unfold
