import Principia.FirstEdition.Volume1.Star20Source
import Principia.Syntax.Ramified
import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star10Derived
import Principia.Deduction.Star12Derived
import Principia.Deduction.Star13Derived

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱20 -/

/-- ✱20·04: comma-separated double membership is conjunction. -/
def star_20_04
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (left right : Formula signature real apparent 0) :
    Formula signature real apparent 0 :=
  mixedConjunction negation negation negation disjunction left right

theorem star_20_04_unfold
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (left right : Formula signature real apparent 0) :
    star_20_04 negation disjunction left right =
      mixedConjunction negation negation negation disjunction left right := rfl

/-- ✱20·05: comma-separated triple membership associates to the left, as
shown by PM's defining right-hand side. -/
def star_20_05
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (first second third : Formula signature real apparent 0) :
    Formula signature real apparent 0 :=
  mixedConjunction negation negation negation disjunction
    (star_20_04 negation disjunction first second) third

theorem star_20_05_unfold
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (first second third : Formula signature real apparent 0) :
    star_20_05 negation disjunction first second third =
      mixedConjunction negation negation negation disjunction
        (star_20_04 negation disjunction first second) third := rfl

/-- ✱20·06: non-membership is the negation of membership. -/
def star_20_06
    (negation : signature.Negation order)
    (membership : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation membership

theorem star_20_06_unfold
    (negation : signature.Negation order)
    (membership : Formula signature real apparent order) :
    star_20_06 negation membership = .neg negation membership := rfl

/-- ✱20·07: quantification over classes is quantification over predicative
one-place functions.  `classSort resultOrder 0` records the essential `!`. -/
def star_20_07
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (classSort resultOrder 0)) :=
  .always universal body

theorem star_20_07_unfold
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    star_20_07 universal body = .always universal body := rfl

/-- ✱20·071: existential class quantification has the same predicative
function expansion as ✱20·07. -/
def star_20_071
    (existential : ExistentialVocabulary signature (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (classSort resultOrder 0)) :=
  .sometimes existential body

theorem star_20_071_unfold
    (existential : ExistentialVocabulary signature (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    star_20_071 existential body = .sometimes existential body := rfl

/-- ✱20·081: membership of a class argument in a predicative class
function is application, exactly as ✱20·02. -/
def star_20_081
    (predicate : Term signature real apparent
      (.function [classSort argumentOrder 0] resultOrder 0))
    (argument : Term signature real apparent (classSort argumentOrder 0)) :
    Formula signature real apparent resultOrder :=
  applyUnary predicate argument

theorem star_20_081_unfold
    (predicate : Term signature real apparent
      (.function [classSort argumentOrder 0] resultOrder 0))
    (argument : Term signature real apparent (classSort argumentOrder 0)) :
    star_20_081 predicate argument = applyUnary predicate argument := rfl

/-- Audited catalogue reading of ✱20·1.  The apparent class on the left is
eliminated by ✱20·01, so both sides parse as the same existential expansion. -/
def star_20_1_reading
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (matrix : Formula signature real (.individual :: []) resultOrder)
    (continuation : Formula signature real
      (classSort resultOrder 0 :: []) scopeOrder) :
    ClaimReading signature real where
  printed := "⊢ : f{ẑ(ψz)} .≡ : (∃φ) : φ!x .≡ₓ. ψx : f{φ!ẑ}"
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_20_01 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
    (star_20_01 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation))

/-- ✱20·1, following PM's two printed citations: unfold ✱20·01, then use
✱4·2 on the resulting formula.  The predicative `!` is the zero excess in
`classSort resultOrder 0`.
`demonstration_provenance: follows-printed`. -/
theorem star_20_1
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)))
    (matrix : Formula signature real [.individual] resultOrder)
    (continuation : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Derivation (star_20_1_reading existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction finalNegation finalDisjunction matrix
      continuation).parsed := by
  have line1 := star_20_01_unfold existential universal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction matrix continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_20_01 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
  rw [line1] at line2
  exact line2

/-! ## The eliminative theorem ✱20·3

`star_10_35` is not yet exported by `Star10Derived`.  The theorem below
therefore exposes its one required, fully specialized use as the named local
hypothesis `star_10_35_hypothesis`.  Its two inputs are exactly the preceding
printed ✱10·43 transport and the final ✱12·1 reducibility assertion; it is not
an assumption of the conclusion itself.
-/

/-- The predicative function matrix used when ✱10·43 specializes the
pointwise equivalence at `x`. -/
def star_20_3_predicateMatrix
    (_matrix : Formula signature real [.individual] resultOrder) :
    Formula signature (classSort resultOrder 0 :: real) [.individual]
      resultOrder :=
  applyUnary
    (.real (.zero : Var (classSort resultOrder 0 :: real)
      (classSort resultOrder 0)))
    (.apparent .zero)

/-- The exact ✱10·43 instance occurring on PM's third displayed line in the
proof of ✱20·3. -/
def star_20_3_transportFormula
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (outerNegation : signature.Negation
      (bindOrder resultOrder .individual))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) resultOrder))
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    Formula signature (classSort resultOrder 0 :: real) []
      (max (bindOrder resultOrder .individual) resultOrder) :=
  mixedImplication outerNegation outerDisjunction
    (.always universal
      (equivalence equivalenceNegation equivalenceDisjunction
        (star_20_3_predicateMatrix matrix) matrix.weakenReal))
    ((equivalence equivalenceNegation equivalenceDisjunction
      (star_20_3_predicateMatrix matrix) matrix.weakenReal).instantiate
        x.weakenReal)

/-- The continuation obtained from the membership definition ✱20·02.  Since
class abstraction is contextual, this continuation is part of the expansion
of the whole displayed equivalence. -/
def star_20_3_continuation
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    Formula signature real [classSort resultOrder 0] resultOrder :=
  equivalence equivalenceNegation equivalenceDisjunction
    (star_20_02 (.apparent .zero) x.weaken)
    ((matrix.instantiate x).rename
      (emptyRenaming (target := [classSort resultOrder 0])))

/-- Object formula of ✱20·3 after the contextual definition ✱20·01. -/
def star_20_3_formula
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) resultOrder))
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
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    Formula signature real []
      (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
        (classSort resultOrder 0)) :=
  star_20_01 existential universal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction matrix
    (star_20_3_continuation equivalenceNegation equivalenceDisjunction
      matrix x)

/-- Audited catalogue reading of ✱20·3. -/
def star_20_3_reading
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) resultOrder))
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
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual) :
    ClaimReading signature real where
  printed := "✱20·3. ⊢ : x ε ẑ(ψz) .≡ . ψx"
  parsed := .assertion (star_20_3_formula existential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix x)

/-- ✱20·3, following the printed ✱20·1·02, ✱10·43·35, ✱12·1 chain.

`star_10_35_hypothesis` is explicit because ✱10·35 is not yet present in
`Star10Derived.lean`.  `direct_assumptions: PM1:REDUCIBILITY` records the
non-logical assumption reached through ✱12·1.
`demonstration_provenance: follows-printed`. -/
theorem star_20_3
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
    (finalNegation : signature.Negation
      (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
        (classSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
        (classSort resultOrder 0)))
    (matrix : Formula signature real [.individual] resultOrder)
    (x : Term signature real [] .individual)
    (star_10_35_hypothesis :
      (⊢ᵣ star_20_3_transportFormula universal equivalenceNegation
        equivalenceDisjunction leftNegation conjunctionDisjunction matrix x) →
      ⊢ᵣ mixedImplication reducibilityOuterNegation bridgeDisjunction
        (star_12_1_formula reducibilityExistential universal
          equivalenceNegation equivalenceDisjunction matrix)
        (star_20_3_formula abstractionExistential universal
          equivalenceNegation equivalenceDisjunction leftNegation rightNegation
          outerNegation conjunctionDisjunction matrix x)) :
    Derivation (star_20_3_reading abstractionExistential universal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x).parsed := by
  have definitionUnfold := star_20_01_unfold abstractionExistential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix
    (star_20_3_continuation equivalenceNegation equivalenceDisjunction
      matrix x)
  have line1 := star_20_1 abstractionExistential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction finalNegation finalDisjunction
    matrix (star_20_3_continuation equivalenceNegation
      equivalenceDisjunction matrix x)
  have line2 := star_20_02_unfold
    (.apparent (.zero : Var [classSort resultOrder 0]
      (classSort resultOrder 0))) x.weaken
  have line3 := star_10_43 universal equivalenceNegation
    equivalenceDisjunction leftNegation conjunctionDisjunction
    (star_20_3_predicateMatrix matrix) matrix.weakenReal x.weakenReal
  have line4 := star_10_35_hypothesis line3
  have line5 := star_12_1 reducibilityExistential universal
    equivalenceNegation equivalenceDisjunction matrix
  have line6 := Derivation.star_9_12 reducibilityOuterNegation
    bridgeDisjunction line5 line4
  change ⊢ᵣ star_20_3_formula abstractionExistential universal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix x at line6 ⊢
  change ⊢ᵣ star_4_01 finalNegation finalDisjunction
    (star_20_3_formula abstractionExistential universal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x)
    (star_20_3_formula abstractionExistential universal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction matrix x) at line1
  unfold star_20_3_formula at line1 line6 ⊢
  rw [definitionUnfold] at line1 line6 ⊢
  unfold star_20_3_continuation at line1 line6 ⊢
  rw [line2] at line1 line6 ⊢
  let target := Formula.sometimes abstractionExistential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      (equivalence equivalenceNegation equivalenceDisjunction
        (applyUnary (.apparent .zero) x.weaken)
        ((matrix.instantiate x).rename
          (emptyRenaming (target := [classSort resultOrder 0])))))
  change ⊢ᵣ target at line6 ⊢
  change ⊢ᵣ star_4_01 finalNegation finalDisjunction target target at line1
  have line7 : ⊢ᵣ implication finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target)
      (implication finalNegation finalDisjunction target
        (conjunction finalNegation finalDisjunction
          (star_4_01 finalNegation finalDisjunction target target) target)) :=
    star_3_2 finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target) target
  have line8 : ⊢ᵣ implication finalNegation finalDisjunction target
      (conjunction finalNegation finalDisjunction
        (star_4_01 finalNegation finalDisjunction target target) target) :=
    Derivation.star_9_12_same finalNegation finalDisjunction line1 line7
  have line9 : ⊢ᵣ conjunction finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target) target :=
    Derivation.star_9_12_same finalNegation finalDisjunction line6 line8
  exact Derivation.star_9_12_same finalNegation finalDisjunction line9
    (star_3_27 finalNegation finalDisjunction
      (star_4_01 finalNegation finalDisjunction target target) target)

/-- Audited catalogue reading of ✱20·6. -/
def star_20_6_reading
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (body : Formula signature real [classSort resultOrder 0] matrixOrder) :
    ClaimReading signature real where
  printed := "⊢ : (∃α) . fα .≡ . ∼{(α) . ∼fα}"
  parsed := .assertion (star_4_01 equivalenceNegation equivalenceDisjunction
    (star_20_071 existential body)
    (.neg existential.outerNegation
      (star_20_07 existential.universal
        (.neg existential.matrixNegation body))))

/-- ✱20·6, following PM's printed ✱4·2, ✱10·01, ✱20·07 chain.
`demonstration_provenance: follows-printed`. -/
theorem star_20_6
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (classSort resultOrder 0)))
    (body : Formula signature real [classSort resultOrder 0] matrixOrder) :
    Derivation (star_20_6_reading existential equivalenceNegation
      equivalenceDisjunction body).parsed := by
  have line1 := star_4_2 equivalenceNegation equivalenceDisjunction
    (star_20_071 existential body)
  have line2 : star_20_071 existential body =
      .neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation body)) :=
    star_10_01_unfold existential body
  have line3 := star_20_07_unfold existential.universal
    (.neg existential.matrixNegation body)
  exact Derivation.castAssertion
    (congrArg
      (star_4_01 equivalenceNegation equivalenceDisjunction
        (star_20_071 existential body))
      (Eq.trans line2
        (congrArg
          (fun formula => Formula.neg existential.outerNegation formula)
          line3).symm))
    line1

/-- Audited catalogue reading of ✱20·34.  The class variable is exactly the
predicative unary-function variable quantified in Leibniz identity ✱13·01. -/
def star_20_34_reading
    (vocabulary : IdentityVocabulary signature .individual order 0)
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (x y : Term signature real [] .individual) :
    ClaimReading signature real where
  printed := "⊢ : x = y .≡ : x ∈ α .⊃ₐ. y ∈ α"
  parsed := .assertion (star_4_01 equivalenceNegation
    equivalenceDisjunction
    (star_13_01 vocabulary x y)
    (star_20_07 vocabulary.universal
      (implication vocabulary.negation vocabulary.disjunction
        (star_20_02 (.apparent .zero) x.weaken)
        (star_20_02 (.apparent .zero) y.weaken))))

/-- ✱20·34.  PM prints no proof; unfolding ✱13·01, ✱20·07 and ✱20·02
gives the same object formula on both sides.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_20_34
    (vocabulary : IdentityVocabulary signature .individual order 0)
    (equivalenceNegation : signature.Negation
      (bindOrder order (classSort order 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (classSort order 0)))
    (x y : Term signature real [] .individual) :
    Derivation (star_20_34_reading vocabulary equivalenceNegation
      equivalenceDisjunction x y).parsed := by
  have line1 := star_4_2 equivalenceNegation equivalenceDisjunction
    (star_13_01 vocabulary x y)
  exact line1

/-- Audited catalogue reading of ✱20·61. -/
def star_20_61_reading
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (classSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [classSort resultOrder 0] scopeOrder)
    (beta : Term signature real [] (classSort resultOrder 0)) :
    ClaimReading signature real where
  printed := "⊢ : (α) . fα .⊃ . fβ"
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal body) (body.instantiate beta))

/-- ✱20·61, by the printed use of universal instantiation ✱10·1.
`demonstration_provenance: follows-printed`. -/
theorem star_20_61
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (classSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [classSort resultOrder 0] scopeOrder)
    (beta : Term signature real [] (classSort resultOrder 0)) :
    Derivation
      (star_20_61_reading universal negation disjunction body beta).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction body beta
  exact line1

/-- Audited catalogue reading of the metalinguistic rule ✱20·62. -/
def star_20_62_reading
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "When fβ is true, whatever possible argument of the form ẑ(φ!z) β may be, then (α). fα is true."
  parsed := .assertion (.always universal body)

/-- ✱20·62, following the printed application of the rule ✱10·11.
The premise is legitimate because PM states ✱20·62 as a rule, not with `⊢`.
`demonstration_provenance: follows-printed`. -/
theorem star_20_62
    (universal : signature.Universal (classSort resultOrder 0) scopeOrder)
    (body : Formula signature real [classSort resultOrder 0] scopeOrder)
    (line1 : Derivation (.assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (classSort resultOrder 0 :: real)
          (classSort resultOrder 0)))))) :
    Derivation (star_20_62_reading universal body).parsed := by
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/-- Audited catalogue reading of ✱20·63. -/
def star_20_63_reading
    (universal : signature.Universal (classSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (classSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [classSort resultOrder 0] 0) :
    ClaimReading signature real where
  printed := "⊢ : (α). p ∨ fα .⊃ : p .∨ . (α). fα"
  parsed := .assertion (implication negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body))
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body)))

/-- ✱20·63, following PM's printed reduction through ✱20·07 to ✱10·12.
`demonstration_provenance: follows-printed`. -/
theorem star_20_63
    (universal : signature.Universal (classSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (classSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (classSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [classSort resultOrder 0] 0) :
    Derivation (star_20_63_reading universal matrixDisjunction negation
      disjunction p body).parsed := by
  have line1 := star_10_12 universal matrixDisjunction negation disjunction p body
  exact line1

/-- Audited catalogue reading of ✱20·631. -/
def star_20_631_reading
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "If \"fα\" is significant, then if β is of the same type as α, \"fβ\" is significant, and vice versa."
  parsed := .significance body

/-- ✱20·631, following PM's reduction to ✱10·121.
`demonstration_provenance: follows-printed`. -/
theorem star_20_631
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Derivation (star_20_631_reading body).parsed := by
  have line1 := Derivation.star_10_121 body
  exact line1

/-- Audited catalogue reading of ✱20·632. -/
def star_20_632_reading
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "If, for some α, there is a proposition fα, then there is a function fα̂, and vice versa."
  parsed := .functionExistence body

/-- ✱20·632, following PM's reduction to ✱10·122.
`demonstration_provenance: follows-printed`. -/
theorem star_20_632
    (body : Formula signature real [classSort resultOrder 0] scopeOrder) :
    Derivation (star_20_632_reading body).parsed := by
  have line1 := Derivation.star_10_122 body
  exact line1

/-- Audited catalogue reading of ✱20·633. -/
def star_20_633_reading
    (leftInner : signature.Universal (classSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (classSort rightOrder 0)
      (bindOrder matrixOrder (classSort leftOrder 0)))
    (rightInner : signature.Universal (classSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (classSort leftOrder 0)
      (bindOrder matrixOrder (classSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
        (classSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
          (classSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (classSort rightOrder 0))
          (classSort leftOrder 0))))
    (body : Formula signature real
      [classSort leftOrder 0, classSort rightOrder 0] matrixOrder) :
    ClaimReading signature real where
  printed := "\"Whatever possible class α may be, f(α,β) is true whatever possible class β may be\" implies the corresponding statement with α and β interchanged except in \"f(α,β)\"."
  parsed := .assertion (star_11_07_formula leftInner rightOuter rightInner
    leftOuter negation disjunction body)

/-- ✱20·633, reconstructed as the class-sorted instance of ✱11·07.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_20_633
    (leftInner : signature.Universal (classSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (classSort rightOrder 0)
      (bindOrder matrixOrder (classSort leftOrder 0)))
    (rightInner : signature.Universal (classSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (classSort leftOrder 0)
      (bindOrder matrixOrder (classSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
        (classSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (classSort leftOrder 0))
          (classSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (classSort rightOrder 0))
          (classSort leftOrder 0))))
    (body : Formula signature real
      [classSort leftOrder 0, classSort rightOrder 0] matrixOrder) :
    Derivation (star_20_633_reading leftInner rightOuter rightInner leftOuter
      negation disjunction body).parsed := by
  have line1 := Derivation.star_11_07 leftInner rightOuter rightInner leftOuter
    negation disjunction body
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_20_61
#print axioms PM.RamifiedSyntax.star_20_62
#print axioms PM.RamifiedSyntax.star_20_63
#print axioms PM.RamifiedSyntax.star_20_631
#print axioms PM.RamifiedSyntax.star_20_632
#print axioms PM.RamifiedSyntax.star_20_633
#print axioms PM.RamifiedSyntax.star_20_1
#print axioms PM.RamifiedSyntax.star_20_3
#print axioms PM.RamifiedSyntax.star_20_6
#print axioms PM.RamifiedSyntax.star_20_34
#print axioms PM.RamifiedSyntax.star_20_04_unfold
#print axioms PM.RamifiedSyntax.star_20_05_unfold
#print axioms PM.RamifiedSyntax.star_20_06_unfold
#print axioms PM.RamifiedSyntax.star_20_07_unfold
#print axioms PM.RamifiedSyntax.star_20_071_unfold
#print axioms PM.RamifiedSyntax.star_20_081_unfold
