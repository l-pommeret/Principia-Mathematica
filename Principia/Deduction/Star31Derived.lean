import Principia.Deduction.Star21Derived
import Principia.FirstEdition.Volume1.Star31Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱31

`Cnv` and `P̌` are incomplete symbols.  ✱31·02 is a relation abstraction over
two individuals, so it is exactly the contextual `star_21_01` of the ramified
syntax and is reconstructed below with its `rfl` unfolding.  ✱31·01 binds two
*relation* arguments and needs the two-sorted abstraction instead.

The elimination that PM cites for ✱31·1 and ✱31·11 is ✱21·3, and `star_21_3`
is not unconditional: after ✱12·11 the derivation reaches
`.sometimes reducibilityExistential (binaryReducibilityMatrix …)` whereas the
abstraction it must reach is
`.sometimes abstractionExistential (mixedConjunction … (.always …) continuation)`.
The two existential vocabularies live at different orders and the two bodies do
not reduce to one another, so the ✱10·35 transport PM uses is missing.  ✱31·11
is therefore stated here with that one premise carried through under the name
`star_31_11_hypothesis`; nothing else is assumed, and no formula is weakened.

✱31·12 (`P̌ = CnvʻP`) and everything that rests on it — ✱31·13, ✱31·131,
✱31·132, ✱31·14, ✱31·15, ✱31·16, ✱31·17, ✱31·18 — additionally require the
descriptive-function identity ✱30·3, which `Star30Derived` leaves underived:
its printed step ✱14·202 goes through ✱13·195.  ✱13·195 is now proved
unconditionally, so what blocks this cascade is ✱14·202 alone, which
`Star14Derived` does not yet declare.
-/

/-- The matrix `yPx` printed at ✱31·02.  Under the ✱21·01 binders the head
apparent variable is the first argument `x` of the abstraction and the next one
is `y`, so the converse applies `P` to them in the reverse order. -/
def star_31_02_matrix
    (relation : Term signature real apparent
      (.function [.individual, .individual] resultOrder excess)) :
    Formula signature real
      (.individual :: .individual :: apparent) resultOrder :=
  applyBinary
    (relation.weaken.weaken :
      Term signature real (.individual :: .individual :: apparent)
        (.function [.individual, .individual] resultOrder excess))
    (.apparent (.succ .zero)) (.apparent .zero)

theorem star_31_02_matrix_unfold
    (relation : Term signature real apparent
      (.function [.individual, .individual] resultOrder excess)) :
    star_31_02_matrix relation =
      applyBinary
        (relation.weaken.weaken :
          Term signature real (.individual :: .individual :: apparent)
            (.function [.individual, .individual] resultOrder excess))
        (.apparent (.succ .zero)) (.apparent .zero) := rfl

/-- ✱31·02: `P̌ = x̂ŷ(yPx)` Df.  The converse is an incomplete symbol, so what
the definition licenses is the ✱21·01 contextual scope of the relation
abstraction whose matrix is `yPx`; no converse-valued `Term` is introduced. -/
def star_31_02
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (relation : Term signature real apparent
      (.function [.individual, .individual] resultOrder excess))
    (continuation : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)) :=
  star_21_01 existential leftUniversal rightUniversal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction (star_31_02_matrix relation) continuation

theorem star_31_02_unfold
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (relation : Term signature real apparent
      (.function [.individual, .individual] resultOrder excess))
    (continuation : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    star_31_02 existential leftUniversal rightUniversal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction relation continuation =
      star_21_01 existential leftUniversal rightUniversal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction (star_31_02_matrix relation) continuation := rfl

/-- The vocabulary ✱21·3 already requires, gathered so that the ✱31·11
statement stays readable.  It adds no object rule. -/
structure Star31ConverseVocabulary (signature : Signature)
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
    (bindOrder (bindOrder (bindOrder resultOrder .individual) .individual)
      (relationSort resultOrder 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder (bindOrder resultOrder .individual) .individual)
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

/-- Object formula of ✱31·11 once ✱31·02 and ✱21·01 are eliminated: exactly the
✱21·3 formula at the converse matrix `yPx`. -/
def star_31_11_formula
    (vocabulary : Star31ConverseVocabulary signature resultOrder)
    (relation : Term signature real []
      (.function [.individual, .individual] resultOrder excess))
    (x y : Term signature real [] .individual) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          resultOrder)
        (relationSort resultOrder 0)) :=
  star_21_3_formula vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction (star_31_02_matrix relation) x y

theorem star_31_11_formula_unfold
    (vocabulary : Star31ConverseVocabulary signature resultOrder)
    (relation : Term signature real []
      (.function [.individual, .individual] resultOrder excess))
    (x y : Term signature real [] .individual) :
    star_31_11_formula vocabulary relation x y =
      star_21_3_formula vocabulary.abstractionExistential
        vocabulary.leftUniversal vocabulary.rightUniversal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (star_31_02_matrix relation) x y := rfl

/-- Audited scope reading of ✱31·11.  The abstraction of ✱31·02 keeps the whole
printed equivalence as its scope, exactly as ✱21·3 requires. -/
def star_31_11_reading
    (vocabulary : Star31ConverseVocabulary signature resultOrder)
    (relation : Term signature real []
      (.function [.individual, .individual] resultOrder excess))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱31·11. ⊢ : xP̌y ≡ . yPx [✱21·3.(✱31·02)]"
  parsed := .assertion (star_31_11_formula vocabulary relation x y)
  scopeReading := "`P̌` is eliminated by ✱31·02; the relation abstraction of ✱21·01 has the whole printed equivalence as its scope, and its matrix is the converse application `yPx`."

/-- The one premise ✱21·3 still needs, restated at the converse matrix of
✱31·02.  It is PM's ✱10·35 step from the reducibility existential of ✱12·11 to
the abstraction existential of ✱21·01; the two `.sometimes` heads carry
different vocabularies and different bodies, so no unfolding supplies it. -/
def Star31_11Hypothesis
    (vocabulary : Star31ConverseVocabulary signature resultOrder)
    (relation : Term signature real []
      (.function [.individual, .individual] resultOrder excess))
    (x y : Term signature real [] .individual) : Prop :=
  (⊢ᵣ star_21_3_transportFormula vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.conjunctionDisjunction (star_31_02_matrix relation) x y) →
  ⊢ᵣ mixedImplication vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction
    (star_12_11_formula vocabulary.reducibilityExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      (star_31_02_matrix relation))
    (star_31_11_formula vocabulary relation x y)

/-- ✱31·11, by the printed route `[✱21·3.(✱31·02)]`.  The single premise
`star_31_11_hypothesis` is ✱21·3's own missing ✱10·35 transport, inherited and
not added: nothing is assumed about the converse beyond it.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_31_11
    (vocabulary : Star31ConverseVocabulary signature resultOrder)
    (relation : Term signature real []
      (.function [.individual, .individual] resultOrder excess))
    (x y : Term signature real [] .individual)
    (star_31_11_hypothesis : Star31_11Hypothesis vocabulary relation x y) :
    Derivation (star_31_11_reading vocabulary relation x y).parsed := by
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction (star_31_02_matrix relation) x y
    star_31_11_hypothesis
  exact line1

/-! ## The two-sorted form of ✱21·01 and of its elimination ✱21·3

`star_21_01` and `star_21_3` fix both abstracted arguments to `.individual`,
because that is how ✱21 prints them.  ✱31·01 abstracts two *relations* and
✱32·01 abstracts a class and an individual, so both need the same construction
with its two argument sorts left open.  What follows is that construction with
`.individual` replaced by the two sort parameters; the primitives it consumes,
✱11·1 and ✱12·11, are already generic in their argument sorts.  The premise
`SortedEliminationHypothesis` is the same missing ✱10·35 transport as in
`star_21_3`, restated at those sorts. -/

/-- ✱21·01 with its two argument sorts left open. -/
def twoSortedAbstraction
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

theorem twoSortedAbstraction_unfold
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
    twoSortedAbstraction existential leftUniversal rightUniversal
        equivalenceNegation equivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction matrix continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          ((equivalence equivalenceNegation equivalenceDisjunction
            (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
              (.apparent (.succ .zero)))
            (matrix.rename (liftRenamingN [leftSort, rightSort]
              (fun v => .succ v)))).always₂ leftUniversal rightUniversal)
          continuation) := rfl

/-- The application of the abstracted predicative function to the two bound
arguments, at the sorts left open. -/
def twoSortedFunctionMatrix
    (_matrix : Formula signature real [leftSort, rightSort] resultOrder) :
    Formula signature
      (.function [leftSort, rightSort] resultOrder 0 :: real)
      [leftSort, rightSort] resultOrder :=
  applyBinary
    (.real (.zero : Var
      (.function [leftSort, rightSort] resultOrder 0 :: real)
      (.function [leftSort, rightSort] resultOrder 0)))
    (.apparent .zero) (.apparent (.succ .zero))

/-- PM's ✱10·43 line of ✱21·3, taken at two open sorts.  The ramified API
exposes this simultaneous two-variable specialization as ✱11·1. -/
def twoSortedTransport
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
      (twoSortedFunctionMatrix matrix) matrix.weakenReal)
    left.weakenReal right.weakenReal

/-- The continuation obtained from the eliminable application definition
✱21·02, at two open sorts. -/
def twoSortedContinuation
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

/-- Object formula of the two-sorted ✱21·3. -/
def twoSortedEliminationFormula
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
    (right : Term signature real [] rightSort) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (bindOrder resultOrder leftSort) rightSort) resultOrder)
        (.function [leftSort, rightSort] resultOrder 0)) :=
  twoSortedAbstraction existential leftUniversal rightUniversal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix
    (twoSortedContinuation equivalenceNegation equivalenceDisjunction
      matrix left right)

/-- The vocabulary the two-sorted elimination needs.  It adds no object rule. -/
structure TwoSortedEliminationVocabulary (signature : Signature)
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

/-- The one premise the two-sorted ✱21·3 still needs: PM's ✱10·35 step from the
reducibility existential of ✱12·11 to the abstraction existential of ✱21·01.
The two `.sometimes` heads carry different vocabularies, at different orders,
over different bodies, so no unfolding supplies it. -/
def SortedEliminationHypothesis
    (vocabulary : TwoSortedEliminationVocabulary signature leftSort rightSort
      resultOrder)
    (matrix : Formula signature real [leftSort, rightSort] resultOrder)
    (left : Term signature real [] leftSort)
    (right : Term signature real [] rightSort) : Prop :=
  (⊢ᵣ twoSortedTransport vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.conjunctionDisjunction matrix left
    right) →
  ⊢ᵣ mixedImplication vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction
    (star_12_11_formula vocabulary.reducibilityExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction matrix)
    (twoSortedEliminationFormula vocabulary.abstractionExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      matrix left right)

/-- ✱21·3 at two open argument sorts, on PM's printed route ✱11·1, ✱12·11 and
✱9·12, with the same single missing ✱10·35 transport carried through.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem twoSortedElimination
    (vocabulary : TwoSortedEliminationVocabulary signature leftSort rightSort
      resultOrder)
    (matrix : Formula signature real [leftSort, rightSort] resultOrder)
    (left : Term signature real [] leftSort)
    (right : Term signature real [] rightSort)
    (star_10_35_hypothesis : SortedEliminationHypothesis vocabulary matrix
      left right) :
    ⊢ᵣ twoSortedEliminationFormula vocabulary.abstractionExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      matrix left right := by
  have line1 := star_11_1 vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.leftNegation vocabulary.conjunctionDisjunction
    (equivalence vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction
      (twoSortedFunctionMatrix matrix) matrix.weakenReal)
    left.weakenReal right.weakenReal
  have line2 := star_10_35_hypothesis line1
  have line3 := star_12_11 vocabulary.reducibilityExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction matrix
  have line4 := Derivation.star_9_12 vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction line3 line2
  exact line4

/-! ## ✱31·01 and ✱31·1 -/

/-- The matrix `xQy .≡ₓ,ᵧ. yPx` printed at ✱31·01.  Under the ✱21·01 binders
the head apparent variable is `Q` and the next one is `P`; the two individual
variables `x` and `y` are bound by the printed double universal. -/
def star_31_01_matrix
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder) :
    Formula signature real
      (relationSort resultOrder 0 :: relationSort resultOrder 0 :: apparent)
      (bindOrder (bindOrder resultOrder .individual) .individual) :=
  (equivalence equivalenceNegation equivalenceDisjunction
    (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
      (.apparent (.succ .zero)))
    (applyBinary (.apparent (.succ (.succ (.succ .zero))))
      (.apparent (.succ .zero)) (.apparent .zero))).always₂
    leftUniversal rightUniversal

theorem star_31_01_matrix_unfold {signature : Signature}
    {real apparent : Context} {resultOrder : Nat}
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder) :
    star_31_01_matrix (real := real) (apparent := apparent) leftUniversal
        rightUniversal equivalenceNegation equivalenceDisjunction =
      (equivalence equivalenceNegation equivalenceDisjunction
        (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
          (.apparent (.succ .zero)))
        (applyBinary (.apparent (.succ (.succ (.succ .zero))))
          (.apparent (.succ .zero)) (.apparent .zero))).always₂
        leftUniversal rightUniversal := rfl

/-- The order of the matrix printed inside ✱31·01: two individual variables
are bound in it. -/
abbrev star_31_01_matrixOrder (resultOrder : Nat) : Nat :=
  bindOrder (bindOrder resultOrder .individual) .individual

/-- ✱31·01: `Cnv = Q̂P̂{xQy ≡ₓ,ᵧ yPx}` Df.  `Cnv` is an incomplete symbol whose
two abstracted arguments are relations, so the definition is the two-sorted
✱21·01 scope at the matrix printed above. -/
def star_31_01
    (existential : ExistentialVocabulary signature
      (.function [relationSort resultOrder 0, relationSort resultOrder 0]
        (star_31_01_matrixOrder resultOrder) 0)
      (max (bindOrder (bindOrder (star_31_01_matrixOrder resultOrder)
          (relationSort resultOrder 0)) (relationSort resultOrder 0))
        scopeOrder))
    (abstractionLeftUniversal : signature.Universal
      (relationSort resultOrder 0) (star_31_01_matrixOrder resultOrder))
    (abstractionRightUniversal : signature.Universal
      (relationSort resultOrder 0)
      (bindOrder (star_31_01_matrixOrder resultOrder)
        (relationSort resultOrder 0)))
    (abstractionEquivalenceNegation : signature.Negation
      (star_31_01_matrixOrder resultOrder))
    (abstractionEquivalenceDisjunction : signature.Disjunction
      (star_31_01_matrixOrder resultOrder))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder (star_31_01_matrixOrder resultOrder)
        (relationSort resultOrder 0)) (relationSort resultOrder 0)))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder (star_31_01_matrixOrder resultOrder)
          (relationSort resultOrder 0)) (relationSort resultOrder 0))
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder (star_31_01_matrixOrder resultOrder)
          (relationSort resultOrder 0)) (relationSort resultOrder 0))
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (continuation : Formula signature real
      (.function [relationSort resultOrder 0, relationSort resultOrder 0]
        (star_31_01_matrixOrder resultOrder) 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max (bindOrder (bindOrder (star_31_01_matrixOrder resultOrder)
            (relationSort resultOrder 0)) (relationSort resultOrder 0))
          scopeOrder)
        (.function [relationSort resultOrder 0, relationSort resultOrder 0]
          (star_31_01_matrixOrder resultOrder) 0)) :=
  twoSortedAbstraction existential abstractionLeftUniversal
    abstractionRightUniversal abstractionEquivalenceNegation
    abstractionEquivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction
    (star_31_01_matrix leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction)
    continuation

/-- Object formula of ✱31·1 once ✱31·01 and ✱21·01 are eliminated: the
two-sorted ✱21·3 at the matrix `xQy .≡ₓ,ᵧ. yPx`, both abstracted arguments
being of relation sort. -/
def star_31_1_formula
    (vocabulary : TwoSortedEliminationVocabulary signature
      (relationSort resultOrder 0) (relationSort resultOrder 0)
      (star_31_01_matrixOrder resultOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (converse direct : Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (bindOrder (star_31_01_matrixOrder resultOrder)
            (relationSort resultOrder 0)) (relationSort resultOrder 0))
          (star_31_01_matrixOrder resultOrder))
        (.function [relationSort resultOrder 0, relationSort resultOrder 0]
          (star_31_01_matrixOrder resultOrder) 0)) :=
  twoSortedEliminationFormula vocabulary.abstractionExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_31_01_matrix leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction)
    converse direct

/-- Audited scope reading of ✱31·1. -/
def star_31_1_reading
    (vocabulary : TwoSortedEliminationVocabulary signature
      (relationSort resultOrder 0) (relationSort resultOrder 0)
      (star_31_01_matrixOrder resultOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (converse direct : Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱31·1. ⊢ : Q Cnv P ≡ : xQy ≡ₓ,ᵧ yPx [✱21·3.(✱31·01)]"
  parsed := .assertion (star_31_1_formula vocabulary leftUniversal
    rightUniversal equivalenceNegation equivalenceDisjunction converse direct)
  scopeReading := "`Cnv` is eliminated by ✱31·01; the two-relation abstraction of ✱21·01 has the whole printed equivalence as its scope, and its matrix is the printed double universal `xQy .≡ₓ,ᵧ. yPx`."

/-- ✱31·1, by the printed route `[✱21·3.(✱31·01)]` at the two relation sorts.
The single premise `star_31_1_hypothesis` is ✱21·3's own missing ✱10·35
transport, inherited and not added.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_31_1
    (vocabulary : TwoSortedEliminationVocabulary signature
      (relationSort resultOrder 0) (relationSort resultOrder 0)
      (star_31_01_matrixOrder resultOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (converse direct : Term signature real [] (relationSort resultOrder 0))
    (star_31_1_hypothesis : SortedEliminationHypothesis vocabulary
      (star_31_01_matrix leftUniversal rightUniversal equivalenceNegation
        equivalenceDisjunction) converse direct) :
    Derivation (star_31_1_reading vocabulary leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction converse direct).parsed := by
  have line1 := twoSortedElimination vocabulary
    (star_31_01_matrix leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction) converse direct star_31_1_hypothesis
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_31_02_matrix_unfold
#print axioms PM.RamifiedSyntax.star_31_02_unfold
#print axioms PM.RamifiedSyntax.star_31_11_formula_unfold
#print axioms PM.RamifiedSyntax.star_31_11
#print axioms PM.RamifiedSyntax.twoSortedAbstraction_unfold
#print axioms PM.RamifiedSyntax.twoSortedElimination
#print axioms PM.RamifiedSyntax.star_31_01_matrix_unfold
#print axioms PM.RamifiedSyntax.star_31_01
#print axioms PM.RamifiedSyntax.star_31_1
