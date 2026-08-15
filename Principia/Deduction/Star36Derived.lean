import Principia.Deduction.Star35Derived
import Principia.FirstEdition.Volume1.Star36Source

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱36 -/

/-- ✱36·01, `P⟏α`, as the contextual relation abstraction `α↿P↾α`.
The incomplete relation has the scope supplied by `continuation`. -/
def star_36_01
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (continuation : Formula signature real [relationSort order 0] order) :
    Formula signature real []
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) order)
        (relationSort order 0)) :=
  star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_35_03 negation disjunction alpha.weaken.weaken
      relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
      (.apparent (.succ .zero))) continuation

/-- The complete contextual expansion printed at ✱36·01. -/
theorem star_36_01_unfold
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (continuation : Formula signature real [relationSort order 0] order) :
    star_36_01 vocabulary negation disjunction alpha relation continuation =
      star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_35_03 negation disjunction alpha.weaken.weaken
          relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
          (.apparent (.succ .zero))) continuation := rfl

/-- Audited contextual reading of ✱36·11. -/
def star_36_11_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (continuation : Formula signature real [relationSort order 0] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱36·11. ⊢ . P⟏α = α◁P▷α"
  scopeReading := "Both incomplete relation symbols have the scope supplied by the continuation."
  parsed := .assertion (star_4_01 vocabulary.finalNegation
    vocabulary.finalDisjunction
    (star_36_01 vocabulary negation disjunction alpha relation continuation)
    (star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_35_03 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))) continuation))

/-- ✱36·11, the assertion of the eliminable definition ✱36·01.
PM prints no demonstration for this assertion.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_36_11
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (continuation : Formula signature real [relationSort order 0] order) :
    Derivation (star_36_11_reading vocabulary negation disjunction alpha
      relation continuation).parsed := by
  have definitionUnfold := star_36_01_unfold vocabulary negation disjunction
    alpha relation continuation
  have line1 := star_4_2 vocabulary.finalNegation vocabulary.finalDisjunction
    (star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_35_03 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))) continuation)
  exact Derivation.castAssertion
    (congrArg (fun left => star_4_01 vocabulary.finalNegation
      vocabulary.finalDisjunction left
      (star_21_01 vocabulary.abstractionExistential
        vocabulary.leftUniversal vocabulary.rightUniversal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (star_35_03 negation disjunction alpha.weaken.weaken
          relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
          (.apparent (.succ .zero))) continuation)) definitionUnfold)
    line1

/-- Audited contextual reading of ✱36·13. -/
def star_36_13_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱36·13. ⊢ : x(P⟏α)y .≡. x∈α . y∈α . xPy"
  scopeReading := "The limited relation is eliminated by ✱36·01; the resulting two-place abstraction has the scope of the displayed equivalence."
  parsed := .assertion
    (star_36_01 vocabulary negation disjunction alpha relation
      (star_21_3_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction
        (star_35_03 negation disjunction alpha.weaken.weaken
          relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
          (.apparent (.succ .zero))) x y))

/-- ✱36·13, exactly the ✱35·102/✱21·3 instance exposed by ✱36·01.
After unfolding, the remaining scope transport has the distinct
reducibility and abstraction existential roots recorded at ✱21·3; ✱10·35
does not identify those trees.
PM prints no demonstration for this assertion.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_36_13
    (vocabulary : Star21EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (relation : Term signature real []
      (relationSort order relationExcess))
    (x y : Term signature real [] .individual)
    (reducibility_scope_transport : Star21EliminationHypothesis vocabulary
      (star_35_03 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))) x y) :
    Derivation (star_36_13_reading vocabulary negation disjunction alpha
      relation x y).parsed := by
  have definitionUnfold := star_36_01_unfold vocabulary negation disjunction
    alpha relation
    (star_21_3_continuation vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction
      (star_35_03 negation disjunction alpha.weaken.weaken
        relation.weaken.weaken alpha.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))) x y)
  have line1 := star_35_102 vocabulary negation disjunction alpha relation
    alpha x y reducibility_scope_transport
  exact Derivation.castAssertion definitionUnfold line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_36_01_unfold
#print axioms PM.RamifiedSyntax.star_36_11
#print axioms PM.RamifiedSyntax.star_36_13
