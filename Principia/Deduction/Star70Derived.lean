import Principia.Deduction.Star63Derived
import Principia.Deduction.Star10Derived
import Principia.Deduction.Star12Derived
import Principia.FirstEdition.Volume1.Star70Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱70

The arrow class is a class whose arguments are themselves relations.  Its
sort is therefore `.function [relationSort relationOrder 0] conditionOrder 0`;
it is not an individual class and it is not a relation-valued term.  The
definition below is the systematic-ambiguity instance of ✱20·01 at that sort.
-/

/-- The matrix printed inside the relation-class abstraction at ✱70·01:
`R⃗ʻʻᗡʻR ⊂ α . R⃖ʻʻDʻR ⊂ β`.  The two conjuncts retain independent assigned
orders. -/
def star_70_01_matrix
    (referentNegation : signature.Negation referentOrder)
    (relataNegation : signature.Negation relataOrder)
    (conjunctionNegation : signature.Negation
      (max referentOrder relataOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max referentOrder relataOrder))
    (referentInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) referentOrder)
    (relataInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) relataOrder) :
    Formula signature real (relationSort relationOrder 0 :: apparent)
      (max referentOrder relataOrder) :=
  mixedConjunction referentNegation relataNegation conjunctionNegation
    conjunctionDisjunction referentInclusion relataInclusion

theorem star_70_01_matrix_unfold
    (referentNegation : signature.Negation referentOrder)
    (relataNegation : signature.Negation relataOrder)
    (conjunctionNegation : signature.Negation
      (max referentOrder relataOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max referentOrder relataOrder))
    (referentInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) referentOrder)
    (relataInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) relataOrder) :
    star_70_01_matrix referentNegation relataNegation conjunctionNegation
        conjunctionDisjunction referentInclusion relataInclusion =
      mixedConjunction referentNegation relataNegation conjunctionNegation
        conjunctionDisjunction referentInclusion relataInclusion := rfl

/-- Logical vocabulary for the contextual definition ✱70·01. -/
structure Star70DefinitionVocabulary (signature : Signature)
    (relationOrder referentOrder relataOrder scopeOrder : Nat) where
  referentNegation : signature.Negation referentOrder
  relataNegation : signature.Negation relataOrder
  matrixNegation : signature.Negation (max referentOrder relataOrder)
  matrixDisjunction : signature.Disjunction (max referentOrder relataOrder)
  existential : ExistentialVocabulary signature
    (.function [relationSort relationOrder 0]
      (max referentOrder relataOrder) 0)
    (max
      (bindOrder (max referentOrder relataOrder)
        (relationSort relationOrder 0))
      scopeOrder)
  universal : signature.Universal (relationSort relationOrder 0)
    (max referentOrder relataOrder)
  equivalenceNegation : signature.Negation (max referentOrder relataOrder)
  equivalenceDisjunction : signature.Disjunction (max referentOrder relataOrder)
  abstractionLeftNegation : signature.Negation
    (bindOrder (max referentOrder relataOrder)
      (relationSort relationOrder 0))
  abstractionRightNegation : signature.Negation scopeOrder
  abstractionOuterNegation : signature.Negation
    (max
      (bindOrder (max referentOrder relataOrder)
        (relationSort relationOrder 0))
      scopeOrder)
  abstractionDisjunction : signature.Disjunction
    (max
      (bindOrder (max referentOrder relataOrder)
        (relationSort relationOrder 0))
      scopeOrder)

/-- ✱70·01, as an eliminable contextual class abstraction.  The bound
predicative function is a class of relations; no class enters the ontology as
a standalone term. -/
def star_70_01
    (vocabulary : Star70DefinitionVocabulary signature relationOrder
      referentOrder relataOrder scopeOrder)
    (referentInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) referentOrder)
    (relataInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) relataOrder)
    (continuation : Formula signature real
      (.function [relationSort relationOrder 0]
        (max referentOrder relataOrder) 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max
          (bindOrder (max referentOrder relataOrder)
            (relationSort relationOrder 0))
          scopeOrder)
        (.function [relationSort relationOrder 0]
          (max referentOrder relataOrder) 0)) :=
  .sometimes vocabulary.existential
    (mixedConjunction vocabulary.abstractionLeftNegation
      vocabulary.abstractionRightNegation vocabulary.abstractionOuterNegation
      vocabulary.abstractionDisjunction
      (.always vocabulary.universal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          ((star_70_01_matrix vocabulary.referentNegation
            vocabulary.relataNegation vocabulary.matrixNegation
            vocabulary.matrixDisjunction referentInclusion relataInclusion).rename
              (liftRenaming (fun v => .succ v)))))
      continuation)

/-- The full defining expansion of ✱70·01. -/
theorem star_70_01_unfold
    (vocabulary : Star70DefinitionVocabulary signature relationOrder
      referentOrder relataOrder scopeOrder)
    (referentInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) referentOrder)
    (relataInclusion : Formula signature real
      (relationSort relationOrder 0 :: apparent) relataOrder)
    (continuation : Formula signature real
      (.function [relationSort relationOrder 0]
        (max referentOrder relataOrder) 0 :: apparent) scopeOrder) :
    star_70_01 vocabulary referentInclusion relataInclusion continuation =
      .sometimes vocabulary.existential
        (mixedConjunction vocabulary.abstractionLeftNegation
          vocabulary.abstractionRightNegation
          vocabulary.abstractionOuterNegation
          vocabulary.abstractionDisjunction
          (.always vocabulary.universal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              ((star_70_01_matrix vocabulary.referentNegation
                vocabulary.relataNegation vocabulary.matrixNegation
                vocabulary.matrixDisjunction referentInclusion
                relataInclusion).rename
                  (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

/-! ## ✱70·1, the systematic-ambiguity instance of ✱20·3 -/

/-- Vocabulary for the ✱20·3 elimination at a relation argument sort. -/
structure Star70EliminationVocabulary (signature : Signature)
    (relationOrder referentOrder relataOrder : Nat) where
  definition : Star70DefinitionVocabulary signature relationOrder
    referentOrder relataOrder (max referentOrder relataOrder)
  reducibilityExistential : ExistentialVocabulary signature
    (.function [relationSort relationOrder 0]
      (max referentOrder relataOrder) 0)
    (bindOrder (max referentOrder relataOrder)
      (relationSort relationOrder 0))
  reducibilityOuterNegation : signature.Negation
    (bindOrder
      (bindOrder (max referentOrder relataOrder)
        (relationSort relationOrder 0))
      (.function [relationSort relationOrder 0]
        (max referentOrder relataOrder) 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder
        (bindOrder (max referentOrder relataOrder)
          (relationSort relationOrder 0))
        (.function [relationSort relationOrder 0]
          (max referentOrder relataOrder) 0))
      (bindOrder
        (max
          (bindOrder (max referentOrder relataOrder)
            (relationSort relationOrder 0))
          (max referentOrder relataOrder))
        (.function [relationSort relationOrder 0]
          (max referentOrder relataOrder) 0)))

/-- The predicative relation-class variable on the ✱10·43 line of ✱20·3. -/
def star_70_1_predicateMatrix
    (_matrix : Formula signature real [relationSort relationOrder 0]
      conditionOrder) :
    Formula signature
      (.function [relationSort relationOrder 0] conditionOrder 0 :: real)
      [relationSort relationOrder 0] conditionOrder :=
  applyUnary
    (.real (.zero : Var
      (.function [relationSort relationOrder 0] conditionOrder 0 :: real)
      (.function [relationSort relationOrder 0] conditionOrder 0)))
    (.apparent .zero)

/-- Exact ✱10·43 specialization used inside the ✱20·3 instance. -/
def star_70_1_transportFormula
    (universal : signature.Universal (relationSort relationOrder 0)
      conditionOrder)
    (equivalenceNegation : signature.Negation conditionOrder)
    (equivalenceDisjunction : signature.Disjunction conditionOrder)
    (outerNegation : signature.Negation
      (bindOrder conditionOrder (relationSort relationOrder 0)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder conditionOrder (relationSort relationOrder 0))
        conditionOrder))
    (matrix : Formula signature real [relationSort relationOrder 0]
      conditionOrder)
    (relation : Term signature real [] (relationSort relationOrder 0)) :
    Formula signature
      (.function [relationSort relationOrder 0] conditionOrder 0 :: real) []
      (max (bindOrder conditionOrder (relationSort relationOrder 0))
        conditionOrder) :=
  mixedImplication outerNegation outerDisjunction
    (.always universal
      (equivalence equivalenceNegation equivalenceDisjunction
        (star_70_1_predicateMatrix matrix) matrix.weakenReal))
    ((equivalence equivalenceNegation equivalenceDisjunction
      (star_70_1_predicateMatrix matrix) matrix.weakenReal).instantiate
        relation.weakenReal)

/-- The membership continuation of ✱70·1 after ✱70·01 is expanded. -/
def star_70_1_continuation
    (equivalenceNegation : signature.Negation conditionOrder)
    (equivalenceDisjunction : signature.Disjunction conditionOrder)
    (matrix : Formula signature real [relationSort relationOrder 0]
      conditionOrder)
    (relation : Term signature real [] (relationSort relationOrder 0)) :
    Formula signature real
      [.function [relationSort relationOrder 0] conditionOrder 0]
      conditionOrder :=
  equivalence equivalenceNegation equivalenceDisjunction
    (applyUnary (.apparent .zero) relation.weaken)
    ((matrix.instantiate relation).rename
      (emptyRenaming
        (target :=
          [.function [relationSort relationOrder 0] conditionOrder 0])))

/-- Object formula of ✱70·1, with the definition ✱70·01 visibly in use. -/
def star_70_1_formula
    (vocabulary : Star70EliminationVocabulary signature relationOrder
      referentOrder relataOrder)
    (referentInclusion : Formula signature real
      [relationSort relationOrder 0] referentOrder)
    (relataInclusion : Formula signature real
      [relationSort relationOrder 0] relataOrder)
    (relation : Term signature real [] (relationSort relationOrder 0)) :=
  let matrix := star_70_01_matrix vocabulary.definition.referentNegation
    vocabulary.definition.relataNegation vocabulary.definition.matrixNegation
    vocabulary.definition.matrixDisjunction referentInclusion relataInclusion
  star_70_01 vocabulary.definition referentInclusion relataInclusion
    (star_70_1_continuation vocabulary.definition.equivalenceNegation
      vocabulary.definition.equivalenceDisjunction matrix relation)

theorem star_70_1_formula_unfold
    (vocabulary : Star70EliminationVocabulary signature relationOrder
      referentOrder relataOrder)
    (referentInclusion : Formula signature real
      [relationSort relationOrder 0] referentOrder)
    (relataInclusion : Formula signature real
      [relationSort relationOrder 0] relataOrder)
    (relation : Term signature real [] (relationSort relationOrder 0)) :
    star_70_1_formula vocabulary referentInclusion relataInclusion relation =
      star_70_01 vocabulary.definition referentInclusion relataInclusion
        (star_70_1_continuation vocabulary.definition.equivalenceNegation
          vocabulary.definition.equivalenceDisjunction
          (star_70_01_matrix vocabulary.definition.referentNegation
            vocabulary.definition.relataNegation
            vocabulary.definition.matrixNegation
            vocabulary.definition.matrixDisjunction referentInclusion
            relataInclusion)
          relation) := rfl

/-- The remaining contextual reducibility-scope transport inherited from the
generalized replay of ✱20·3.  This is kept separate from the asserted formula:
it is not a premise printed at ✱70·1, and it is stronger than the proved
order-zero object equivalence ✱10·35. -/
def Star70ReducibilityScopeTransport
    (vocabulary : Star70EliminationVocabulary signature relationOrder
      referentOrder relataOrder)
    (referentInclusion : Formula signature real
      [relationSort relationOrder 0] referentOrder)
    (relataInclusion : Formula signature real
      [relationSort relationOrder 0] relataOrder)
    (relation : Term signature real [] (relationSort relationOrder 0)) : Prop :=
  let matrix := star_70_01_matrix vocabulary.definition.referentNegation
    vocabulary.definition.relataNegation vocabulary.definition.matrixNegation
    vocabulary.definition.matrixDisjunction referentInclusion relataInclusion
  (⊢ᵣ star_70_1_transportFormula vocabulary.definition.universal
    vocabulary.definition.equivalenceNegation
    vocabulary.definition.equivalenceDisjunction
    vocabulary.definition.abstractionLeftNegation
    vocabulary.definition.abstractionDisjunction matrix relation) →
  ⊢ᵣ mixedImplication vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction
    (star_12_1_formula vocabulary.reducibilityExistential
      vocabulary.definition.universal
      vocabulary.definition.equivalenceNegation
      vocabulary.definition.equivalenceDisjunction matrix)
    (star_70_1_formula vocabulary referentInclusion relataInclusion relation)

/-- Audited reading of ✱70·1. -/
def star_70_1_reading
    (vocabulary : Star70EliminationVocabulary signature relationOrder
      referentOrder relataOrder)
    (referentInclusion : Formula signature real
      [relationSort relationOrder 0] referentOrder)
    (relataInclusion : Formula signature real
      [relationSort relationOrder 0] relataOrder)
    (relation : Term signature real [] (relationSort relationOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted
    "✱70·1. ⊢: R ∈ α →β.≡. R⃗ʻʻᗡʻR ⊂α. R⃖ʻʻDʻR⊂β [✱20·3.(✱70·01)]"
  parsed := .assertion
    (star_70_1_formula vocabulary referentInclusion relataInclusion relation)
  scopeReading := "The class of relations α→β is eliminated contextually by ✱70·01; its matrix is the displayed conjunction."

/-- ✱70·1 by the printed `[✱20·3.(✱70·01)]` route.

The current ✱20·3 reconstruction remains conditional on a contextual
reducibility-scope transport.  The same stronger condition is therefore
explicit here: its `mixedImplication` root does not reduce to the `star_4_01`
root exported by ✱10·35.
`direct_assumptions: PM1:REDUCIBILITY` records the ✱12·1 vocabulary; the
logical scope-transport premise remains explicit in the theorem signature.
`demonstration_provenance: follows-printed`. -/
theorem star_70_1
    (vocabulary : Star70EliminationVocabulary signature relationOrder
      referentOrder relataOrder)
    (referentInclusion : Formula signature real
      [relationSort relationOrder 0] referentOrder)
    (relataInclusion : Formula signature real
      [relationSort relationOrder 0] relataOrder)
    (relation : Term signature real [] (relationSort relationOrder 0))
    (reducibility_scope_transport : Star70ReducibilityScopeTransport vocabulary
      referentInclusion relataInclusion relation) :
    Derivation (star_70_1_reading vocabulary referentInclusion
      relataInclusion relation).parsed := by
  let matrix := star_70_01_matrix vocabulary.definition.referentNegation
    vocabulary.definition.relataNegation vocabulary.definition.matrixNegation
    vocabulary.definition.matrixDisjunction referentInclusion relataInclusion
  have line1 := star_10_43 vocabulary.definition.universal
    vocabulary.definition.equivalenceNegation
    vocabulary.definition.equivalenceDisjunction
    vocabulary.definition.abstractionLeftNegation
    vocabulary.definition.abstractionDisjunction
    (star_70_1_predicateMatrix matrix) matrix.weakenReal relation.weakenReal
  have line2 := reducibility_scope_transport line1
  have line3 := star_12_1 vocabulary.reducibilityExistential
    vocabulary.definition.universal vocabulary.definition.equivalenceNegation
    vocabulary.definition.equivalenceDisjunction matrix
  have line4 := Derivation.star_9_12 vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction line3 line2
  exact line4

/-!
No later assertion of ✱70 is declared from this conditional result.  The
available `star_20_3` cannot itself discharge the printed citation at the
required systematic-ambiguity instance: its matrix has apparent context
`[.individual]` and its abstraction is rooted at `star_20_01` for
`classSort resultOrder 0`, whereas `star_70_1_formula` has apparent context
`[relationSort relationOrder 0]` and is rooted at `star_70_01` for
`.function [relationSort relationOrder 0]
  (max referentOrder relataOrder) 0`.

Consequently the constructor `.sometimes` produced by `star_20_3_formula`
binds a class of individuals, while the constructor `.sometimes` required by
`star_70_1_formula` binds a class of relations.  These two `SortCode.function`
indices do not reduce to one another.  The proof above therefore replays the
systematic-ambiguity instance of the printed ✱20·3 route and exposes its
still-missing contextual bridge as `reducibility_scope_transport`; it is not
an unconditional derivation of ✱70·1.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_70_01_matrix_unfold
#print axioms PM.RamifiedSyntax.star_70_01_unfold
#print axioms PM.RamifiedSyntax.star_70_1_formula_unfold
#print axioms PM.RamifiedSyntax.star_70_1
