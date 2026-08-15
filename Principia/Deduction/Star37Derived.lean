import Principia.Deduction.Star36Derived
import Principia.FirstEdition.Volume1.Star37Source

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱37 — images of relations -/

/-- The vocabulary required by the predicative class abstraction eliminated
at ✱37·1.  It packages no new rule. -/
structure Star37EliminationVocabulary (signature : Signature)
    (resultOrder : Nat) where
  abstractionExistential : ExistentialVocabulary signature
    (classSort resultOrder 0)
    (max (bindOrder resultOrder .individual) resultOrder)
  reducibilityExistential : ExistentialVocabulary signature
    (classSort resultOrder 0) (bindOrder resultOrder .individual)
  universal : signature.Universal .individual resultOrder
  equivalenceNegation : signature.Negation resultOrder
  equivalenceDisjunction : signature.Disjunction resultOrder
  leftNegation : signature.Negation (bindOrder resultOrder .individual)
  rightNegation : signature.Negation resultOrder
  outerNegation : signature.Negation
    (max (bindOrder resultOrder .individual) resultOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder resultOrder .individual) resultOrder)
  reducibilityOuterNegation : signature.Negation
    (bindOrder (bindOrder resultOrder .individual)
      (classSort resultOrder 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder resultOrder .individual)
        (classSort resultOrder 0))
      (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
        (classSort resultOrder 0)))
  finalNegation : signature.Negation
    (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
      (classSort resultOrder 0))
  finalDisjunction : signature.Disjunction
    (bindOrder (max (bindOrder resultOrder .individual) resultOrder)
      (classSort resultOrder 0))

/-- The matrix `(∃y).y∈β.xRy` printed in the definition ✱37·01.  The
apparent variable before binding is `x`; after binding, `y` is zero. -/
def star_37_01_matrix
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real apparent
      (classSort relationOrder classExcess))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess)) :
    Formula signature real (.individual :: apparent)
      (bindOrder relationOrder .individual) :=
  .sometimes existential
    (conjunction negation disjunction
      (membership (.apparent .zero) beta.weaken.weaken)
      (applyBinary relation.weaken.weaken (.apparent (.succ .zero))
        (.apparent .zero)))

/-- Full primitive expansion of the ✱37·01 image matrix. -/
theorem star_37_01_matrix_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real apparent
      (classSort relationOrder classExcess))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess)) :
    star_37_01_matrix existential negation disjunction beta relation =
      .sometimes existential
        (conjunction negation disjunction
          (membership (.apparent .zero) beta.weaken.weaken)
          (applyBinary relation.weaken.weaken (.apparent (.succ .zero))
            (.apparent .zero))) := rfl

/-- ✱37·01, `Rʻʻβ`, as an incomplete class abstraction. -/
def star_37_01
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real apparent
      (classSort relationOrder classExcess))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (continuation : Formula signature real
      (classSort (bindOrder relationOrder .individual) 0 :: apparent)
      (bindOrder relationOrder .individual)) :=
  star_20_01 vocabulary.abstractionExistential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_37_01_matrix existential negation disjunction beta relation)
    continuation

/-- The contextual expansion printed at ✱37·01. -/
theorem star_37_01_unfold
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real apparent
      (classSort relationOrder classExcess))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (continuation : Formula signature real
      (classSort (bindOrder relationOrder .individual) 0 :: apparent)
      (bindOrder relationOrder .individual)) :
    star_37_01 vocabulary existential negation disjunction beta relation
        continuation =
      star_20_01 vocabulary.abstractionExistential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (star_37_01_matrix existential negation disjunction beta relation)
        continuation := rfl

/-- Audited contextual reading of ✱37·1. -/
def star_37_1_reading
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real [] (classSort relationOrder classExcess))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "✱37·1. ⊢:x∈ Rʻʻβ.≡.(∃ y).y∈ β.xRy [*20·3.(*37·01)]"
  scopeReading := "The incomplete image class has the scope of the displayed membership equivalence."
  parsed := .assertion
    (star_37_01 vocabulary existential negation disjunction beta relation
      (star_20_3_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction
        (star_37_01_matrix existential negation disjunction beta relation) x))

/-- ✱37·1, exactly the printed ✱20·3 instance of ✱37·01.
The remaining premise transports between the distinct reducibility and
abstraction existential trees exposed by ✱20·3; ✱10·35 does not reduce one
to the other.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_37_1
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real [] (classSort relationOrder classExcess))
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x : Term signature real [] .individual)
    (reducibility_scope_transport :
      (⊢ᵣ star_20_3_transportFormula vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.conjunctionDisjunction
        (star_37_01_matrix existential negation disjunction beta relation) x) →
      ⊢ᵣ mixedImplication vocabulary.reducibilityOuterNegation
        vocabulary.bridgeDisjunction
        (star_12_1_formula vocabulary.reducibilityExistential
          vocabulary.universal vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (star_37_01_matrix existential negation disjunction beta relation))
        (star_20_3_formula vocabulary.abstractionExistential
          vocabulary.universal vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction vocabulary.leftNegation
          vocabulary.rightNegation vocabulary.outerNegation
          vocabulary.conjunctionDisjunction
          (star_37_01_matrix existential negation disjunction beta relation)
          x)) :
    Derivation (star_37_1_reading vocabulary existential negation disjunction
      beta relation x).parsed := by
  have definitionUnfold := star_37_01_unfold vocabulary existential negation
    disjunction beta relation
    (star_20_3_continuation vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction
      (star_37_01_matrix existential negation disjunction beta relation) x)
  have line1 := star_20_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    vocabulary.reducibilityOuterNegation vocabulary.bridgeDisjunction
    vocabulary.finalNegation vocabulary.finalDisjunction
    (star_37_01_matrix existential negation disjunction beta relation) x
    reducibility_scope_transport
  exact Derivation.castAssertion definitionUnfold line1

/-! ## The converse image ✱37·105 -/

/-- The right member printed at ✱37·105, `(∃y).y∈β.yRx`.  Its second
conjunct applies `R` to the apparent pair in the order `y, x`, so this tree
is not the ✱37·01 image matrix, whose second conjunct applies its relation
in the order `x, y`. -/
def star_37_105_matrix
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real apparent
      (classSort relationOrder classExcess))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess)) :
    Formula signature real (.individual :: apparent)
      (bindOrder relationOrder .individual) :=
  .sometimes existential
    (conjunction negation disjunction
      (membership (.apparent .zero) beta.weaken.weaken)
      (applyBinary relation.weaken.weaken (.apparent .zero)
        (.apparent (.succ .zero))))

/-- Full primitive expansion of the ✱37·105 right member. -/
theorem star_37_105_matrix_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real apparent
      (classSort relationOrder classExcess))
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess)) :
    star_37_105_matrix existential negation disjunction beta relation =
      .sometimes existential
        (conjunction negation disjunction
          (membership (.apparent .zero) beta.weaken.weaken)
          (applyBinary relation.weaken.weaken (.apparent .zero)
            (.apparent (.succ .zero)))) := rfl

/-- Audited contextual reading of ✱37·105.  The image class is formed from
the converse relation, exactly as PM's `Řʻʻβ` requires; the right member of
the displayed equivalence is the independently built printed tree
`(∃y).y∈β.yRx`, which mentions `R` and not `Ř`. -/
def star_37_105_reading
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (beta : Term signature real [] (classSort relationOrder classExcess))
    (relation converseRelation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱37·105. ⊢:x∈ Řʻʻβ.≡.(∃ y).y∈ β.yRx [*37·1.*31·11]"
  scopeReading := "The incomplete converse image class has the scope of the displayed membership equivalence; the printed right member is stated with the original relation."
  parsed := .assertion
    (star_37_01 vocabulary existential negation disjunction beta
      converseRelation
      (star_20_3_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction
        (star_37_105_matrix existential negation disjunction beta relation)
        x))

/- ✱37·105 is catalogued as a reading only.  The printed route is
`✱37·1.✱31·11`, and neither half closes here.

The ✱37·1 instance for `Ř` produces the continuation whose right member is
`star_37_01_matrix existential negation disjunction beta converseRelation`,
that is

  `.sometimes existential (conjunction … (membership (.apparent .zero) β)
     (.apply converseRelation (.cons (.apparent (.succ .zero))
        (.cons (.apparent .zero) .nil))))`,

whereas ✱37·105 prints `star_37_105_matrix … relation`, that is

  `.sometimes existential (conjunction … (membership (.apparent .zero) β)
     (.apply relation (.cons (.apparent .zero)
        (.cons (.apparent (.succ .zero)) .nil))))`.

The two `Formula.apply` nodes carry different head terms and their
`Arguments.cons` spines are in the opposite order, so no `rfl` identifies
them.  What identifies them in PM is ✱31·11, and
`Principia/Deduction/Star31Derived.lean` declares no theorem: the ✱21·3
elimination it needs is itself still conditional.  Even with ✱31·11 in hand
the equivalence would still have to be carried under `.sometimes` and
`conjunction`, which is ✱10·11·281; the library has ✱10·28 only for
`Formula signature real [argument] 0` (`star_10_28`), and no ✱10·281 at
all.  Nothing is asserted here. -/

/-! ## The image-membership relation ✱37·02 -/

/-- ✱37·02, `R_∈`, expanded contextually as the relation abstraction
`α̂β̂(α=Rʻʻβ)`.  The supplied matrix is the independently constructed
object formula printed as `α=Rʻʻβ`. -/
def star_37_02
    (vocabulary : BinaryEliminationVocabulary signature
      (classSort classOrder classExcess) (classSort classOrder classExcess)
      order)
    (imageIdentity : Formula signature real
      [classSort classOrder classExcess, classSort classOrder classExcess]
      order)
    (continuation : Formula signature real
      [.function [classSort classOrder classExcess,
        classSort classOrder classExcess] order 0] order) :=
  binaryAbstraction vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction imageIdentity continuation

/-- Full contextual expansion of the definition ✱37·02. -/
theorem star_37_02_unfold
    (vocabulary : BinaryEliminationVocabulary signature
      (classSort classOrder classExcess) (classSort classOrder classExcess)
      order)
    (imageIdentity : Formula signature real
      [classSort classOrder classExcess, classSort classOrder classExcess]
      order)
    (continuation : Formula signature real
      [.function [classSort classOrder classExcess,
        classSort classOrder classExcess] order 0] order) :
    star_37_02 vocabulary imageIdentity continuation =
      binaryAbstraction vocabulary.abstractionExistential
        vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction imageIdentity continuation := rfl

/-- Audited contextual reading of ✱37·101. -/
def star_37_101_reading
    (vocabulary : BinaryEliminationVocabulary signature
      (classSort classOrder classExcess) (classSort classOrder classExcess)
      order)
    (imageIdentity : Formula signature real
      [classSort classOrder classExcess, classSort classOrder classExcess]
      order)
    (alpha beta :
      Term signature real [] (classSort classOrder classExcess)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱37·101. ⊢:α R_∈β.≡.α=Rʻʻβ [*21·3.(*37·02)]"
  scopeReading := "The relation abstraction ✱37·02 has the scope of the displayed application equivalence."
  parsed := .assertion
    (star_37_02 vocabulary imageIdentity
      (binaryEliminationContinuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction imageIdentity alpha beta))

/-- ✱37·101, following the printed `✱21·3.(✱37·02)` route.
The remaining premise transports between the distinct reducibility and
abstraction existential trees; ✱10·35 does not identify their vocabularies or
bodies.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_37_101
    (vocabulary : BinaryEliminationVocabulary signature
      (classSort classOrder classExcess) (classSort classOrder classExcess)
      order)
    (imageIdentity : Formula signature real
      [classSort classOrder classExcess, classSort classOrder classExcess]
      order)
    (alpha beta :
      Term signature real [] (classSort classOrder classExcess))
    (reducibility_scope_transport : BinaryEliminationHypothesis vocabulary
      imageIdentity alpha beta) :
    Derivation
      (star_37_101_reading vocabulary imageIdentity alpha beta).parsed := by
  have definitionUnfold := star_37_02_unfold vocabulary imageIdentity
    (binaryEliminationContinuation vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction imageIdentity alpha beta)
  have line1 := binaryElimination vocabulary imageIdentity alpha beta
    reducibility_scope_transport
  exact Derivation.castAssertion definitionUnfold line1

/-- Audited reading of the converse-relation substitution at ✱37·102.
The matrix parameter is built independently from the printed right member
`α=Řʻʻβ`; no identification with the non-converse matrix is made. -/
def star_37_102_reading
    (vocabulary : BinaryEliminationVocabulary signature
      (classSort classOrder classExcess) (classSort classOrder classExcess)
      order)
    (converseImageIdentity :
      Formula signature real
        [classSort classOrder classExcess, classSort classOrder classExcess]
        order)
    (alpha beta :
      Term signature real [] (classSort classOrder classExcess)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱37·102. ⊢:α(Ř)_∈β.≡.α=Řʻʻβ [*37·101]"
  scopeReading := "This is the Ř/R substitution in ✱37·101, with its own converse-image identity matrix."
  parsed := .assertion
    (star_37_02 vocabulary converseImageIdentity
      (binaryEliminationContinuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction converseImageIdentity alpha beta))

/-- ✱37·102, exactly the printed Ř/R instance of ✱37·101.
It inherits the same unresolved reducibility-scope transport as ✱37·101.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_37_102
    (vocabulary : BinaryEliminationVocabulary signature
      (classSort classOrder classExcess) (classSort classOrder classExcess)
      order)
    (converseImageIdentity :
      Formula signature real
        [classSort classOrder classExcess, classSort classOrder classExcess]
        order)
    (alpha beta :
      Term signature real [] (classSort classOrder classExcess))
    (reducibility_scope_transport : BinaryEliminationHypothesis vocabulary
      converseImageIdentity alpha beta) :
    Derivation (star_37_102_reading vocabulary converseImageIdentity
      alpha beta).parsed := by
  have line1 := star_37_101 vocabulary converseImageIdentity alpha beta
    reducibility_scope_transport
  exact line1

/-! ## The eliminable existence abbreviation ✱37·05 -/

/-- ✱37·05, `E‼Rʻʻβ`, expanded as the displayed universal implication. -/
def star_37_05
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (beta : Term signature real [] (classSort order classExcess))
    (relationValueExists : Formula signature real [.individual] order) :
    Formula signature real [] (bindOrder order .individual) :=
  .always universal
    (implication negation disjunction
      (membership (.apparent .zero) beta.weaken) relationValueExists)

/-- Full expansion of the definition ✱37·05. -/
theorem star_37_05_unfold
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (beta : Term signature real [] (classSort order classExcess))
    (relationValueExists : Formula signature real [.individual] order) :
    star_37_05 universal negation disjunction beta relationValueExists =
      .always universal
        (implication negation disjunction
          (membership (.apparent .zero) beta.weaken)
          relationValueExists) := rfl

/-- Audited reading of the definitional assertion ✱37·104. -/
def star_37_104_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (outerNegation : signature.Negation (bindOrder order .individual))
    (outerDisjunction : signature.Disjunction (bindOrder order .individual))
    (beta : Term signature real [] (classSort order classExcess))
    (relationValueExists : Formula signature real [.individual] order) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱37·104. ⊢:. E‼Rʻʻβ.≡:y∈ β.⊃y.E!Rʻy [*4·2.(*37·05)]"
  scopeReading := "The universal quantifier covers the implication defining existence throughout the image."
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (star_37_05 universal negation disjunction beta relationValueExists)
    (.always universal
      (implication negation disjunction
        (membership (.apparent .zero) beta.weaken) relationValueExists)))

/-- ✱37·104, by the printed `✱4·2.(✱37·05)` route.
`demonstration_provenance: follows-printed`. -/
theorem star_37_104
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (outerNegation : signature.Negation (bindOrder order .individual))
    (outerDisjunction : signature.Disjunction (bindOrder order .individual))
    (beta : Term signature real [] (classSort order classExcess))
    (relationValueExists : Formula signature real [.individual] order) :
    Derivation (star_37_104_reading universal negation disjunction
      outerNegation outerDisjunction beta relationValueExists).parsed := by
  have definitionUnfold := star_37_05_unfold universal negation disjunction
    beta relationValueExists
  have line1 := star_4_2 outerNegation outerDisjunction
    (.always universal
      (implication negation disjunction
        (membership (.apparent .zero) beta.weaken) relationValueExists))
  exact Derivation.castAssertion
    (congrArg (fun left => star_4_01 outerNegation outerDisjunction left
      (.always universal
        (implication negation disjunction
          (membership (.apparent .zero) beta.weaken)
          relationValueExists))) definitionUnfold)
    line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_37_01_matrix_unfold
#print axioms PM.RamifiedSyntax.star_37_01_unfold
#print axioms PM.RamifiedSyntax.star_37_1
#print axioms PM.RamifiedSyntax.star_37_105_matrix_unfold
#print axioms PM.RamifiedSyntax.star_37_02_unfold
#print axioms PM.RamifiedSyntax.star_37_101
#print axioms PM.RamifiedSyntax.star_37_102
#print axioms PM.RamifiedSyntax.star_37_05_unfold
#print axioms PM.RamifiedSyntax.star_37_104
