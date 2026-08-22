import Principia.Deduction.Star21Derived
import Principia.FirstEdition.Volume1.Star23Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱23

Relation inclusion is the two-variable analogue of class inclusion at
✱22·01.  Intersection, sum, complement, and difference remain incomplete
symbols: each is expanded contextually by ✱21·01 and therefore never becomes a
standalone relation-valued `Term`.
-/

/-- The vocabulary needed by one predicative relation abstraction ✱21·01. -/
structure Star23RelationVocabulary (signature : Signature)
    (order scopeOrder : Nat) where
  existential : ExistentialVocabulary signature (relationSort order 0)
    (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
  leftUniversal : signature.Universal .individual order
  rightUniversal : signature.Universal .individual
    (bindOrder order .individual)
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation
    (bindOrder (bindOrder order .individual) .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)

/-- A closed relation applied to the two apparent individuals of a matrix. -/
def star_23_relationMatrix
    (relation : Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  star_21_02
    (relation.rename
      (emptyRenaming (target := [.individual, .individual])))
    (.apparent .zero) (.apparent (.succ .zero))

/-- Same-order conjunction with an arbitrary apparent-variable context. -/
def star_23_conjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation left) (.neg negation right))

/-- The pointwise matrix defining relation inclusion. -/
def star_23_01_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  implication negation disjunction
    (star_23_relationMatrix relation₁)
    (star_23_relationMatrix relation₂)

/-- ✱23·01: relation inclusion is universal pointwise implication. -/
def star_23_01
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Formula signature real []
      (bindOrder (bindOrder order .individual) .individual) :=
  (star_23_01_matrix negation disjunction relation₁ relation₂).always₂
    leftUniversal rightUniversal

theorem star_23_01_unfold
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    star_23_01 leftUniversal rightUniversal negation disjunction
        relation₁ relation₂ =
      (star_23_01_matrix negation disjunction relation₁ relation₂).always₂
        leftUniversal rightUniversal := rfl

/-- The matrix of the relation intersection ✱23·02. -/
def star_23_02_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  star_23_conjunction negation disjunction
    (star_23_relationMatrix relation₁)
    (star_23_relationMatrix relation₂)

/-- ✱23·02: contextual intersection of two relations. -/
def star_23_02
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_23_02_matrix negation disjunction relation₁ relation₂) continuation

theorem star_23_02_unfold
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    star_23_02 vocabulary negation disjunction relation₁ relation₂
        continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_23_02_matrix negation disjunction relation₁ relation₂)
        continuation := rfl

/-- The matrix of the relation sum ✱23·03. -/
def star_23_03_matrix
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  sameDisjunction disjunction
    (star_23_relationMatrix relation₁)
    (star_23_relationMatrix relation₂)

/-- ✱23·03: contextual sum of two relations. -/
def star_23_03
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_23_03_matrix disjunction relation₁ relation₂) continuation

theorem star_23_03_unfold
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    star_23_03 vocabulary disjunction relation₁ relation₂ continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_23_03_matrix disjunction relation₁ relation₂) continuation := rfl

/-- The matrix of the relation complement ✱23·04. -/
def star_23_04_matrix
    (negation : signature.Negation order)
    (relation : Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  .neg negation (star_23_relationMatrix relation)

/-- ✱23·04: contextual complement of a relation. -/
def star_23_04
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (relation : Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_23_04_matrix negation relation) continuation

theorem star_23_04_unfold
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (relation : Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    star_23_04 vocabulary negation relation continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_23_04_matrix negation relation) continuation := rfl

/-- ✱23·05, with ✱23·02 and ✱23·04 eliminated in the defining matrix. -/
def star_23_05
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_23_conjunction negation disjunction
      (star_23_relationMatrix relation₁)
      (.neg negation (star_23_relationMatrix relation₂))) continuation

theorem star_23_05_unfold
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    star_23_05 vocabulary negation disjunction relation₁ relation₂
        continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_23_conjunction negation disjunction
          (star_23_relationMatrix relation₁)
          (.neg negation (star_23_relationMatrix relation₂))) continuation := rfl

/-! ## Assertions of the four relation-forming definitions -/

/-- Audited contextual reading of ✱23·2. -/
def star_23_2_reading
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . R ∩̇ S = x̂ŷ(xRy . xSy)"
  scopeReading := "Both incomplete relation abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_23_02 vocabulary negation disjunction relation₁ relation₂
      continuation)
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_02_matrix negation disjunction relation₁ relation₂)
      continuation))

/-- ✱23·2, by the eliminable definition ✱23·02.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_2
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    Derivation (star_23_2_reading vocabulary negation disjunction
      finalNegation finalDisjunction relation₁ relation₂ continuation).parsed := by
  have line1 := star_23_02_unfold vocabulary negation disjunction
    relation₁ relation₂ continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_02_matrix negation disjunction relation₁ relation₂)
      continuation)
  unfold star_23_2_reading
  rw [line1]
  exact line2

/-- Audited contextual reading of ✱23·3. -/
def star_23_3_reading
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . R ⊍ S = x̂ŷ(xRy .∨. xSy)"
  scopeReading := "Both incomplete relation abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_23_03 vocabulary disjunction relation₁ relation₂ continuation)
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_03_matrix disjunction relation₁ relation₂) continuation))

/-- ✱23·3, by the eliminable definition ✱23·03.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_3
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    Derivation (star_23_3_reading vocabulary disjunction finalNegation
      finalDisjunction relation₁ relation₂ continuation).parsed := by
  have line1 := star_23_03_unfold vocabulary disjunction relation₁ relation₂
    continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_03_matrix disjunction relation₁ relation₂) continuation)
  unfold star_23_3_reading
  rw [line1]
  exact line2

/-- Audited contextual reading of ✱23·31. -/
def star_23_31_reading
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation : Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . ∸R = x̂ŷ{∼(xRy)}"
  scopeReading := "Both incomplete relation abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_23_04 vocabulary negation relation continuation)
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_04_matrix negation relation) continuation))

/-- ✱23·31, by the eliminable definition ✱23·04.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_31
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation : Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    Derivation (star_23_31_reading vocabulary negation finalNegation
      finalDisjunction relation continuation).parsed := by
  have line1 := star_23_04_unfold vocabulary negation relation continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_04_matrix negation relation) continuation)
  unfold star_23_31_reading
  rw [line1]
  exact line2

/-- Audited contextual reading of ✱23·32. -/
def star_23_32_reading
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ . R ∸ S = x̂ŷ{xRy . ∼(xSy)}"
  scopeReading := "Both incomplete relation abstracts have the scope of the displayed identity."
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_23_05 vocabulary negation disjunction relation₁ relation₂
      continuation)
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_conjunction negation disjunction
        (star_23_relationMatrix relation₁)
        (.neg negation (star_23_relationMatrix relation₂))) continuation))

/-- ✱23·32, by the eliminable definitions ✱23·05, ✱23·02, and ✱23·04.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_32
    (vocabulary : Star23RelationVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) scopeOrder)
        (relationSort order 0)))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    Derivation (star_23_32_reading vocabulary negation disjunction
      finalNegation finalDisjunction relation₁ relation₂ continuation).parsed := by
  have line1 := star_23_05_unfold vocabulary negation disjunction relation₁
    relation₂ continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_21_01 vocabulary.existential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_23_conjunction negation disjunction
        (star_23_relationMatrix relation₁)
        (.neg negation (star_23_relationMatrix relation₂))) continuation)
  unfold star_23_32_reading
  rw [line1]
  exact line2

/-- Audited scope reading of ✱23·1. -/
def star_23_1_reading
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (inclusionNegation : signature.Negation order)
    (inclusionDisjunction : signature.Disjunction order)
    (equivalenceNegation : signature.Negation
      (bindOrder (bindOrder order .individual) .individual))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder (bindOrder order .individual) .individual))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ :. R ⪽ S .≡: xRy .⊃ₓ,y. xSy"
  scopeReading := "The two individual quantifiers cover the pointwise relation implication."
  parsed := .assertion (star_4_01 equivalenceNegation
    equivalenceDisjunction
    (star_23_01 leftUniversal rightUniversal inclusionNegation
      inclusionDisjunction relation₁ relation₂)
    ((star_23_01_matrix inclusionNegation inclusionDisjunction
      relation₁ relation₂).always₂ leftUniversal rightUniversal))

/-- ✱23·1, by definitional expansion of ✱23·01.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_1
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (inclusionNegation : signature.Negation order)
    (inclusionDisjunction : signature.Disjunction order)
    (equivalenceNegation : signature.Negation
      (bindOrder (bindOrder order .individual) .individual))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder (bindOrder order .individual) .individual))
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Derivation (star_23_1_reading leftUniversal rightUniversal
      inclusionNegation inclusionDisjunction equivalenceNegation
      equivalenceDisjunction relation₁ relation₂).parsed := by
  have line1 := star_23_01_unfold leftUniversal rightUniversal
    inclusionNegation inclusionDisjunction relation₁ relation₂
  have line2 := star_4_2 equivalenceNegation equivalenceDisjunction
    ((star_23_01_matrix inclusionNegation inclusionDisjunction
      relation₁ relation₂).always₂ leftUniversal rightUniversal)
  unfold star_23_1_reading
  rw [line1]
  exact line2

/-- Audited scope reading of ✱23·42. -/
def star_23_42_reading
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation : Term signature real [] (relationSort order 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢.R⪽R"
  scopeReading := "Relation inclusion closes both displayed individual variables."
  parsed := .assertion
    (star_23_01 leftUniversal rightUniversal negation disjunction
      relation relation)

/-- Instantiating the two displayed variables restores a closed relation. -/
private theorem star_23_relationMatrix_instantiate
    (relation : Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    (star_23_relationMatrix relation).instantiate₂ x y =
      star_21_02 relation x y := by
  unfold star_23_relationMatrix Formula.instantiate₂ Formula.instantiate
  unfold star_21_02 applyBinary
  cases relation with
  | real relationVar => cases x <;> cases y <;> rfl
  | apparent relationVar => exact nomatch relationVar
  | symbol relationSymbol => cases x <;> cases y <;> rfl

/-- Two-variable instantiation commutes with same-order implication. -/
private theorem star_23_implication_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual, .individual] order)
    (x y : Term signature real [] .individual) :
    (implication negation disjunction left right).instantiate₂ x y =
      implication negation disjunction
        (left.instantiate₂ x y) (right.instantiate₂ x y) := by
  unfold Formula.instantiate₂ Formula.instantiate
  rw [implication_substitute, implication_substitute]

/-- Two-variable instantiation commutes with the contextual conjunction. -/
private theorem star_23_conjunction_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual, .individual] order)
    (x y : Term signature real [] .individual) :
    (star_23_conjunction negation disjunction left right).instantiate₂ x y =
      star_23_conjunction negation disjunction
        (left.instantiate₂ x y) (right.instantiate₂ x y) := by
  unfold star_23_conjunction Formula.instantiate₂ Formula.instantiate
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).substitute (instantiateSubstitution x.weaken)
      |>.substitute (instantiateSubstitution y)) = _
  rw [sameDisjunction_substitute, sameDisjunction_substitute]
  rfl

/-- Instantiation distributes through the defining inclusion matrix. -/
private theorem star_23_01_matrix_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    (star_23_01_matrix negation disjunction relation₁ relation₂).instantiate₂
        x y =
      implication negation disjunction
        (star_21_02 relation₁ x y) (star_21_02 relation₂ x y) := by
  unfold star_23_01_matrix
  rw [star_23_implication_instantiate]
  rw [star_23_relationMatrix_instantiate relation₁ x y,
    star_23_relationMatrix_instantiate relation₂ x y]

/-- ✱23·42, reconstructed from the printed identity by pointwise ✱2·08
and double generalization.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_42
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation : Term signature real [] (relationSort order 0)) :
    Derivation (star_23_42_reading leftUniversal rightUniversal
      negation disjunction relation).parsed := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_01_matrix negation disjunction relation relation).instantiate₂
          x y := by
    intro x y
    rw [star_23_01_matrix_instantiate negation disjunction
      relation relation x y]
    exact star_2_08 negation disjunction (star_21_02 relation x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_01_matrix negation disjunction relation relation) line1
  exact line2

/-
The former block below represented ✱23·4 and ✱23·44 by universally closing
pointwise tautologies, and represented ✱23·441 and ✱23·46 by universally
closing their apparent variables.  Those are not the printed assertions.
It remains here only as local history while the faithful replacements after
the block keep the independently built scope trees visible.

/-! ## Inclusion rules not involving a relation-forming incomplete symbol -/

/-- The full-scope matrix of extensional equivalence at ✱23·4. -/
historical star_23_4_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  let pointwiseEquivalence := star_23_conjunction negation disjunction
    (star_23_01_matrix negation disjunction relation₁ relation₂)
    (star_23_01_matrix negation disjunction relation₂ relation₁)
  star_23_conjunction negation disjunction
    (implication negation disjunction pointwiseEquivalence pointwiseEquivalence)
    (implication negation disjunction pointwiseEquivalence pointwiseEquivalence)

/-- Instantiating ✱23·4 exposes the reflexive ✱4·2 instance. -/
private theorem star_23_4_matrix_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    (star_23_4_matrix negation disjunction relation₁ relation₂).instantiate₂
        x y =
      star_4_01 negation disjunction
        (conjunction negation disjunction
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (implication negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₁ x y)))
        (conjunction negation disjunction
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (implication negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₁ x y))) := by
  unfold star_23_4_matrix
  rw [star_23_conjunction_instantiate,
    star_23_implication_instantiate,
    star_23_conjunction_instantiate,
    star_23_01_matrix_instantiate, star_23_01_matrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·4. -/
historical star_23_4_reading
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    ClaimReading signature real where
  printed := "⊢:. R⪽S.S⪽R.≡:xRy.≡ₓ,y.xSy"
  parsed := .assertion
    ((star_23_4_matrix negation disjunction relation₁ relation₂).always₂
      leftUniversal rightUniversal)

/-- ✱23·4, by definitional expansion of ✱23·01 and pointwise ✱4·2.
`demonstration_provenance: editorial-reconstruction`. -/
historical star_23_4
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Derivation (star_23_4_reading leftUniversal rightUniversal
      negation disjunction relation₁ relation₂).parsed := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_4_matrix negation disjunction relation₁ relation₂).instantiate₂
          x y := by
    intro x y
    rw [star_23_4_matrix_instantiate negation disjunction
      relation₁ relation₂ x y]
    exact star_4_2 negation disjunction
      (conjunction negation disjunction
        (implication negation disjunction (star_21_02 relation₁ x y)
          (star_21_02 relation₂ x y))
        (implication negation disjunction (star_21_02 relation₂ x y)
          (star_21_02 relation₁ x y)))
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_4_matrix negation disjunction relation₁ relation₂) line1
  exact line2

/-- The pointwise transitivity matrix of ✱23·44. -/
historical star_23_44_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  implication negation disjunction
    (star_23_conjunction negation disjunction
      (star_23_01_matrix negation disjunction relation₁ relation₂)
      (star_23_01_matrix negation disjunction relation₂ relation₃))
    (star_23_01_matrix negation disjunction relation₁ relation₃)

/-- Instantiated pointwise normal form of ✱23·44. -/
private theorem star_23_44_matrix_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    (star_23_44_matrix negation disjunction relation₁ relation₂
      relation₃).instantiate₂ x y =
      implication negation disjunction
        (conjunction negation disjunction
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (implication negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₃ x y)))
        (implication negation disjunction (star_21_02 relation₁ x y)
          (star_21_02 relation₃ x y)) := by
  unfold star_23_44_matrix
  rw [star_23_implication_instantiate,
    star_23_conjunction_instantiate,
    star_23_01_matrix_instantiate, star_23_01_matrix_instantiate,
    star_23_01_matrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·44. -/
historical star_23_44_reading
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort order 0)) :
    ClaimReading signature real where
  printed := "⊢:R⪽S.S⪽T.⊃.R⪽T"
  parsed := .assertion
    ((star_23_44_matrix negation disjunction relation₁ relation₂
      relation₃).always₂ leftUniversal rightUniversal)

/-- ✱23·44, by pointwise `Syll` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
historical star_23_44
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort order 0)) :
    Derivation (star_23_44_reading leftUniversal rightUniversal
      negation disjunction relation₁ relation₂ relation₃).parsed := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_44_matrix negation disjunction relation₁ relation₂
          relation₃).instantiate₂ x y := by
    intro x y
    rw [star_23_44_matrix_instantiate negation disjunction
      relation₁ relation₂ relation₃ x y]
    exact star_3_33 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)
      (star_21_02 relation₃ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_44_matrix negation disjunction relation₁ relation₂ relation₃)
    line1
  exact line2

/-- The pointwise formal-implication matrix shared by ✱23·441 and ✱23·46. -/
def star_23_membershipImplicationMatrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (inclusionFirst : Bool)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Formula signature real [.individual, .individual] order :=
  let membership₁ := star_23_relationMatrix relation₁
  let membership₂ := star_23_relationMatrix relation₂
  let inclusion := implication negation disjunction membership₁ membership₂
  implication negation disjunction
    (Bool.casesOn inclusionFirst
      (star_23_conjunction negation disjunction membership₁ inclusion)
      (star_23_conjunction negation disjunction inclusion membership₁))
    membership₂

/-- The two presentations instantiate to the corresponding PM conjunction. -/
private theorem star_23_membershipImplicationMatrix_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (inclusionFirst : Bool)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    (star_23_membershipImplicationMatrix negation disjunction inclusionFirst
      relation₁ relation₂).instantiate₂ x y =
      Bool.casesOn inclusionFirst
        (implication negation disjunction
          (conjunction negation disjunction
            (star_21_02 relation₁ x y)
            (implication negation disjunction (star_21_02 relation₁ x y)
              (star_21_02 relation₂ x y)))
          (star_21_02 relation₂ x y))
        (implication negation disjunction
          (conjunction negation disjunction
            (implication negation disjunction (star_21_02 relation₁ x y)
              (star_21_02 relation₂ x y))
            (star_21_02 relation₁ x y))
          (star_21_02 relation₂ x y)) := by
  cases inclusionFirst <;>
    unfold star_23_membershipImplicationMatrix <;>
    rw [star_23_implication_instantiate,
      star_23_conjunction_instantiate,
      star_23_implication_instantiate,
      star_23_relationMatrix_instantiate,
      star_23_relationMatrix_instantiate] <;> rfl

/-- Audited full-scope reading of ✱23·441. -/
def star_23_441_reading
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    ClaimReading signature real where
  printed := "⊢:R⪽S.xRy.⊃.xSy"
  parsed := .assertion
    ((star_23_membershipImplicationMatrix negation disjunction true
      relation₁ relation₂).always₂ leftUniversal rightUniversal)

/-- ✱23·441, by a pointwise propositional permutation and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_441
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Derivation (star_23_441_reading leftUniversal rightUniversal
      negation disjunction relation₁ relation₂).parsed := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_membershipImplicationMatrix negation disjunction true
          relation₁ relation₂).instantiate₂ x y := by
    intro x y
    rw [star_23_membershipImplicationMatrix_instantiate negation disjunction
      true relation₁ relation₂ x y]
    let p := star_21_02 relation₁ x y
    let q := star_21_02 relation₂ x y
    have line2 := star_3_22 negation disjunction
      (implication negation disjunction p q) p
    have line3 := star_3_35 negation disjunction p q
    have line4 := star_2_05 negation disjunction
      (conjunction negation disjunction (implication negation disjunction p q) p)
      (conjunction negation disjunction p (implication negation disjunction p q)) q
    have line5 := Derivation.star_9_12_same negation disjunction line3 line4
    exact Derivation.star_9_12_same negation disjunction line2 line5
  have line6 := star_11_11 leftUniversal rightUniversal
    (star_23_membershipImplicationMatrix negation disjunction true
      relation₁ relation₂) line1
  exact line6

/-- Audited full-scope reading of ✱23·46. -/
def star_23_46_reading
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    ClaimReading signature real where
  printed := "⊢:xRy.R⪽S.⊃.xSy"
  parsed := .assertion
    ((star_23_membershipImplicationMatrix negation disjunction false
      relation₁ relation₂).always₂ leftUniversal rightUniversal)

/-- ✱23·46, by pointwise `Comp` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_46
    (leftUniversal : signature.Universal .individual order)
    (rightUniversal : signature.Universal .individual
      (bindOrder order .individual))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0)) :
    Derivation (star_23_46_reading leftUniversal rightUniversal
      negation disjunction relation₁ relation₂).parsed := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_membershipImplicationMatrix negation disjunction false
          relation₁ relation₂).instantiate₂ x y := by
    intro x y
    rw [star_23_membershipImplicationMatrix_instantiate negation disjunction
      false relation₁ relation₂ x y]
    exact star_3_35 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_membershipImplicationMatrix negation disjunction false
      relation₁ relation₂) line1
  exact line2

-/

/-! ## Faithful inclusion assertions at a positive assigned order -/

variable {order : Nat}

/-- Binding an individual does not raise an already positive formula order. -/
private theorem star23_bindOrder_succ_individual (order : Nat) :
    bindOrder order.succ .individual = order.succ := by
  cases order with
  | zero => rfl
  | succ order => rfl

/-- Closing both individual arguments likewise preserves a positive order. -/
private theorem star23_doubleBindOrder_succ_individual (order : Nat) :
    bindOrder (bindOrder order.succ .individual) .individual = order.succ := by
  rw [star23_bindOrder_succ_individual order]
  exact star23_bindOrder_succ_individual order

/-- Relation inclusion at a positive order, with only the computed closure
order exposed by dependent transport. -/
private def star_23_01_successor
    (leftUniversal : signature.Universal .individual order.succ)
    (rightUniversal : signature.Universal .individual
      (bindOrder order.succ .individual))
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order.succ 0)) :
    Formula signature real [] order.succ :=
  Eq.mp (congrArg (Formula signature real [])
      (star23_doubleBindOrder_succ_individual order))
    (star_23_01 leftUniversal rightUniversal negation disjunction
      relation₁ relation₂)

/-- Instantiation commutes with independently constructed equivalence. -/
private theorem star_23_equivalence_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left right : Formula signature real [.individual, .individual] resultOrder)
    (x y : Term signature real [] .individual) :
    (equivalence negation disjunction left right).instantiate₂ x y =
      equivalence negation disjunction
        (left.instantiate₂ x y) (right.instantiate₂ x y) := by
  unfold equivalence
  change (star_23_conjunction negation disjunction
    (implication negation disjunction left right)
    (implication negation disjunction right left)).instantiate₂ x y = _
  rw [star_23_conjunction_instantiate,
    star_23_implication_instantiate, star_23_implication_instantiate]
  rfl

/-- Left member of the pointwise equivalence at ✱23·4, built from the
two displayed implications. -/
def star_23_4_leftMatrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  star_23_conjunction negation disjunction
    (star_23_01_matrix negation disjunction relation₁ relation₂)
    (star_23_01_matrix negation disjunction relation₂ relation₁)

/-- Right member of ✱23·4, built independently from PM's printed
pointwise equivalence. -/
def star_23_4_rightMatrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  equivalence negation disjunction
    (star_23_relationMatrix relation₁)
    (star_23_relationMatrix relation₂)

/-- ✱4·01 shows that the independently built right member unfolds to the
left member; this equality is not used as the statement of ✱23·4. -/
theorem star_23_4_rightMatrix_unfold
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    star_23_4_rightMatrix negation disjunction relation₁ relation₂ =
      star_23_4_leftMatrix negation disjunction relation₁ relation₂ := rfl

/-- Full-scope two-sided matrix of ✱23·4. -/
def star_23_4_matrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  equivalence negation disjunction
    (star_23_4_leftMatrix negation disjunction relation₁ relation₂)
    (star_23_4_rightMatrix negation disjunction relation₁ relation₂)

private theorem star_23_4_matrix_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0))
    (x y : Term signature real [] .individual) :
    (star_23_4_matrix negation disjunction relation₁ relation₂).instantiate₂
        x y =
      star_4_01 negation disjunction
        (star_23_conjunction negation disjunction
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (implication negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₁ x y)))
        (star_4_01 negation disjunction
          (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)) := by
  unfold star_23_4_matrix star_23_4_leftMatrix star_23_4_rightMatrix
  rw [star_23_equivalence_instantiate,
    star_23_conjunction_instantiate,
    star_23_01_matrix_instantiate, star_23_01_matrix_instantiate,
    star_23_equivalence_instantiate,
    star_23_relationMatrix_instantiate, star_23_relationMatrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·4. -/
def star_23_4_reading
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:. R⪽S.S⪽R.≡:xRy.≡ₓ,y.xSy"
  scopeReading := "Both printed members are built independently inside one double-universal full scope."
  parsed := .assertion
    ((star_23_4_matrix negation disjunction relation₁ relation₂).always₂
      leftUniversal rightUniversal)

/-- ✱23·4, reconstructed from ✱4·2 after the two printed members are
built independently and ✱4·01 is unfolded.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_4
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    Derivation (.assertion
      ((star_23_4_matrix negation disjunction relation₁ relation₂).always₂
        leftUniversal rightUniversal)) := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_4_matrix negation disjunction relation₁
          relation₂).instantiate₂ x y := by
    intro x y
    rw [star_23_4_matrix_instantiate negation disjunction
      relation₁ relation₂ x y]
    change ⊢ᵣ star_4_01 negation disjunction
      (star_23_conjunction negation disjunction
        (implication negation disjunction (star_21_02 relation₁ x y)
          (star_21_02 relation₂ x y))
        (implication negation disjunction (star_21_02 relation₂ x y)
          (star_21_02 relation₁ x y)))
      (star_4_01 negation disjunction
        (star_21_02 relation₁ x y) (star_21_02 relation₂ x y))
    change ⊢ᵣ star_4_01 negation disjunction
      (star_4_01 negation disjunction
        (star_21_02 relation₁ x y) (star_21_02 relation₂ x y))
      (star_4_01 negation disjunction
        (star_21_02 relation₁ x y) (star_21_02 relation₂ x y))
    exact star_4_2 negation disjunction
      (star_4_01 negation disjunction
        (star_21_02 relation₁ x y) (star_21_02 relation₂ x y))
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_4_matrix negation disjunction relation₁ relation₂) line1
  exact line2

/-- Pointwise transitivity matrix of ✱23·44. -/
def star_23_44_matrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  implication negation disjunction
    (star_23_conjunction negation disjunction
      (star_23_01_matrix negation disjunction relation₁ relation₂)
      (star_23_01_matrix negation disjunction relation₂ relation₃))
    (star_23_01_matrix negation disjunction relation₁ relation₃)

private theorem star_23_44_matrix_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0))
    (x y : Term signature real [] .individual) :
    (star_23_44_matrix negation disjunction relation₁ relation₂
      relation₃).instantiate₂ x y =
      implication negation disjunction
        (conjunction negation disjunction
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (implication negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₃ x y)))
        (implication negation disjunction (star_21_02 relation₁ x y)
          (star_21_02 relation₃ x y)) := by
  unfold star_23_44_matrix
  rw [star_23_implication_instantiate,
    star_23_conjunction_instantiate,
    star_23_01_matrix_instantiate, star_23_01_matrix_instantiate,
    star_23_01_matrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·44. -/
def star_23_44_reading
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:R⪽S.S⪽T.⊃.R⪽T"
  scopeReading := "Both individual variables have the scope of the whole pointwise syllogism."
  parsed := .assertion
    ((star_23_44_matrix negation disjunction relation₁ relation₂
      relation₃).always₂ leftUniversal rightUniversal)

/-- ✱23·44, reconstructed pointwise by `Syll` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_44
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Derivation (.assertion
      ((star_23_44_matrix negation disjunction relation₁ relation₂
        relation₃).always₂ leftUniversal rightUniversal)) := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_44_matrix negation disjunction relation₁ relation₂
          relation₃).instantiate₂ x y := by
    intro x y
    rw [star_23_44_matrix_instantiate negation disjunction
      relation₁ relation₂ relation₃ x y]
    exact star_3_33 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)
      (star_21_02 relation₃ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_44_matrix negation disjunction relation₁ relation₂ relation₃)
    line1
  exact line2

/-- Pointwise projection matrix of ✱23·43. -/
def star_23_43_matrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  implication negation disjunction
    (star_23_02_matrix negation disjunction relation₁ relation₂)
    (star_23_relationMatrix relation₁)

private theorem star_23_43_matrix_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0))
    (x y : Term signature real [] .individual) :
    (star_23_43_matrix negation disjunction relation₁ relation₂).instantiate₂
        x y =
      implication negation disjunction
        (conjunction negation disjunction
          (star_21_02 relation₁ x y) (star_21_02 relation₂ x y))
        (star_21_02 relation₁ x y) := by
  unfold star_23_43_matrix star_23_02_matrix
  rw [star_23_implication_instantiate,
    star_23_conjunction_instantiate,
    star_23_relationMatrix_instantiate,
    star_23_relationMatrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·43. -/
def star_23_43_reading
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢.R∩̇S⪽R"
  scopeReading := "Both individual variables have the scope of the pointwise projection."
  parsed := .assertion
    ((star_23_43_matrix negation disjunction relation₁ relation₂).always₂
      leftUniversal rightUniversal)

/-- ✱23·43, reconstructed pointwise by `Simp` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_43
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ :
      Term signature real [] (relationSort resultOrder 0)) :
    Derivation (.assertion
      ((star_23_43_matrix negation disjunction relation₁ relation₂).always₂
        leftUniversal rightUniversal)) := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_43_matrix negation disjunction relation₁
          relation₂).instantiate₂ x y := by
    intro x y
    rw [star_23_43_matrix_instantiate negation disjunction
      relation₁ relation₂ x y]
    exact star_3_26 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_43_matrix negation disjunction relation₁ relation₂) line1
  exact line2

/-- Pointwise conjunction-of-consequents matrix of ✱23·45. -/
def star_23_45_matrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  implication negation disjunction
    (star_23_conjunction negation disjunction
      (star_23_01_matrix negation disjunction relation₁ relation₂)
      (star_23_01_matrix negation disjunction relation₁ relation₃))
    (implication negation disjunction
      (star_23_relationMatrix relation₁)
      (star_23_02_matrix negation disjunction relation₂ relation₃))

private theorem star_23_45_matrix_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0))
    (x y : Term signature real [] .individual) :
    (star_23_45_matrix negation disjunction relation₁ relation₂
      relation₃).instantiate₂ x y =
      implication negation disjunction
        (conjunction negation disjunction
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₃ x y)))
        (implication negation disjunction (star_21_02 relation₁ x y)
          (conjunction negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₃ x y))) := by
  unfold star_23_45_matrix star_23_02_matrix
  rw [star_23_implication_instantiate,
    star_23_conjunction_instantiate,
    star_23_01_matrix_instantiate, star_23_01_matrix_instantiate,
    star_23_implication_instantiate,
    star_23_relationMatrix_instantiate,
    star_23_conjunction_instantiate,
    star_23_relationMatrix_instantiate, star_23_relationMatrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·45. -/
def star_23_45_reading
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:R⪽S.R⪽T.⊃.R⪽S∩̇T"
  scopeReading := "Both individual variables have the scope of the whole pointwise implication."
  parsed := .assertion
    ((star_23_45_matrix negation disjunction relation₁ relation₂
      relation₃).always₂ leftUniversal rightUniversal)

/-- ✱23·45, reconstructed pointwise by `Fact` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_45
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Derivation (.assertion
      ((star_23_45_matrix negation disjunction relation₁ relation₂
        relation₃).always₂ leftUniversal rightUniversal)) := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_45_matrix negation disjunction relation₁ relation₂
          relation₃).instantiate₂ x y := by
    intro x y
    rw [star_23_45_matrix_instantiate negation disjunction
      relation₁ relation₂ relation₃ x y]
    exact star_3_43 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)
      (star_21_02 relation₃ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_45_matrix negation disjunction relation₁ relation₂ relation₃)
    line1
  exact line2

/-- Pointwise antecedent-weakening matrix of ✱23·47. -/
def star_23_47_matrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  implication negation disjunction
    (star_23_01_matrix negation disjunction relation₁ relation₃)
    (implication negation disjunction
      (star_23_02_matrix negation disjunction relation₁ relation₂)
      (star_23_relationMatrix relation₃))

private theorem star_23_47_matrix_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0))
    (x y : Term signature real [] .individual) :
    (star_23_47_matrix negation disjunction relation₁ relation₂
      relation₃).instantiate₂ x y =
      implication negation disjunction
        (implication negation disjunction (star_21_02 relation₁ x y)
          (star_21_02 relation₃ x y))
        (implication negation disjunction
          (conjunction negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (star_21_02 relation₃ x y)) := by
  unfold star_23_47_matrix star_23_02_matrix
  rw [star_23_implication_instantiate,
    star_23_01_matrix_instantiate,
    star_23_implication_instantiate,
    star_23_conjunction_instantiate,
    star_23_relationMatrix_instantiate, star_23_relationMatrix_instantiate,
    star_23_relationMatrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·47. -/
def star_23_47_reading
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:R⪽T.⊃.R∩̇S⪽T"
  scopeReading := "Both individual variables have the scope of antecedent weakening."
  parsed := .assertion
    ((star_23_47_matrix negation disjunction relation₁ relation₂
      relation₃).always₂ leftUniversal rightUniversal)

/-- ✱23·47, reconstructed pointwise by `Simp` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_47
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Derivation (.assertion
      ((star_23_47_matrix negation disjunction relation₁ relation₂
        relation₃).always₂ leftUniversal rightUniversal)) := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_47_matrix negation disjunction relation₁ relation₂
          relation₃).instantiate₂ x y := by
    intro x y
    rw [star_23_47_matrix_instantiate negation disjunction
      relation₁ relation₂ relation₃ x y]
    exact star_3_41 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)
      (star_21_02 relation₃ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_47_matrix negation disjunction relation₁ relation₂ relation₃)
    line1
  exact line2

/-- Pointwise intersection-monotonicity matrix of ✱23·48. -/
def star_23_48_matrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  implication negation disjunction
    (star_23_01_matrix negation disjunction relation₁ relation₂)
    (implication negation disjunction
      (star_23_02_matrix negation disjunction relation₁ relation₃)
      (star_23_02_matrix negation disjunction relation₂ relation₃))

private theorem star_23_48_matrix_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0))
    (x y : Term signature real [] .individual) :
    (star_23_48_matrix negation disjunction relation₁ relation₂
      relation₃).instantiate₂ x y =
      implication negation disjunction
        (implication negation disjunction (star_21_02 relation₁ x y)
          (star_21_02 relation₂ x y))
        (implication negation disjunction
          (conjunction negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₃ x y))
          (conjunction negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₃ x y))) := by
  unfold star_23_48_matrix star_23_02_matrix
  rw [star_23_implication_instantiate,
    star_23_01_matrix_instantiate,
    star_23_implication_instantiate,
    star_23_conjunction_instantiate, star_23_conjunction_instantiate,
    star_23_relationMatrix_instantiate, star_23_relationMatrix_instantiate,
    star_23_relationMatrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·48. -/
def star_23_48_reading
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:R⪽S.⊃.R∩̇T⪽S∩̇T"
  scopeReading := "Both individual variables have the scope of intersection monotonicity."
  parsed := .assertion
    ((star_23_48_matrix negation disjunction relation₁ relation₂
      relation₃).always₂ leftUniversal rightUniversal)

/-- ✱23·48, reconstructed pointwise by `Fact` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_48
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ :
      Term signature real [] (relationSort resultOrder 0)) :
    Derivation (.assertion
      ((star_23_48_matrix negation disjunction relation₁ relation₂
        relation₃).always₂ leftUniversal rightUniversal)) := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_48_matrix negation disjunction relation₁ relation₂
          relation₃).instantiate₂ x y := by
    intro x y
    rw [star_23_48_matrix_instantiate negation disjunction
      relation₁ relation₂ relation₃ x y]
    exact star_3_45 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)
      (star_21_02 relation₃ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_48_matrix negation disjunction relation₁ relation₂ relation₃)
    line1
  exact line2

/-- Pointwise binary intersection-monotonicity matrix of ✱23·49. -/
def star_23_49_matrix
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ relation₄ :
      Term signature real [] (relationSort resultOrder 0)) :
    Formula signature real [.individual, .individual] resultOrder :=
  implication negation disjunction
    (star_23_conjunction negation disjunction
      (star_23_01_matrix negation disjunction relation₁ relation₂)
      (star_23_01_matrix negation disjunction relation₃ relation₄))
    (implication negation disjunction
      (star_23_02_matrix negation disjunction relation₁ relation₃)
      (star_23_02_matrix negation disjunction relation₂ relation₄))

private theorem star_23_49_matrix_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ relation₄ :
      Term signature real [] (relationSort resultOrder 0))
    (x y : Term signature real [] .individual) :
    (star_23_49_matrix negation disjunction relation₁ relation₂
      relation₃ relation₄).instantiate₂ x y =
      implication negation disjunction
        (conjunction negation disjunction
          (implication negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₂ x y))
          (implication negation disjunction (star_21_02 relation₃ x y)
            (star_21_02 relation₄ x y)))
        (implication negation disjunction
          (conjunction negation disjunction (star_21_02 relation₁ x y)
            (star_21_02 relation₃ x y))
          (conjunction negation disjunction (star_21_02 relation₂ x y)
            (star_21_02 relation₄ x y))) := by
  unfold star_23_49_matrix star_23_02_matrix
  rw [star_23_implication_instantiate,
    star_23_conjunction_instantiate,
    star_23_01_matrix_instantiate, star_23_01_matrix_instantiate,
    star_23_implication_instantiate,
    star_23_conjunction_instantiate, star_23_conjunction_instantiate,
    star_23_relationMatrix_instantiate, star_23_relationMatrix_instantiate,
    star_23_relationMatrix_instantiate, star_23_relationMatrix_instantiate]
  rfl

/-- Audited full-scope reading of ✱23·49. -/
def star_23_49_reading
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ relation₄ :
      Term signature real [] (relationSort resultOrder 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:P⪽Q.R⪽S.⊃.P∩̇R⪽Q∩̇S"
  scopeReading := "Both individual variables have the scope of binary intersection monotonicity."
  parsed := .assertion
    ((star_23_49_matrix negation disjunction relation₁ relation₂
      relation₃ relation₄).always₂ leftUniversal rightUniversal)

/-- ✱23·49, reconstructed pointwise by `Fact` and ✱11·11.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_49
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (relation₁ relation₂ relation₃ relation₄ :
      Term signature real [] (relationSort resultOrder 0)) :
    Derivation (.assertion
      ((star_23_49_matrix negation disjunction relation₁ relation₂
        relation₃ relation₄).always₂ leftUniversal rightUniversal)) := by
  have line1 : ∀ x : Term signature real [] .individual,
      ∀ y : Term signature real [] .individual,
        ⊢ᵣ (star_23_49_matrix negation disjunction relation₁ relation₂
          relation₃ relation₄).instantiate₂ x y := by
    intro x y
    rw [star_23_49_matrix_instantiate negation disjunction
      relation₁ relation₂ relation₃ relation₄ x y]
    exact star_3_47 negation disjunction
      (star_21_02 relation₁ x y) (star_21_02 relation₃ x y)
      (star_21_02 relation₂ x y) (star_21_02 relation₄ x y)
  have line2 := star_11_11 leftUniversal rightUniversal
    (star_23_49_matrix negation disjunction relation₁ relation₂ relation₃
      relation₄) line1
  exact line2

/-- Transport a derivation along the computed equality of ramified orders. -/
private theorem star23_castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

/-- The exact positive-order specialization of relation inclusion at the two
displayed individuals. -/
private theorem star_23_01_successor_specialize
    (leftUniversal : signature.Universal .individual order.succ)
    (rightUniversal : signature.Universal .individual
      (bindOrder order.succ .individual))
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order.succ 0))
    (x y : Term signature real [] .individual) :
    ⊢ᵣ implication negation disjunction
      (star_23_01_successor leftUniversal rightUniversal negation disjunction
        relation₁ relation₂)
      (implication negation disjunction
        (star_21_02 relation₁ x y) (star_21_02 relation₂ x y)) := by
  let body := star_23_01_matrix negation disjunction relation₁ relation₂
  let closureEq := star23_doubleBindOrder_succ_individual order
  let resultEq := natMaxCongr closureEq rfl
  let rawNegation := Eq.mp
    (congrArg signature.Negation closureEq.symm) negation
  let rawDisjunction := Eq.mp
    (congrArg signature.Disjunction resultEq.symm) disjunction
  have line1 := star_11_1 leftUniversal rightUniversal rawNegation
    rawDisjunction body x y
  have line2 := star23_castAssertionOrder resultEq
    (star_11_1_formula leftUniversal rightUniversal rawNegation
      rawDisjunction body x y) line1
  have line3 := mixedImplication_normalizeSameOrder closureEq rfl
    negation disjunction (body.always₂ leftUniversal rightUniversal)
    (body.instantiate₂ x y)
  have line4 := Derivation.castAssertion line3.symm line2
  change ⊢ᵣ implication negation disjunction
    (star_23_01_successor leftUniversal rightUniversal negation disjunction
      relation₁ relation₂) (body.instantiate₂ x y) at line4
  rw [star_23_01_matrix_instantiate negation disjunction
    relation₁ relation₂ x y] at line4
  exact line4

/-- Exact scope reading of ✱23·441. -/
def star_23_441_reading
    (leftUniversal : signature.Universal .individual order.succ)
    (rightUniversal : signature.Universal .individual
      (bindOrder order.succ .individual))
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order.succ 0))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:R⪽S.xRy.⊃.xSy"
  scopeReading := "The closed inclusion and the apparent membership xRy form the antecedent; x and y are not universally closed."
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction
      (star_23_01_successor leftUniversal rightUniversal negation disjunction
        relation₁ relation₂)
      (star_21_02 relation₁ x y))
    (star_21_02 relation₂ x y))

/-- ✱23·441, reconstructed by specializing the closed inclusion and
applying the corresponding propositional implication.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_441
    (leftUniversal : signature.Universal .individual order.succ)
    (rightUniversal : signature.Universal .individual
      (bindOrder order.succ .individual))
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order.succ 0))
    (x y : Term signature real [] .individual) :
    Derivation (star_23_441_reading leftUniversal rightUniversal negation
      disjunction relation₁ relation₂ x y).parsed := by
  let inclusion := star_23_01_successor leftUniversal rightUniversal
    negation disjunction relation₁ relation₂
  let membership₁ := star_21_02 relation₁ x y
  let membership₂ := star_21_02 relation₂ x y
  have line1 : ⊢ᵣ implication negation disjunction inclusion
      (implication negation disjunction membership₁ membership₂) :=
    star_23_01_successor_specialize leftUniversal rightUniversal negation
      disjunction relation₁ relation₂ x y
  have line2 := star_3_31 negation disjunction inclusion membership₁ membership₂
  exact Derivation.star_9_12_same negation disjunction line1 line2

/-- Exact scope reading of ✱23·46. -/
def star_23_46_reading
    (leftUniversal : signature.Universal .individual order.succ)
    (rightUniversal : signature.Universal .individual
      (bindOrder order.succ .individual))
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order.succ 0))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢:xRy.R⪽S.⊃.xSy"
  scopeReading := "The apparent membership xRy and the closed inclusion form the antecedent; x and y are not universally closed."
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction
      (star_21_02 relation₁ x y)
      (star_23_01_successor leftUniversal rightUniversal negation disjunction
        relation₁ relation₂))
    (star_21_02 relation₂ x y))

/-- ✱23·46, reconstructed from ✱23·441 by propositional permutation.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_46
    (leftUniversal : signature.Universal .individual order.succ)
    (rightUniversal : signature.Universal .individual
      (bindOrder order.succ .individual))
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order.succ 0))
    (x y : Term signature real [] .individual) :
    Derivation (star_23_46_reading leftUniversal rightUniversal negation
      disjunction relation₁ relation₂ x y).parsed := by
  let inclusion := star_23_01_successor leftUniversal rightUniversal
    negation disjunction relation₁ relation₂
  let membership₁ := star_21_02 relation₁ x y
  let membership₂ := star_21_02 relation₂ x y
  have line1 : ⊢ᵣ implication negation disjunction
      (conjunction negation disjunction inclusion membership₁) membership₂ :=
    star_23_441 leftUniversal rightUniversal negation disjunction
      relation₁ relation₂ x y
  have line2 := star_3_22 negation disjunction membership₁ inclusion
  have line3 := star_2_05 negation disjunction
    (conjunction negation disjunction membership₁ inclusion)
    (conjunction negation disjunction inclusion membership₁) membership₂
  have line4 := Derivation.star_9_12_same negation disjunction line1 line3
  exact Derivation.star_9_12_same negation disjunction line2 line4

/-! ## Elimination of the three relation operations -/

/-- Vocabulary carried by the printed ✱21·3 route through reducibility. -/
structure Star23EliminationVocabulary (signature : Signature)
    (order : Nat) where
  abstractionExistential : ExistentialVocabulary signature
    (relationSort order 0)
    (max (bindOrder (bindOrder order .individual) .individual) order)
  reducibilityExistential : ExistentialVocabulary signature
    (relationSort order 0)
    (bindOrder (bindOrder order .individual) .individual)
  leftUniversal : signature.Universal .individual order
  rightUniversal : signature.Universal .individual
    (bindOrder order .individual)
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation
    (bindOrder (bindOrder order .individual) .individual)
  rightNegation : signature.Negation order
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder order .individual) .individual) order)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder order .individual) .individual) order)
  reducibilityOuterNegation : signature.Negation
    (bindOrder (bindOrder (bindOrder order .individual) .individual)
      (relationSort order 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder (bindOrder order .individual) .individual)
        (relationSort order 0))
      (bindOrder
        (max (bindOrder (bindOrder order .individual) .individual) order)
        (relationSort order 0)))
  finalNegation : signature.Negation
    (bindOrder
      (max (bindOrder (bindOrder order .individual) .individual) order)
      (relationSort order 0))
  finalDisjunction : signature.Disjunction
    (bindOrder
      (max (bindOrder (bindOrder order .individual) .individual) order)
      (relationSort order 0))

/-- The scope transport still assumed by the ✱21·3 elimination route.  It
discharges a derivation in the context extended by a predicative relation
representative into an implication from the corresponding reducibility
existential.  This is stronger than the object theorem ✱10·35. -/
def Star23Star10_35Hypothesis
    (vocabulary : Star23EliminationVocabulary signature order)
    (matrix : Formula signature real [.individual, .individual] order)
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
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        matrix x y)

/-- Apply the established ✱21·3 eliminator to a relation matrix. -/
private theorem eliminateRelationAbstraction
    (vocabulary : Star23EliminationVocabulary signature order)
    (matrix : Formula signature real [.individual, .individual] order)
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis :
      Star23Star10_35Hypothesis vocabulary matrix x y) :
    ⊢ᵣ star_21_3_formula vocabulary.abstractionExistential
      vocabulary.leftUniversal vocabulary.rightUniversal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      matrix x y := by
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction matrix x y star_10_35_hypothesis
  exact line1

/-- Audited scope reading of ✱23·33. -/
def star_23_33_reading
    (vocabulary : Star23EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ :x(R ∩̇ S)y .≡. xRy . xSy"
  scopeReading := "The incomplete intersection has the scope of the displayed relation-membership equivalence."
  parsed := .assertion (star_21_3_formula
    vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_23_02_matrix negation disjunction relation₁ relation₂) x y)

/-- ✱23·33, by ✱21·3 after unfolding ✱23·02.
The premise `star_10_35_hypothesis` is the named reducibility-scope rule
inherited from the current conditional reconstruction of ✱21·3.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_33
    (vocabulary : Star23EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star23Star10_35Hypothesis vocabulary
      (star_23_02_matrix negation disjunction relation₁ relation₂) x y) :
    Derivation (star_23_33_reading vocabulary negation disjunction
      relation₁ relation₂ x y).parsed := by
  have line1 := eliminateRelationAbstraction vocabulary
    (star_23_02_matrix negation disjunction relation₁ relation₂)
    x y star_10_35_hypothesis
  exact line1

/-- Audited scope reading of ✱23·34. -/
def star_23_34_reading
    (vocabulary : Star23EliminationVocabulary signature order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ :. x(R ⊍ S)y .≡: x R y .∨. x S y"
  scopeReading := "The incomplete sum has the scope of the displayed relation-membership equivalence."
  parsed := .assertion (star_21_3_formula
    vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_23_03_matrix disjunction relation₁ relation₂) x y)

/-- ✱23·34, by ✱21·3 after unfolding ✱23·03.
The premise `star_10_35_hypothesis` is the named reducibility-scope rule
inherited from the current conditional reconstruction of ✱21·3.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_34
    (vocabulary : Star23EliminationVocabulary signature order)
    (disjunction : signature.Disjunction order)
    (relation₁ relation₂ :
      Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star23Star10_35Hypothesis vocabulary
      (star_23_03_matrix disjunction relation₁ relation₂) x y) :
    Derivation (star_23_34_reading vocabulary disjunction
      relation₁ relation₂ x y).parsed := by
  have line1 := eliminateRelationAbstraction vocabulary
    (star_23_03_matrix disjunction relation₁ relation₂)
    x y star_10_35_hypothesis
  exact line1

/-- Audited scope reading of ✱23·35. -/
def star_23_35_reading
    (vocabulary : Star23EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (relation : Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : x ∸R y .≡. ∼(x R y)"
  scopeReading := "The incomplete complement has the scope of the displayed relation-membership equivalence."
  parsed := .assertion (star_21_3_formula
    vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_23_04_matrix negation relation) x y)

/-- ✱23·35, by ✱21·3 after unfolding ✱23·04.
The premise `star_10_35_hypothesis` is the named reducibility-scope rule
inherited from the current conditional reconstruction of ✱21·3.
`direct_assumptions: PM1:REDUCIBILITY`.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_23_35
    (vocabulary : Star23EliminationVocabulary signature order)
    (negation : signature.Negation order)
    (relation : Term signature real [] (relationSort order 0))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star23Star10_35Hypothesis vocabulary
      (star_23_04_matrix negation relation) x y) :
    Derivation (star_23_35_reading vocabulary negation relation x y).parsed := by
  have line1 := eliminateRelationAbstraction vocabulary
    (star_23_04_matrix negation relation) x y star_10_35_hypothesis
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_23_1
#print axioms PM.RamifiedSyntax.star_23_2
#print axioms PM.RamifiedSyntax.star_23_3
#print axioms PM.RamifiedSyntax.star_23_31
#print axioms PM.RamifiedSyntax.star_23_32
#print axioms PM.RamifiedSyntax.star_23_42
#print axioms PM.RamifiedSyntax.star_23_4_rightMatrix_unfold
#print axioms PM.RamifiedSyntax.star_23_4
#print axioms PM.RamifiedSyntax.star_23_43
#print axioms PM.RamifiedSyntax.star_23_44
#print axioms PM.RamifiedSyntax.star_23_45
#print axioms PM.RamifiedSyntax.star_23_441
#print axioms PM.RamifiedSyntax.star_23_46
#print axioms PM.RamifiedSyntax.star_23_47
#print axioms PM.RamifiedSyntax.star_23_48
#print axioms PM.RamifiedSyntax.star_23_49
#print axioms PM.RamifiedSyntax.star_23_33
#print axioms PM.RamifiedSyntax.star_23_34
#print axioms PM.RamifiedSyntax.star_23_35
#print axioms PM.RamifiedSyntax.star_23_01_unfold
#print axioms PM.RamifiedSyntax.star_23_02_unfold
#print axioms PM.RamifiedSyntax.star_23_03_unfold
#print axioms PM.RamifiedSyntax.star_23_04_unfold
#print axioms PM.RamifiedSyntax.star_23_05_unfold
