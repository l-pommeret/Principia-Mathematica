import Principia.Syntax.Ramified
import Principia.Syntax.RamifiedReading
import Principia.Deduction.Star4Ramified
import Principia.FirstEdition.Volume1.Star30Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱30

Descriptive functions remain contextual: no description-valued `Term` is
introduced.  The unconditional results below are the direct ✱4·2 and ✱14
instances printed by PM for ✱30·1, ✱30·11, and ✱30·2.  The other propositions
still require the corresponding derived theorems of ✱14.
-/

/-- The ✱14·01 vocabulary needed to eliminate one descriptive-function
application.  Grouping it here keeps ✱30·01 contextual: no description-valued
term is introduced. -/
structure Star30DescriptionVocabulary (signature : Signature) (sort : RSort)
    (identityBaseOrder identityExcess scopeOrder : Nat) where
  existential : ExistentialVocabulary signature sort
    (max (bindOrder (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder)
  universal : signature.Universal sort (bindOrder identityBaseOrder
    (.function [sort] identityBaseOrder identityExcess))
  identity : IdentityVocabulary signature sort identityBaseOrder identityExcess
  equivalenceNegation : signature.Negation (bindOrder identityBaseOrder
    (.function [sort] identityBaseOrder identityExcess))
  equivalenceDisjunction : signature.Disjunction (bindOrder identityBaseOrder
    (.function [sort] identityBaseOrder identityExcess))
  leftNegation : signature.Negation (bindOrder (bindOrder identityBaseOrder
    (.function [sort] identityBaseOrder identityExcess)) sort)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder)

/-- ✱30·01: `Rʻy` is the contextual description `(℩x)(xRy)`, eliminated
by the exact ✱14·01 expansion. -/
def star_30_01
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort) :=
  star_14_01 vocabulary.existential vocabulary.universal vocabulary.identity
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction condition continuation

theorem star_30_01_unfold
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    star_30_01 vocabulary condition continuation =
      star_14_01 vocabulary.existential vocabulary.universal vocabulary.identity
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction condition continuation := rfl

/-- ✱30·02: `RʻSʻy` is `Rʻ(Sʻy)`.  Since descriptions are incomplete
symbols, this is the ✱30·01 expansion for `Sʻy` whose continuation is the
✱30·01 expansion for `Rʻc`; `c` is the outer apparent candidate. -/
def star_30_02
    (innerVocabulary : Star30DescriptionVocabulary signature sort
      innerIdentityBaseOrder innerIdentityExcess
      (bindOrder
        (max (bindOrder (bindOrder outerIdentityBaseOrder
          (.function [sort] outerIdentityBaseOrder outerIdentityExcess)) sort)
          continuationOrder) sort))
    (outerVocabulary : Star30DescriptionVocabulary signature sort
      outerIdentityBaseOrder outerIdentityExcess continuationOrder)
    (innerCondition : Formula signature real (sort :: apparent)
      (bindOrder innerIdentityBaseOrder
        (.function [sort] innerIdentityBaseOrder innerIdentityExcess)))
    (outerCondition : Formula signature real (sort :: sort :: apparent)
      (bindOrder outerIdentityBaseOrder
        (.function [sort] outerIdentityBaseOrder outerIdentityExcess)))
    (continuation : Formula signature real
      (sort :: sort :: apparent) continuationOrder) :=
  star_30_01 innerVocabulary innerCondition
    (star_30_01 outerVocabulary outerCondition continuation)

theorem star_30_02_unfold
    (innerVocabulary : Star30DescriptionVocabulary signature sort
      innerIdentityBaseOrder innerIdentityExcess
      (bindOrder
        (max (bindOrder (bindOrder outerIdentityBaseOrder
          (.function [sort] outerIdentityBaseOrder outerIdentityExcess)) sort)
          continuationOrder) sort))
    (outerVocabulary : Star30DescriptionVocabulary signature sort
      outerIdentityBaseOrder outerIdentityExcess continuationOrder)
    (innerCondition : Formula signature real (sort :: apparent)
      (bindOrder innerIdentityBaseOrder
        (.function [sort] innerIdentityBaseOrder innerIdentityExcess)))
    (outerCondition : Formula signature real (sort :: sort :: apparent)
      (bindOrder outerIdentityBaseOrder
        (.function [sort] outerIdentityBaseOrder outerIdentityExcess)))
    (continuation : Formula signature real
      (sort :: sort :: apparent) continuationOrder) :
    star_30_02 innerVocabulary outerVocabulary innerCondition outerCondition
        continuation =
      star_30_01 innerVocabulary innerCondition
        (star_30_01 outerVocabulary outerCondition continuation) := rfl

/-- Printed left member of ✱30·1, constructed from the descriptive-function
definition ✱30·01. -/
def star_30_1_left
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort) :=
  star_30_01 vocabulary condition continuation

/-- Printed right member of ✱30·1, constructed independently from the
description `(℩x)(xRy)` by ✱14·01. -/
def star_30_1_right
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort) :=
  star_14_01 vocabulary.existential vocabulary.universal vocabulary.identity
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction condition continuation

theorem star_30_1_left_unfold
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    star_30_1_left vocabulary condition continuation =
      star_30_01 vocabulary condition continuation := rfl

theorem star_30_1_right_unfold
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    star_30_1_right vocabulary condition continuation =
      star_14_01 vocabulary.existential vocabulary.universal vocabulary.identity
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction condition continuation := rfl

/-- Audited scope reading of ✱30·1. -/
def star_30_1_reading
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real [sort]
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real [sort] scopeOrder)
    (negation : signature.Negation
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort))
    (disjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱30·1. ⊢:[Rʻy].f(Rʻy).≡.[(℩x)(xRy)].f(℩x)(xRy) [*4·2.(*30·01)]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_30_1_left vocabulary condition continuation)
    (star_30_1_right vocabulary condition continuation))
  scopeReading := "The left member unfolds by ✱30·01; the independently built right member unfolds by ✱14·01."

/-- ✱30·1, exactly the printed ✱4·2 instance after unfolding ✱30·01.
`demonstration_provenance: follows-printed`. -/
theorem star_30_1
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real [sort]
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real [sort] scopeOrder)
    (negation : signature.Negation
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort))
    (disjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort)) :
    Derivation (star_30_1_reading vocabulary condition continuation
      negation disjunction).parsed := by
  have line1 := star_4_2 negation disjunction
    (star_14_01 vocabulary.existential vocabulary.universal vocabulary.identity
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction condition continuation)
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_30_1_left vocabulary condition continuation)
    (star_30_1_right vocabulary condition continuation)))
  rw [star_30_1_left_unfold, star_30_01_unfold,
    star_30_1_right_unfold]
  exact line1

/-- The right member printed at ✱30·11, built directly as the existential
✱14·01 expansion rather than being identified with the left member. -/
def star_30_11_right
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort) :=
  let x : Term signature real (sort :: sort :: apparent) sort := .apparent .zero
  let b : Term signature real (sort :: sort :: apparent) sort :=
    .apparent (.succ .zero)
  let conditionUnderB := condition.rename (liftRenaming (fun v => .succ v))
  Formula.sometimes vocabulary.existential
    (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.always vocabulary.universal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction conditionUnderB
          (star_13_01 vocabulary.identity x b)))
      continuation)

theorem star_30_11_right_unfold
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real (sort :: apparent) scopeOrder) :
    star_30_11_right vocabulary condition continuation =
      Formula.sometimes vocabulary.existential
        (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
          vocabulary.outerNegation vocabulary.conjunctionDisjunction
          (.always vocabulary.universal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (condition.rename (liftRenaming (fun v => .succ v)))
              (star_13_01 vocabulary.identity (.apparent .zero)
                (.apparent (.succ .zero)))))
          continuation) := rfl

/-- Audited scope reading of ✱30·11. -/
def star_30_11_reading
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real [sort]
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real [sort] scopeOrder)
    (negation : signature.Negation
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort))
    (disjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱30·11. ⊢:.[Rʻy].f(Rʻy).≡:(∃ b):xRy.≡ₓ.x=b:fb [*30·1.*14·1]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_30_1_left vocabulary condition continuation)
    (star_30_11_right vocabulary condition continuation))
  scopeReading := "The left member unfolds through ✱30·01; the right member is independently constructed from the printed existential matrix."

/-- ✱30·11, by the printed ✱30·1 step and contextual expansion ✱14·1.
`demonstration_provenance: follows-printed`. -/
theorem star_30_11
    (vocabulary : Star30DescriptionVocabulary signature sort
      identityBaseOrder identityExcess scopeOrder)
    (condition : Formula signature real [sort]
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature real [sort] scopeOrder)
    (negation : signature.Negation
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort))
    (disjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort)) :
    Derivation (star_30_11_reading vocabulary condition continuation
      negation disjunction).parsed := by
  have line1 := star_4_2 negation disjunction
    (star_30_11_right vocabulary condition continuation)
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_30_1_left vocabulary condition continuation)
    (star_30_11_right vocabulary condition continuation)))
  rw [star_30_1_left_unfold, star_30_01_unfold,
    star_14_01_unfold, star_30_11_right_unfold]
  exact line1

/-- Printed left member `E!Rʻy`, obtained from the definition ✱14·02. -/
def star_30_2_left
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder) :
    Formula signature real [] (bindOrder matrixOrder sort) :=
  star_14_02 existential relationMatrix

/-- Printed right member of ✱30·2, constructed directly as the displayed
existential uniqueness matrix. -/
def star_30_2_right
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder) :
    Formula signature real [] (bindOrder matrixOrder sort) :=
  Formula.sometimes existential relationMatrix

theorem star_30_2_left_unfold
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder) :
    star_30_2_left existential relationMatrix =
      Formula.sometimes existential relationMatrix := rfl

theorem star_30_2_right_unfold
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder) :
    star_30_2_right existential relationMatrix =
      Formula.sometimes existential relationMatrix := rfl

/-- Audited scope reading of ✱30·2. -/
def star_30_2_reading
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder sort))
    (disjunction : signature.Disjunction (bindOrder matrixOrder sort)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱30·2. ⊢:.E!Rʻy.≡:(∃ b):xRy.≡ₓ.x=b [*4·2.*14·11.(*30·01)]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_30_2_left existential relationMatrix)
    (star_30_2_right existential relationMatrix))
  scopeReading := "The left member unfolds by ✱14·02; the right member is independently built from the printed existential."

/-- ✱30·2, by the printed instance of ✱14·11 (whose proof is ✱4·2),
after unfolding the eliminable definition ✱30·01.
`demonstration_provenance: follows-printed`. -/
theorem star_30_2
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder sort))
    (disjunction : signature.Disjunction (bindOrder matrixOrder sort)) :
    Derivation (star_30_2_reading existential relationMatrix
      negation disjunction).parsed := by
  have line1 := star_4_2 negation disjunction
    (.sometimes existential relationMatrix)
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_30_2_left existential relationMatrix)
    (star_30_2_right existential relationMatrix)))
  rw [star_30_2_left_unfold, star_30_2_right_unfold]
  exact line1

/-! ## ✱30·3 and ✱30·31: the two members, and the step that is missing

PM prints

    ✱30·3.  ⊢:. x=Rʻy.≡:zRy.≡z.z=x
    ✱30·31. ⊢:. x=Rʻy.≡:xRy:zRy.⊃z.z=x

`Rʻy` is not a term.  By ✱30·01 it is the description `(℩z)(zRy)`, so the
member `x = Rʻy` is the ✱14·01 scope of that description whose continuation is
PM's identity `x = b` between the free `x` and the description candidate `b`.
The right members are built below from their own printed forms.  The step
joining them is ✱14·202, whose printed demonstration is `✱14·1` then `✱13·195`;
`star_13_195` is still conditional on `star_13_195_hypothesis`, so ✱14·202 has
no unconditional derivation here and no theorem `star_30_3` is declared. -/

/-- The order ✱13·01 assigns to `x = b` at `sort`.  ✱14·01 forces the
condition of a description over `sort` to carry exactly this order, so the
printed condition `zRy` of `Rʻy` is applied at it. -/
abbrev star_30_identityOrder (sort : RSort)
    (identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder identityBaseOrder (.function [sort] identityBaseOrder identityExcess)

/-- The sort of `R` in `Rʻy`: a two-place predicative function whose result
order is the one ✱14·01 forces on the description condition. -/
abbrev star_30_relationSort (sort : RSort)
    (identityBaseOrder identityExcess : Nat) : RSort :=
  .function [sort, sort]
    (star_30_identityOrder sort identityBaseOrder identityExcess) 0

/-- Order of the printed member `x = Rʻy` once ✱30·01 and ✱14·01 are
eliminated. -/
abbrev star_30_3_leftOrder (sort : RSort)
    (identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder
    (max (bindOrder (star_30_identityOrder sort identityBaseOrder identityExcess)
      sort) (star_30_identityOrder sort identityBaseOrder identityExcess)) sort

/-- Order of the printed member `zRy .≡z. z=x`. -/
abbrev star_30_3_rightOrder (sort : RSort)
    (identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder (star_30_identityOrder sort identityBaseOrder identityExcess) sort

/-- Order of the printed member `xRy : zRy .⊃z. z=x`. -/
abbrev star_30_31_rightOrder (sort : RSort)
    (identityBaseOrder identityExcess : Nat) : Nat :=
  max (star_30_identityOrder sort identityBaseOrder identityExcess)
    (star_30_3_rightOrder sort identityBaseOrder identityExcess)

/-- `zRy`: the printed condition of the description `(℩z)(zRy)` that ✱30·01
substitutes for `Rʻy`.  The described variable `z` is the head apparent
variable, exactly where ✱14·01 expects it. -/
def star_30_descriptionCondition
    (relation : Term signature real apparent
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (y : Term signature real apparent sort) :
    Formula signature real (sort :: apparent)
      (star_30_identityOrder sort identityBaseOrder identityExcess) :=
  applyBinary relation.weaken (.apparent .zero) y.weaken

theorem star_30_descriptionCondition_unfold
    (relation : Term signature real apparent
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (y : Term signature real apparent sort) :
    star_30_descriptionCondition relation y =
      applyBinary relation.weaken (.apparent .zero) y.weaken := rfl

/-- Every logical meaning the printed members of ✱30·3 and ✱30·31 need, at the
orders ✱13·01 and ✱14·01 force on them. -/
structure Star30_3Vocabulary (signature : Signature) (sort : RSort)
    (identityBaseOrder identityExcess : Nat) where
  description : Star30DescriptionVocabulary signature sort identityBaseOrder
    identityExcess (star_30_identityOrder sort identityBaseOrder identityExcess)
  universal : signature.Universal sort
    (star_30_identityOrder sort identityBaseOrder identityExcess)
  equivalenceNegation : signature.Negation
    (star_30_identityOrder sort identityBaseOrder identityExcess)
  equivalenceDisjunction : signature.Disjunction
    (star_30_identityOrder sort identityBaseOrder identityExcess)
  leftNegation : signature.Negation
    (star_30_3_leftOrder sort identityBaseOrder identityExcess)
  rightNegation : signature.Negation
    (star_30_3_rightOrder sort identityBaseOrder identityExcess)
  forwardNegation : signature.Negation
    (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
      (star_30_3_rightOrder sort identityBaseOrder identityExcess))
  backwardNegation : signature.Negation
    (max (star_30_3_rightOrder sort identityBaseOrder identityExcess)
      (star_30_3_leftOrder sort identityBaseOrder identityExcess))
  forwardDisjunction : signature.Disjunction
    (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
      (star_30_3_rightOrder sort identityBaseOrder identityExcess))
  backwardDisjunction : signature.Disjunction
    (max (star_30_3_rightOrder sort identityBaseOrder identityExcess)
      (star_30_3_leftOrder sort identityBaseOrder identityExcess))
  outerNegation : signature.Negation
    (max (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
        (star_30_3_rightOrder sort identityBaseOrder identityExcess))
      (max (star_30_3_rightOrder sort identityBaseOrder identityExcess)
        (star_30_3_leftOrder sort identityBaseOrder identityExcess)))
  outerDisjunction : signature.Disjunction
    (max (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
        (star_30_3_rightOrder sort identityBaseOrder identityExcess))
      (max (star_30_3_rightOrder sort identityBaseOrder identityExcess)
        (star_30_3_leftOrder sort identityBaseOrder identityExcess)))

/-- ✱4·01 between two members carrying independently assigned orders.  PM's
typical ambiguity permits this; `equivalence` is only its same-order case, and
the two members of ✱30·3 do not share an order. -/
def star_30_mixedEquivalence
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (forwardNegation : signature.Negation (max leftOrder rightOrder))
    (backwardNegation : signature.Negation (max rightOrder leftOrder))
    (forwardDisjunction : signature.Disjunction (max leftOrder rightOrder))
    (backwardDisjunction : signature.Disjunction (max rightOrder leftOrder))
    (outerNegation : signature.Negation
      (max (max leftOrder rightOrder) (max rightOrder leftOrder)))
    (outerDisjunction : signature.Disjunction
      (max (max leftOrder rightOrder) (max rightOrder leftOrder)))
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    Formula signature real apparent
      (max (max leftOrder rightOrder) (max rightOrder leftOrder)) :=
  mixedConjunction forwardNegation backwardNegation outerNegation
    outerDisjunction
    (mixedImplication leftNegation forwardDisjunction left right)
    (mixedImplication rightNegation backwardDisjunction right left)

theorem star_30_mixedEquivalence_unfold
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (forwardNegation : signature.Negation (max leftOrder rightOrder))
    (backwardNegation : signature.Negation (max rightOrder leftOrder))
    (forwardDisjunction : signature.Disjunction (max leftOrder rightOrder))
    (backwardDisjunction : signature.Disjunction (max rightOrder leftOrder))
    (outerNegation : signature.Negation
      (max (max leftOrder rightOrder) (max rightOrder leftOrder)))
    (outerDisjunction : signature.Disjunction
      (max (max leftOrder rightOrder) (max rightOrder leftOrder)))
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    star_30_mixedEquivalence leftNegation rightNegation forwardNegation
        backwardNegation forwardDisjunction backwardDisjunction outerNegation
        outerDisjunction left right =
      mixedConjunction forwardNegation backwardNegation outerNegation
        outerDisjunction
        (mixedImplication leftNegation forwardDisjunction left right)
        (mixedImplication rightNegation backwardDisjunction right left) := rfl

/-- Printed left member of ✱30·3 and of ✱30·31, `x = Rʻy`.  ✱30·01 replaces
`Rʻy` by the description `(℩z)(zRy)`; its ✱14·01 scope carries PM's identity
`x = b` as continuation, and no description-valued `Term` is formed. -/
def star_30_3_left
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    Formula signature real []
      (star_30_3_leftOrder sort identityBaseOrder identityExcess) :=
  star_30_01 vocabulary.description
    (star_30_descriptionCondition relation y)
    (star_13_01 vocabulary.description.identity x.weaken (.apparent .zero))

theorem star_30_3_left_unfold
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    star_30_3_left vocabulary relation x y =
      star_30_01 vocabulary.description
        (star_30_descriptionCondition relation y)
        (star_13_01 vocabulary.description.identity x.weaken
          (.apparent .zero)) := rfl

/-- Printed right member of ✱30·3, `zRy .≡z. z = x`: the universal closure of
the equivalence between the printed condition and PM's identity `z = x`.  It is
built from its own printed form and carries no existential. -/
def star_30_3_right
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    Formula signature real []
      (star_30_3_rightOrder sort identityBaseOrder identityExcess) :=
  .always vocabulary.universal
    (equivalence vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      (star_30_descriptionCondition relation y)
      (star_13_01 vocabulary.description.identity (.apparent .zero) x.weaken))

theorem star_30_3_right_unfold
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    star_30_3_right vocabulary relation x y =
      .always vocabulary.universal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (star_30_descriptionCondition relation y)
          (star_13_01 vocabulary.description.identity (.apparent .zero)
            x.weaken)) := rfl

/-- Audited scope reading of ✱30·3.  No `Derivation` of this claim is
declared: see `Star30DescriptionIdentityStep`. -/
def star_30_3_reading
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱30·3. ⊢:. x=Rʻy.≡:zRy.≡z.z=x"
  parsed := .assertion (star_30_mixedEquivalence vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.forwardNegation
    vocabulary.backwardNegation vocabulary.forwardDisjunction
    vocabulary.backwardDisjunction vocabulary.outerNegation
    vocabulary.outerDisjunction
    (star_30_3_left vocabulary relation x y)
    (star_30_3_right vocabulary relation x y))
  scopeReading := "The left member is the ✱30·01 description scope of `(℩z)(zRy)` over the identity `x = b`; the right member is the independently built universal equivalence `zRy .≡z. z = x`. The two members carry different assigned orders, so ✱4·01 is taken at independent orders."

/-- The exact rule separating the two printed members of ✱30·3.  It is PM's
✱14·202, printed with the demonstration `✱14·1` then `✱13·195`.  After ✱30·01
and ✱14·01 the left member is `.neg` rooted — the ✱10·01 expansion of `(∃b)`
— over `.always`, while the right member is `.always` rooted over
`equivalence`; nothing unfolds one into the other, and the bridge is exactly
✱13·195, which `Star13Derived` still leaves conditional on
`star_13_195_hypothesis`.  This structure names the debt.  It has no
inhabitant, and no numbered PM proposition is asserted here. -/
structure Star30DescriptionIdentityStep
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) : Prop where
  derive : Derivation (star_30_3_reading vocabulary relation x y).parsed

/-- Printed right member of ✱30·31, `xRy : zRy .⊃z. z = x`: the product of the
printed atomic condition at `x` and the universally closed implication.  Both
factors are built from their own printed forms. -/
def star_30_31_right
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (productNegation : signature.Negation
      (star_30_identityOrder sort identityBaseOrder identityExcess))
    (productOuterNegation : signature.Negation
      (star_30_31_rightOrder sort identityBaseOrder identityExcess))
    (productDisjunction : signature.Disjunction
      (star_30_31_rightOrder sort identityBaseOrder identityExcess))
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    Formula signature real []
      (star_30_31_rightOrder sort identityBaseOrder identityExcess) :=
  mixedConjunction productNegation vocabulary.rightNegation
    productOuterNegation productDisjunction
    (applyBinary relation x y)
    (.always vocabulary.universal
      (implication vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction
        (star_30_descriptionCondition relation y)
        (star_13_01 vocabulary.description.identity (.apparent .zero)
          x.weaken)))

theorem star_30_31_right_unfold
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (productNegation : signature.Negation
      (star_30_identityOrder sort identityBaseOrder identityExcess))
    (productOuterNegation : signature.Negation
      (star_30_31_rightOrder sort identityBaseOrder identityExcess))
    (productDisjunction : signature.Disjunction
      (star_30_31_rightOrder sort identityBaseOrder identityExcess))
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    star_30_31_right vocabulary productNegation productOuterNegation
        productDisjunction relation x y =
      mixedConjunction productNegation vocabulary.rightNegation
        productOuterNegation productDisjunction
        (applyBinary relation x y)
        (.always vocabulary.universal
          (implication vocabulary.equivalenceNegation
            vocabulary.equivalenceDisjunction
            (star_30_descriptionCondition relation y)
            (star_13_01 vocabulary.description.identity (.apparent .zero)
              x.weaken))) := rfl

/-- Audited scope reading of ✱30·31.  Its left member is the same printed
`x = Rʻy` as at ✱30·3, so `star_30_3_left` is reused; the right member is the
printed product.  No `Derivation` of this claim is declared: the step from one
member to the other is again ✱14·202. -/
def star_30_31_reading
    (vocabulary : Star30_3Vocabulary signature sort
      identityBaseOrder identityExcess)
    (productNegation : signature.Negation
      (star_30_identityOrder sort identityBaseOrder identityExcess))
    (productOuterNegation : signature.Negation
      (star_30_31_rightOrder sort identityBaseOrder identityExcess))
    (productDisjunction : signature.Disjunction
      (star_30_31_rightOrder sort identityBaseOrder identityExcess))
    (forwardNegation : signature.Negation
      (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
        (star_30_31_rightOrder sort identityBaseOrder identityExcess)))
    (backwardNegation : signature.Negation
      (max (star_30_31_rightOrder sort identityBaseOrder identityExcess)
        (star_30_3_leftOrder sort identityBaseOrder identityExcess)))
    (forwardDisjunction : signature.Disjunction
      (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
        (star_30_31_rightOrder sort identityBaseOrder identityExcess)))
    (backwardDisjunction : signature.Disjunction
      (max (star_30_31_rightOrder sort identityBaseOrder identityExcess)
        (star_30_3_leftOrder sort identityBaseOrder identityExcess)))
    (outerNegation : signature.Negation
      (max (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
          (star_30_31_rightOrder sort identityBaseOrder identityExcess))
        (max (star_30_31_rightOrder sort identityBaseOrder identityExcess)
          (star_30_3_leftOrder sort identityBaseOrder identityExcess))))
    (outerDisjunction : signature.Disjunction
      (max (max (star_30_3_leftOrder sort identityBaseOrder identityExcess)
          (star_30_31_rightOrder sort identityBaseOrder identityExcess))
        (max (star_30_31_rightOrder sort identityBaseOrder identityExcess)
          (star_30_3_leftOrder sort identityBaseOrder identityExcess))))
    (relation : Term signature real []
      (star_30_relationSort sort identityBaseOrder identityExcess))
    (x y : Term signature real [] sort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱30·31. ⊢:. x=Rʻy.≡:xRy:zRy.⊃z.z=x"
  parsed := .assertion (star_30_mixedEquivalence vocabulary.leftNegation
    productOuterNegation forwardNegation backwardNegation forwardDisjunction
    backwardDisjunction outerNegation outerDisjunction
    (star_30_3_left vocabulary relation x y)
    (star_30_31_right vocabulary productNegation productOuterNegation
      productDisjunction relation x y))
  scopeReading := "The left member is the ✱30·01 description scope of `(℩z)(zRy)` over the identity `x = b`; the right member is the independently built product of `xRy` with the universally closed implication `zRy .⊃z. z = x`."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_30_01_unfold
#print axioms PM.RamifiedSyntax.star_30_02_unfold
#print axioms PM.RamifiedSyntax.star_30_1_left_unfold
#print axioms PM.RamifiedSyntax.star_30_1_right_unfold
#print axioms PM.RamifiedSyntax.star_30_11_right_unfold
#print axioms PM.RamifiedSyntax.star_30_2_left_unfold
#print axioms PM.RamifiedSyntax.star_30_2_right_unfold
#print axioms PM.RamifiedSyntax.star_30_2
#print axioms PM.RamifiedSyntax.star_30_1
#print axioms PM.RamifiedSyntax.star_30_11
#print axioms PM.RamifiedSyntax.star_30_descriptionCondition_unfold
#print axioms PM.RamifiedSyntax.star_30_mixedEquivalence_unfold
#print axioms PM.RamifiedSyntax.star_30_3_left_unfold
#print axioms PM.RamifiedSyntax.star_30_3_right_unfold
#print axioms PM.RamifiedSyntax.star_30_31_right_unfold
