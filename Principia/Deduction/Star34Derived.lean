import Principia.Deduction.Star33Derived
import Principia.FirstEdition.Volume1.Star34Source

namespace PM.RamifiedSyntax

/-! # PM I, ✱34 — relative product -/

/-- Conjunction at one ramified order, PM's ✱3·01 abbreviation. -/
private def star34Conjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation (sameDisjunction disjunction
    (.neg negation left) (.neg negation right))

/-- The matrix `(∃y).xRy.ySz` in the definition ✱34·01.

This is the eliminable application of `R|S` to `x,z`.  The relation
abstraction itself remains contextual, as required by ✱21·01. -/
def star_34_01
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (left : Term signature real apparent
      (relationSort relationOrder leftExcess))
    (right : Term signature real apparent
      (relationSort relationOrder rightExcess))
    (x z : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  .sometimes existential
    (star34Conjunction negation disjunction
      (applyBinary left.weaken x.weaken (.apparent .zero))
      (applyBinary right.weaken (.apparent .zero) z.weaken))

theorem star_34_01_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (left : Term signature real apparent
      (relationSort relationOrder leftExcess))
    (right : Term signature real apparent
      (relationSort relationOrder rightExcess))
    (x z : Term signature real apparent .individual) :
    star_34_01 existential negation disjunction left right x z =
      .sometimes existential
        (.neg negation (sameDisjunction disjunction
          (.neg negation
            (applyBinary left.weaken x.weaken (.apparent .zero)))
          (.neg negation
            (applyBinary right.weaken (.apparent .zero) z.weaken)))) := rfl

/-- The eliminable application `xR²z` from the definition ✱34·02. -/
def star_34_02
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x z : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  star_34_01 existential negation disjunction relation relation x z

theorem star_34_02_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x z : Term signature real apparent .individual) :
    star_34_02 existential negation disjunction relation x z =
      .sometimes existential
        (.neg negation (sameDisjunction disjunction
          (.neg negation
            (applyBinary relation.weaken x.weaken (.apparent .zero)))
          (.neg negation
            (applyBinary relation.weaken (.apparent .zero) z.weaken)))) := rfl

/-- The eliminable application `xR³z` from the definition ✱34·03. -/
def star_34_03
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (square relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x z : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  star_34_01 existential negation disjunction square relation x z

theorem star_34_03_unfold
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (square relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x z : Term signature real apparent .individual) :
    star_34_03 existential negation disjunction square relation x z =
      .sometimes existential
        (.neg negation (sameDisjunction disjunction
          (.neg negation
            (applyBinary square.weaken x.weaken (.apparent .zero)))
          (.neg negation
            (applyBinary relation.weaken (.apparent .zero) z.weaken)))) := rfl

/-! ## What ✱34·1 to ✱34·2 reaches, and what it does not

✱34·1 and ✱34·5 below are the ✱21·3 eliminations; they keep the named
reducibility-scope premise.  Of the three remaining propositions in that range
none can be closed here, and the obstruction is different in each case.

* ✱34·11, `x(R| S)z .≡. ∃ !(R⃖ʻx∩ S⃗ʻz)`.  The right member is built from the
  descriptive relations `R⃖` and `R⃗` of ✱32·01–·02, which are contextual class
  abstractions.  Their elimination is ✱20·3/✱21·3, and
  `Principia/Deduction/Star32Derived.lean` declares no theorem for exactly that
  reason.  The obstruction is therefore inherited, not local to ✱34.

* ✱34·12, `R| S=x̂ẑ{∃ !(R⃖ʻx∩ S⃗ʻx)}`, adds to ✱34·11 the passage from an
  equivalence of applications to an identity of relations, which is ✱21·33 with
  ✱21·43; both rest on ✱21·3.

* ✱34·2, `Cnvʻ(R| S)=Š| Ř`, is stated with the descriptive function `Cnv` of
  ✱31·02.  `Principia/Deduction/Star31Derived.lean` declares no theorem, so
  `Š` and `Ř` have no eliminated form to compare here.

A fourth obstruction is worth recording because it is intrinsic to the relative
product and not inherited.  ✱34·21, `(P| Q)| R=P| (Q| R)`, unfolds on the left
to the tree

    .neg n₁ (.always u₁ (.neg n₂ (.neg n₃ (.always u₂ (.neg n₄ φ)))))

with the binder for `y` outermost, and on the right to the same shape with the
binder for `z` outermost.  Reducing one to the other is the commutation of two
existential quantifiers, ✱11·23.  The only transposition primitive available is
`Derivation.star_11_07`, which rewrites `.always u (.always u' ψ)` — two
adjacent `.always` nodes.  Between the two `.always` nodes of an iterated
`Formula.sometimes` stand the two `Formula.neg` nodes `n₂` and `n₃` produced by
✱9·02 and ✱10·01, and no primitive of ✱9 to ✱11 rewrites under a
`.neg (.always …)` prefix.  That double negation is the exact point at which
the two trees fail to reduce to one another.
-/

/-! ## Elimination of relative products -/

def star_34_1_reading
    (vocabulary : Star21EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (left : Term signature real []
      (relationSort relationOrder leftExcess))
    (right : Term signature real []
      (relationSort relationOrder rightExcess))
    (x z : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "✱34·1. ⊢:x(R| S)z.≡.(∃ y).xRy.ySz [✱21·3.(✱34·01)]"
  scopeReading := "The incomplete relative product has the scope of the displayed application equivalence."
  parsed := .assertion (star_21_3_formula vocabulary.abstractionExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_34_01 existential negation disjunction left.weaken.weaken
      right.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x z)

/-- ✱34·1, by the printed ✱21·3 instance after unfolding ✱34·01.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_34_1
    (vocabulary : Star21EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (left : Term signature real []
      (relationSort relationOrder leftExcess))
    (right : Term signature real []
      (relationSort relationOrder rightExcess))
    (x z : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star21EliminationHypothesis vocabulary
      (star_34_01 existential negation disjunction left.weaken.weaken
        right.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x z) :
    Derivation (.assertion (star_21_3_formula
      vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_34_01 existential negation disjunction left.weaken.weaken
        right.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x z)) := by
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction
    (star_34_01 existential negation disjunction left.weaken.weaken
      right.weaken.weaken (.apparent .zero) (.apparent (.succ .zero))) x z
    star_10_35_hypothesis
  exact line1

def star_34_5_reading
    (vocabulary : Star21EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual) : RamifiedReading signature real where
  printed := PM.pmPrinted "✱34·5. ⊢:xR²y.≡.(∃ z).xRz.zRy [✱34·1.(✱34·02)]"
  scopeReading := "Relation squaring is the contextual ✱34·02 specialization of relative product."
  parsed := .assertion (star_21_3_formula vocabulary.abstractionExistential
    vocabulary.leftUniversal vocabulary.rightUniversal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_34_02 existential negation disjunction relation.weaken.weaken
      (.apparent .zero) (.apparent (.succ .zero))) x y)

/-- ✱34·5, the printed specialization of ✱34·1 by ✱34·02.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY`. -/
theorem star_34_5
    (vocabulary : Star21EliminationVocabulary signature
      (bindOrder relationOrder .individual))
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (relation : Term signature real []
      (relationSort relationOrder relationExcess))
    (x y : Term signature real [] .individual)
    (star_10_35_hypothesis : PM.RamifiedSyntax.Star21EliminationHypothesis vocabulary
      (star_34_02 existential negation disjunction relation.weaken.weaken
        (.apparent .zero) (.apparent (.succ .zero))) x y) :
    Derivation (.assertion (star_21_3_formula
      vocabulary.abstractionExistential vocabulary.leftUniversal
      vocabulary.rightUniversal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction
      (star_34_02 existential negation disjunction relation.weaken.weaken
        (.apparent .zero) (.apparent (.succ .zero))) x y)) := by
  have line1 := star_34_1 vocabulary existential negation disjunction
    relation relation x y star_10_35_hypothesis
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_34_01_unfold
#print axioms PM.RamifiedSyntax.star_34_02_unfold
#print axioms PM.RamifiedSyntax.star_34_03_unfold
#print axioms PM.RamifiedSyntax.star_34_1
#print axioms PM.RamifiedSyntax.star_34_5
