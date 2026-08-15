import Principia.Deduction.Star37Derived
import Principia.FirstEdition.Volume1.Star38Source

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱38 — operations with two descriptors

The operation equation supplied below is object syntax: for ✱38·01 its two
apparent arguments read `u,y` in `u = x♀y`, and for ✱38·02 they read `u,x` in
`u = x♀y`.  The fixed descriptor has already been substituted into that
matrix.  No host-language operation or equality is introduced.
-/

/-- ✱38·01, the left section `x♀`, expanded contextually as the relation
abstraction `ûŷ(u = x♀y)`. -/
def star_38_01
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] order) :=
  star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction operationEquation continuation

theorem star_38_01_unfold
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] order) :
    star_38_01 vocabulary operationEquation continuation =
      star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction operationEquation continuation := rfl

/-- ✱38·02, the right section `♀y`, independently expanded as the relation
abstraction `ûx̂(u = x♀y)`. -/
def star_38_02
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] order) :=
  star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction operationEquation continuation

theorem star_38_02_unfold
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] order) :
    star_38_02 vocabulary operationEquation continuation =
      star_21_01 vocabulary.abstractionExistential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction operationEquation continuation := rfl

/-- Audited contextual reading of ✱38·1. -/
def star_38_1_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (u y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱38·1. ⊢ : u(x♀)y .≡. u = x♀y  [(✱38·01)]"
  scopeReading := "The left section is eliminated by ✱38·01; its relation abstraction has the scope of the displayed equivalence."
  parsed := .assertion
    (star_38_01 vocabulary operationEquation
      (star_21_3_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction operationEquation u y))

/-- ✱38·1, the printed relation-abstraction instance after ✱38·01.
The remaining premise transports between the distinct reducibility and
abstraction existential trees exposed by ✱21·3; ✱10·35 does not identify
them.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_38_1
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (u y : Term signature real [] .individual)
    (reducibility_scope_transport : Star21EliminationHypothesis vocabulary
      operationEquation u y) :
    Derivation (star_38_1_reading vocabulary operationEquation u y).parsed := by
  have definitionUnfold := star_38_01_unfold vocabulary operationEquation
    (star_21_3_continuation vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction operationEquation u y)
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction operationEquation u y
    reducibility_scope_transport
  exact Derivation.castAssertion definitionUnfold line1

/-- Audited contextual reading of ✱38·101. -/
def star_38_101_reading
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (u x : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱38·101. ⊢ : u(♀y)x .≡. u = x♀y  [(✱38·02)]"
  scopeReading := "The right section is independently eliminated by ✱38·02; its relation abstraction has the scope of the displayed equivalence."
  parsed := .assertion
    (star_38_02 vocabulary operationEquation
      (star_21_3_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction operationEquation u x))

/-- ✱38·101, the symmetric relation-abstraction instance after ✱38·02.
It has the same unresolved reducibility-scope transport as ✱38·1.
`demonstration_provenance: follows-printed`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_38_101
    (vocabulary : Star21EliminationVocabulary signature order)
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (u x : Term signature real [] .individual)
    (reducibility_scope_transport : Star21EliminationHypothesis vocabulary
      operationEquation u x) :
    Derivation (star_38_101_reading vocabulary operationEquation u x).parsed := by
  have definitionUnfold := star_38_02_unfold vocabulary operationEquation
    (star_21_3_continuation vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction operationEquation u x)
  have line1 := star_21_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction operationEquation u x
    reducibility_scope_transport
  exact Derivation.castAssertion definitionUnfold line1

/-! ## The image of a section, ✱38·13

PM's `x♀ʻʻα` puts two incomplete symbols on top of one another: the section
`x♀` of ✱38·01, and the image class of ✱37·01 formed from it.  The section
must therefore be given the wider scope, and the image abstraction is built
inside it, where the relation is the apparent variable bound by ✱21·01.
-/

/-- The order of `Rʻʻβ` once ✱37·01 is expanded over a matrix of order
`bindOrder order .individual`.  It is the scope order that the section
abstraction of ✱38·01 has to carry. -/
def star_38_imageScopeOrder (order : Nat) : Nat :=
  bindOrder
    (max (bindOrder (bindOrder order .individual) .individual)
      (bindOrder order .individual))
    (classSort (bindOrder order .individual) 0)

/-- The ✱21·01 vocabulary of the section when its scope is a whole image
class.  It packages no new rule; only the logical meanings of ✱21·01 at the
wider scope order. -/
structure Star38SectionImageVocabulary (signature : Signature) (order : Nat)
    where
  abstractionExistential : ExistentialVocabulary signature
    (relationSort order 0)
    (max (bindOrder (bindOrder order .individual) .individual)
      (star_38_imageScopeOrder order))
  leftUniversal : signature.Universal .individual order
  rightUniversal : signature.Universal .individual
    (bindOrder order .individual)
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation
    (bindOrder (bindOrder order .individual) .individual)
  rightNegation : signature.Negation (star_38_imageScopeOrder order)
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder order .individual) .individual)
      (star_38_imageScopeOrder order))
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder order .individual) .individual)
      (star_38_imageScopeOrder order))

/-- `x♀ʻʻα`: the ✱37·01 image class formed inside the scope of the ✱38·01
section.  The relation argument of the image is the apparent relation
variable bound by ✱21·01, so no relation term is manufactured. -/
def star_38_13_image
    (sectionVocabulary : Star38SectionImageVocabulary signature order)
    (imageVocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (imageExistential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real
      [classSort (bindOrder order .individual) 0, relationSort order 0]
      (bindOrder order .individual)) :=
  star_21_01 sectionVocabulary.abstractionExistential
    sectionVocabulary.leftUniversal sectionVocabulary.rightUniversal
    sectionVocabulary.equivalenceNegation
    sectionVocabulary.equivalenceDisjunction
    sectionVocabulary.leftNegation sectionVocabulary.rightNegation
    sectionVocabulary.outerNegation
    sectionVocabulary.conjunctionDisjunction operationEquation
    (star_37_01 imageVocabulary imageExistential negation disjunction
      alpha.weaken (.apparent .zero) continuation)

/-- The complete two-stage contextual expansion behind `x♀ʻʻα`. -/
theorem star_38_13_image_unfold
    (sectionVocabulary : Star38SectionImageVocabulary signature order)
    (imageVocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (imageExistential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real
      [classSort (bindOrder order .individual) 0, relationSort order 0]
      (bindOrder order .individual)) :
    star_38_13_image sectionVocabulary imageVocabulary imageExistential
        negation disjunction alpha operationEquation continuation =
      star_21_01 sectionVocabulary.abstractionExistential
        sectionVocabulary.leftUniversal sectionVocabulary.rightUniversal
        sectionVocabulary.equivalenceNegation
        sectionVocabulary.equivalenceDisjunction
        sectionVocabulary.leftNegation sectionVocabulary.rightNegation
        sectionVocabulary.outerNegation
        sectionVocabulary.conjunctionDisjunction operationEquation
        (star_37_01 imageVocabulary imageExistential negation disjunction
          alpha.weaken (.apparent .zero) continuation) := rfl

/-- The right member printed at ✱38·13, `(∃y). y ∈ α . u = x♀y`.  It
mentions the operation, not the section, so it is closed under the section
binder. -/
def star_38_13_matrix
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order) :
    Formula signature real [.individual]
      (bindOrder order .individual) :=
  .sometimes existential
    (conjunction negation disjunction
      (membership (.apparent .zero) alpha.weaken.weaken)
      operationEquation)

theorem star_38_13_matrix_unfold
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order) :
    star_38_13_matrix existential negation disjunction alpha
        operationEquation =
      .sometimes existential
        (conjunction negation disjunction
          (membership (.apparent .zero) alpha.weaken.weaken)
          operationEquation) := rfl

/-- Audited contextual reading of ✱38·13.  The section has the whole
proposition for scope; inside it the image class has the scope of the
displayed membership equivalence. -/
def star_38_13_reading
    (sectionVocabulary : Star38SectionImageVocabulary signature order)
    (imageVocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (imageExistential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation :
      Formula signature real [.individual, .individual] order)
    (u : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted
    "✱38·13. ⊢ : u ∈ x♀ʻʻα .≡. (∃y). y ∈ α . u = x♀y  [✱38·1.✱37·1]"
  scopeReading := "The left section is eliminated first by ✱38·01; the image class formed from the bound relation then has the scope of the displayed equivalence."
  parsed := .assertion
    (star_38_13_image sectionVocabulary imageVocabulary imageExistential
      negation disjunction alpha operationEquation
      ((star_20_3_continuation imageVocabulary.equivalenceNegation
        imageVocabulary.equivalenceDisjunction
        (star_38_13_matrix imageExistential negation disjunction alpha
          operationEquation) u).rename
        (liftRenaming (emptyRenaming (target := [relationSort order 0])))))

/- ✱38·13 is catalogued as a reading only, and ✱38·131 below is its mirror
image.  The printed route is `✱38·1.✱37·1`, and it does not close here.

`star_37_1` concludes `⊢ᵣ star_20_3_formula … matrix x`, and `⊢ᵣ` is
`Derivation (.assertion …)` for a `Formula signature real [] _`: ✱20·3 is
available only for a closed apparent context.  In `star_38_13_image` the
image abstraction sits under the ✱21·01 binder, at apparent context
`[relationSort order 0]`, because that binder is what supplies the relation
`x♀`.  So `star_37_1` cannot be applied to it: its matrix argument has type
`Formula signature real [.individual] resultOrder`, while the matrix here is
`Formula signature real [.individual, relationSort order 0] resultOrder`.

Moving the section inside instead does not help.  The image matrix demands
its relation as a term, in the `.apply` node
`applyBinary relation (.apparent (.succ .zero)) (.apparent .zero)` of
`star_37_01_matrix`; ✱38·01 supplies no such term, its expansion being the
`.sometimes`-rooted `star_21_01` tree of order
`bindOrder (max (bindOrder (bindOrder order .individual) .individual)
  scopeOrder) (relationSort order 0)`, which is not even at the matrix order
`order`.

Finally, the last printed step replaces `u(x♀)y` by `u = x♀y` under
`.sometimes` and `conjunction`, which is ✱10·11·281 followed by ✱4·36; the
library has ✱10·28 only for `Formula signature real [argument] 0` and no
✱10·281.  Nothing is asserted here. -/

/-- Matrix obtained by expanding the right-section image in ✱38·03:
`(∃x). x∈α . u=x♀y`.  Before the inner binder the apparent variable is
`u`; afterwards `x` is zero and `u` is one. -/
def star_38_03_matrix
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order) :
    Formula signature real [.individual]
      (bindOrder order .individual) :=
  .sometimes existential
    (conjunction negation disjunction
      (membership (.apparent .zero) alpha.weaken.weaken)
      operationEquation)

theorem star_38_03_matrix_unfold
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order) :
    star_38_03_matrix existential negation disjunction alpha
        operationEquation =
      .sometimes existential
        (conjunction negation disjunction
          (membership (.apparent .zero) alpha.weaken.weaken)
          operationEquation) := rfl

/-- ✱38·03, `α♀_{,,}y`, expanded independently as the class image
`♀yʻʻα`, with both incomplete abstractions eliminated. -/
def star_38_03
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order)
    (continuation : Formula signature real
      [classSort (bindOrder order .individual) 0]
      (bindOrder order .individual)) :=
  star_20_01 vocabulary.abstractionExistential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation
    vocabulary.outerNegation vocabulary.conjunctionDisjunction
    (star_38_03_matrix existential negation disjunction alpha
      operationEquation) continuation

theorem star_38_03_unfold
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order)
    (continuation : Formula signature real
      [classSort (bindOrder order .individual) 0]
      (bindOrder order .individual)) :
    star_38_03 vocabulary existential negation disjunction alpha
        operationEquation continuation =
      star_20_01 vocabulary.abstractionExistential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (star_38_03_matrix existential negation disjunction alpha
          operationEquation) continuation := rfl

/-- Audited definitional reading of ✱38·2. -/
def star_38_2_reading
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order)
    (continuation : Formula signature real
      [classSort (bindOrder order .individual) 0]
      (bindOrder order .individual)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱38·2. ⊢. α♀_{,,}y = ♀yʻʻα  [(✱38·03)]"
  scopeReading := "The right member is built directly from the expanded image matrix; the left member is the independent abbreviation ✱38·03."
  parsed := .assertion (star_4_01 vocabulary.finalNegation
    vocabulary.finalDisjunction
    (star_38_03 vocabulary existential negation disjunction alpha
      operationEquation continuation)
    (star_20_01 vocabulary.abstractionExistential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (star_38_03_matrix existential negation disjunction alpha
        operationEquation) continuation))

/-- ✱38·2, the assertion of the eliminable definition ✱38·03. -/
theorem star_38_2
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order)
    (continuation : Formula signature real
      [classSort (bindOrder order .individual) 0]
      (bindOrder order .individual)) :
    Derivation (star_38_2_reading vocabulary existential negation
      disjunction alpha operationEquation continuation).parsed := by
  have definitionUnfold := star_38_03_unfold vocabulary existential negation
    disjunction alpha operationEquation continuation
  have line1 := star_4_2 vocabulary.finalNegation vocabulary.finalDisjunction
    (star_20_01 vocabulary.abstractionExistential vocabulary.universal
      vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
      vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (star_38_03_matrix existential negation disjunction alpha
        operationEquation) continuation)
  exact Derivation.castAssertion
    (congrArg (fun left => star_4_01 vocabulary.finalNegation
      vocabulary.finalDisjunction left
      (star_20_01 vocabulary.abstractionExistential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (star_38_03_matrix existential negation disjunction alpha
          operationEquation) continuation)) definitionUnfold)
    line1

/-- Audited contextual reading of ✱38·131 after expanding ✱38·02 and the
image definition. -/
def star_38_131_reading
    (vocabulary : Star37EliminationVocabulary signature
      (bindOrder order .individual))
    (existential : ExistentialVocabulary signature .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order classExcess))
    (operationEquation : Formula signature real
      [.individual, .individual] order)
    (u : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱38·131. ⊢ : u ∈ ♀yʻʻα .≡. (∃x). x ∈ α . u = x♀y  [✱38·101.✱37·1]"
  scopeReading := "Both the right section and its image are eliminated; the remaining class abstraction has the scope of the displayed equivalence."
  parsed := .assertion
    (star_38_03 vocabulary existential negation disjunction alpha
      operationEquation
      (star_20_3_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction
        (star_38_03_matrix existential negation disjunction alpha
          operationEquation) u))

/- ✱38·131 is intentionally left as a reading only.  Its former proof used
✱20·3 directly and therefore skipped the printed `✱38·101.✱37·1` chain.
Closing it requires transporting the ✱38·101 equivalence through the
existential image matrix before applying ✱37·1. -/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_38_01_unfold
#print axioms PM.RamifiedSyntax.star_38_02_unfold
#print axioms PM.RamifiedSyntax.star_38_1
#print axioms PM.RamifiedSyntax.star_38_101
#print axioms PM.RamifiedSyntax.star_38_13_image_unfold
#print axioms PM.RamifiedSyntax.star_38_13_matrix_unfold
#print axioms PM.RamifiedSyntax.star_38_03_matrix_unfold
#print axioms PM.RamifiedSyntax.star_38_03_unfold
#print axioms PM.RamifiedSyntax.star_38_2
