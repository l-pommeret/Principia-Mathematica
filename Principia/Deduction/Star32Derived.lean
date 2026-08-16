import Principia.Deduction.Star31Derived
import Principia.FirstEdition.Volume1.Star32Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱32

`R⃗` and `R⃖` are incomplete symbols twice over: ✱32·01 abstracts a *class* and
an *individual*, and the matrix it abstracts, `α = x̂(xRy)`, itself contains the
contextual class abstraction of ✱20·01.  Both eliminations are printed as `Df`,
so both are reconstructed below with their `rfl` unfoldings and no
class-valued or descriptive `Term` is ever formed.

The elimination PM cites for ✱32·1 and ✱32·101 is ✱21·3 at those two sorts,
which is `twoSortedElimination` of `Star31Derived`.  It is not unconditional:
after ✱12·11 the derivation reaches
`.sometimes reducibilityExistential (binaryReducibilityMatrix …)` whereas the
abstraction it must reach is
`.sometimes abstractionExistential (mixedConjunction … (.always …) continuation)`,
and the ✱10·35 transport between the two is missing.  ✱32·1 and ✱32·101 are
therefore stated with exactly that one premise carried through.

✱32·11, ✱32·111, ✱32·13, ✱32·131, ✱32·21 and ✱32·211 all cite ✱30·3, whose own
printed step ✱14·202 goes through ✱13·195 (see the ✱30·3 section of
`Star30Derived`).  ✱13·195 is now proved unconditionally; ✱14·202 remains
undeclared, and it is the whole of what blocks these six.  ✱32·12,
✱32·121, ✱32·22 and ✱32·221 then cite ✱14·21, for which `Star14Derived`
declares no theorem at all: only the audited reading and the missing
`UniversalImplicationToExistentialAntecedentTransport`.  ✱32·18 and ✱32·181
rest on ✱32·13.  None of them is derived here.
-/

/-- The order ✱13·01 assigns to `α = φ` when `α` ranges over classes of
individuals whose membership matrix has order `relationOrder`. -/
abbrev star_32_identityOrder
    (relationOrder identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder identityBaseOrder
    (.function [classSort relationOrder 0] identityBaseOrder identityExcess)

/-- The order of the matrix `α = x̂(xRy)` printed inside ✱32·01, once ✱20·01
has eliminated the class abstraction. -/
abbrev star_32_01_matrixOrder
    (relationOrder identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder
    (max (bindOrder relationOrder .individual)
      (star_32_identityOrder relationOrder identityBaseOrder identityExcess))
    (classSort relationOrder 0)

/-- Everything the printed matrix `α = x̂(xRy)` needs: the ✱20·01 vocabulary
that eliminates the class abstraction, and the ✱13·01 vocabulary of the
identity that stands in front of it. -/
structure Star32ClassMatrixVocabulary (signature : Signature)
    (relationOrder identityBaseOrder identityExcess : Nat) where
  existential : ExistentialVocabulary signature (classSort relationOrder 0)
    (max (bindOrder relationOrder .individual)
      (star_32_identityOrder relationOrder identityBaseOrder identityExcess))
  universal : signature.Universal .individual relationOrder
  equivalenceNegation : signature.Negation relationOrder
  equivalenceDisjunction : signature.Disjunction relationOrder
  leftNegation : signature.Negation (bindOrder relationOrder .individual)
  rightNegation : signature.Negation
    (star_32_identityOrder relationOrder identityBaseOrder identityExcess)
  outerNegation : signature.Negation
    (max (bindOrder relationOrder .individual)
      (star_32_identityOrder relationOrder identityBaseOrder identityExcess))
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder relationOrder .individual)
      (star_32_identityOrder relationOrder identityBaseOrder identityExcess))
  identity : IdentityVocabulary signature (classSort relationOrder 0)
    identityBaseOrder identityExcess

/-- The matrix `α = x̂(xRy)` printed inside ✱32·01.  Under the ✱21·01 binders
the head apparent variable is `α` and the next one is `y`; `x̂(xRy)` is not a
term, it is the ✱20·01 scope whose continuation is the identity `α = φ`. -/
def star_32_01_matrix
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real apparent
      (.function [.individual, .individual] relationOrder excess)) :
    Formula signature real
      (classSort relationOrder 0 :: .individual :: apparent)
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (applyBinary
      (relation.weaken.weaken.weaken : Term signature real
        (.individual :: classSort relationOrder 0 :: .individual :: apparent)
        (.function [.individual, .individual] relationOrder excess))
      (.apparent .zero) (.apparent (.succ (.succ .zero))))
    (star_13_01 vocabulary.identity (.apparent (.succ .zero)) (.apparent .zero))

theorem star_32_01_matrix_unfold
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real apparent
      (.function [.individual, .individual] relationOrder excess)) :
    star_32_01_matrix vocabulary relation =
      star_20_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (applyBinary
          (relation.weaken.weaken.weaken : Term signature real
            (.individual :: classSort relationOrder 0 :: .individual ::
              apparent)
            (.function [.individual, .individual] relationOrder excess))
          (.apparent .zero) (.apparent (.succ (.succ .zero))))
        (star_13_01 vocabulary.identity (.apparent (.succ .zero))
          (.apparent .zero)) := rfl

/-- The matrix `β = ŷ(xRy)` printed inside ✱32·02.  Here the head apparent
variable is `β` and the next one is `x`, and the class abstraction binds the
second argument of `R`. -/
def star_32_02_matrix
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real apparent
      (.function [.individual, .individual] relationOrder excess)) :
    Formula signature real
      (classSort relationOrder 0 :: .individual :: apparent)
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (applyBinary
      (relation.weaken.weaken.weaken : Term signature real
        (.individual :: classSort relationOrder 0 :: .individual :: apparent)
        (.function [.individual, .individual] relationOrder excess))
      (.apparent (.succ (.succ .zero))) (.apparent .zero))
    (star_13_01 vocabulary.identity (.apparent (.succ .zero)) (.apparent .zero))

theorem star_32_02_matrix_unfold
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real apparent
      (.function [.individual, .individual] relationOrder excess)) :
    star_32_02_matrix vocabulary relation =
      star_20_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        (applyBinary
          (relation.weaken.weaken.weaken : Term signature real
            (.individual :: classSort relationOrder 0 :: .individual ::
              apparent)
            (.function [.individual, .individual] relationOrder excess))
          (.apparent (.succ (.succ .zero))) (.apparent .zero))
        (star_13_01 vocabulary.identity (.apparent (.succ .zero))
          (.apparent .zero)) := rfl

/-- The sort of `R⃗` and of `R⃖`: a predicative function of a class and an
individual, at the order of the matrix ✱32·01 abstracts. -/
abbrev star_32_sectionalSort
    (relationOrder identityBaseOrder identityExcess : Nat) : RSort :=
  .function [classSort relationOrder 0, .individual]
    (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess) 0

/-- ✱32·01: `R⃗ = α̂ŷ{α = x̂(xRy)}` Df.  The right-hand sectional function is an
incomplete symbol whose two abstracted arguments have different sorts, so the
definition is the two-sorted ✱21·01 scope at the printed matrix. -/
def star_32_01
    (existential : ExistentialVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      (max
        (bindOrder
          (bindOrder
            (star_32_01_matrixOrder relationOrder identityBaseOrder
              identityExcess)
            (classSort relationOrder 0))
          .individual)
        scopeOrder))
    (abstractionLeftUniversal : signature.Universal (classSort relationOrder 0)
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (abstractionRightUniversal : signature.Universal .individual
      (bindOrder
        (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess)
        (classSort relationOrder 0)))
    (abstractionEquivalenceNegation : signature.Negation
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (abstractionEquivalenceDisjunction : signature.Disjunction
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess)
          (classSort relationOrder 0))
        .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder
            (star_32_01_matrixOrder relationOrder identityBaseOrder
              identityExcess)
            (classSort relationOrder 0))
          .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (star_32_01_matrixOrder relationOrder identityBaseOrder
              identityExcess)
            (classSort relationOrder 0))
          .individual)
        scopeOrder))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real apparent
      (.function [.individual, .individual] relationOrder excess))
    (continuation : Formula signature real
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess ::
        apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max
          (bindOrder
            (bindOrder
              (star_32_01_matrixOrder relationOrder identityBaseOrder
                identityExcess)
              (classSort relationOrder 0))
            .individual)
          scopeOrder)
        (star_32_sectionalSort relationOrder identityBaseOrder
          identityExcess)) :=
  twoSortedAbstraction existential abstractionLeftUniversal
    abstractionRightUniversal abstractionEquivalenceNegation
    abstractionEquivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction (star_32_01_matrix vocabulary relation) continuation

theorem star_32_01_unfold
    (existential : ExistentialVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      (max
        (bindOrder
          (bindOrder
            (star_32_01_matrixOrder relationOrder identityBaseOrder
              identityExcess)
            (classSort relationOrder 0))
          .individual)
        scopeOrder))
    (abstractionLeftUniversal : signature.Universal (classSort relationOrder 0)
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (abstractionRightUniversal : signature.Universal .individual
      (bindOrder
        (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess)
        (classSort relationOrder 0)))
    (abstractionEquivalenceNegation : signature.Negation
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (abstractionEquivalenceDisjunction : signature.Disjunction
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess)
          (classSort relationOrder 0))
        .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder
            (star_32_01_matrixOrder relationOrder identityBaseOrder
              identityExcess)
            (classSort relationOrder 0))
          .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (star_32_01_matrixOrder relationOrder identityBaseOrder
              identityExcess)
            (classSort relationOrder 0))
          .individual)
        scopeOrder))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real apparent
      (.function [.individual, .individual] relationOrder excess))
    (continuation : Formula signature real
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess ::
        apparent) scopeOrder) :
    star_32_01 existential abstractionLeftUniversal abstractionRightUniversal
        abstractionEquivalenceNegation abstractionEquivalenceDisjunction
        leftNegation rightNegation outerNegation conjunctionDisjunction
        vocabulary relation continuation =
      twoSortedAbstraction existential abstractionLeftUniversal
        abstractionRightUniversal abstractionEquivalenceNegation
        abstractionEquivalenceDisjunction leftNegation rightNegation
        outerNegation conjunctionDisjunction
        (star_32_01_matrix vocabulary relation) continuation := rfl

/-- Object formula of ✱32·1 once ✱32·01, ✱20·01 and ✱21·01 are eliminated: the
two-sorted ✱21·3 at the matrix `α = x̂(xRy)`, with a class argument and an
individual argument. -/
def star_32_1_formula
    (elimination : TwoSortedEliminationVocabulary signature
      (classSort relationOrder 0) .individual
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess))
    (classArgument : Term signature real [] (classSort relationOrder 0))
    (y : Term signature real [] .individual) :
    Formula signature real []
      (bindOrder
        (max
          (bindOrder
            (bindOrder
              (star_32_01_matrixOrder relationOrder identityBaseOrder
                identityExcess)
              (classSort relationOrder 0))
            .individual)
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess))
        (star_32_sectionalSort relationOrder identityBaseOrder
          identityExcess)) :=
  twoSortedEliminationFormula elimination.abstractionExistential
    elimination.leftUniversal elimination.rightUniversal
    elimination.equivalenceNegation elimination.equivalenceDisjunction
    elimination.leftNegation elimination.rightNegation
    elimination.outerNegation elimination.conjunctionDisjunction
    (star_32_01_matrix vocabulary relation) classArgument y

/-- Audited scope reading of ✱32·1. -/
def star_32_1_reading
    (elimination : TwoSortedEliminationVocabulary signature
      (classSort relationOrder 0) .individual
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess))
    (classArgument : Term signature real [] (classSort relationOrder 0))
    (y : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱32·1. ⊢:αR⃗y.≡.α=x̂(xRy) [*21·3.(*32·01)]"
  parsed := .assertion (star_32_1_formula elimination vocabulary relation
    classArgument y)
  scopeReading := "`R⃗` is eliminated by ✱32·01; the two-sorted abstraction of ✱21·01 has the whole printed equivalence as its scope, and its matrix is the ✱20·01 scope of `x̂(xRy)` over the identity `α = φ`."

/-- ✱32·1, by the printed route `[✱21·3.(✱32·01)]` at a class argument and an
individual argument.  The single premise `star_32_1_hypothesis` is ✱21·3's own
missing ✱10·35 transport, inherited and not added.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_32_1
    (elimination : TwoSortedEliminationVocabulary signature
      (classSort relationOrder 0) .individual
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess))
    (classArgument : Term signature real [] (classSort relationOrder 0))
    (y : Term signature real [] .individual)
    (star_32_1_hypothesis : SortedEliminationHypothesis elimination
      (star_32_01_matrix vocabulary relation) classArgument y) :
    Derivation (star_32_1_reading elimination vocabulary relation
      classArgument y).parsed := by
  have line1 := twoSortedElimination elimination
    (star_32_01_matrix vocabulary relation) classArgument y
    star_32_1_hypothesis
  exact line1

/-- Object formula of ✱32·101, the mirror of ✱32·1 obtained from ✱32·02. -/
def star_32_101_formula
    (elimination : TwoSortedEliminationVocabulary signature
      (classSort relationOrder 0) .individual
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess))
    (classArgument : Term signature real [] (classSort relationOrder 0))
    (x : Term signature real [] .individual) :
    Formula signature real []
      (bindOrder
        (max
          (bindOrder
            (bindOrder
              (star_32_01_matrixOrder relationOrder identityBaseOrder
                identityExcess)
              (classSort relationOrder 0))
            .individual)
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess))
        (star_32_sectionalSort relationOrder identityBaseOrder
          identityExcess)) :=
  twoSortedEliminationFormula elimination.abstractionExistential
    elimination.leftUniversal elimination.rightUniversal
    elimination.equivalenceNegation elimination.equivalenceDisjunction
    elimination.leftNegation elimination.rightNegation
    elimination.outerNegation elimination.conjunctionDisjunction
    (star_32_02_matrix vocabulary relation) classArgument x

/-- Audited scope reading of ✱32·101. -/
def star_32_101_reading
    (elimination : TwoSortedEliminationVocabulary signature
      (classSort relationOrder 0) .individual
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess))
    (classArgument : Term signature real [] (classSort relationOrder 0))
    (x : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱32·101. ⊢:βR⃖x.≡.β=ŷ(xRy) [*21·3.(*32·02)]"
  parsed := .assertion (star_32_101_formula elimination vocabulary relation
    classArgument x)
  scopeReading := "`R⃖` is eliminated by ✱32·02; the two-sorted abstraction of ✱21·01 has the whole printed equivalence as its scope, and its matrix is the ✱20·01 scope of `ŷ(xRy)` over the identity `β = φ`."

/-- ✱32·101, by the printed route `[✱21·3.(✱32·02)]`, with the same single
inherited premise as ✱32·1.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_32_101
    (elimination : TwoSortedEliminationVocabulary signature
      (classSort relationOrder 0) .individual
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess))
    (vocabulary : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess))
    (classArgument : Term signature real [] (classSort relationOrder 0))
    (x : Term signature real [] .individual)
    (star_32_101_hypothesis : SortedEliminationHypothesis elimination
      (star_32_02_matrix vocabulary relation) classArgument x) :
    Derivation (star_32_101_reading elimination vocabulary relation
      classArgument x).parsed := by
  have line1 := twoSortedElimination elimination
    (star_32_02_matrix vocabulary relation) classArgument x
    star_32_101_hypothesis
  exact line1

/-! ## ✱32·03 and ✱32·2 -/

/-- The vocabulary the ✱32·01 abstraction needs, gathered so that the matrix of
✱32·03 stays readable.  It adds no object rule. -/
structure Star32SectionalVocabulary (signature : Signature)
    (relationOrder identityBaseOrder identityExcess scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
    (max
      (bindOrder
        (bindOrder
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess)
          (classSort relationOrder 0))
        .individual)
      scopeOrder)
  leftUniversal : signature.Universal (classSort relationOrder 0)
    (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess)
  rightUniversal : signature.Universal .individual
    (bindOrder
      (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess)
      (classSort relationOrder 0))
  equivalenceNegation : signature.Negation
    (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess)
  equivalenceDisjunction : signature.Disjunction
    (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess)
  leftNegation : signature.Negation
    (bindOrder
      (bindOrder
        (star_32_01_matrixOrder relationOrder identityBaseOrder identityExcess)
        (classSort relationOrder 0))
      .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max
      (bindOrder
        (bindOrder
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess)
          (classSort relationOrder 0))
        .individual)
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max
      (bindOrder
        (bindOrder
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess)
          (classSort relationOrder 0))
        .individual)
      scopeOrder)

/-- The order ✱13·01 assigns to the identity `A = R⃗` printed inside ✱32·03. -/
abbrev star_32_sgIdentityOrder
    (relationOrder identityBaseOrder identityExcess sgBaseOrder sgExcess :
      Nat) : Nat :=
  bindOrder sgBaseOrder
    (.function
      [star_32_sectionalSort relationOrder identityBaseOrder identityExcess]
      sgBaseOrder sgExcess)

/-- The order of the matrix `A = R⃗` printed inside ✱32·03, once ✱32·01 has
eliminated the sectional function. -/
abbrev star_32_03_matrixOrder
    (relationOrder identityBaseOrder identityExcess sgBaseOrder sgExcess :
      Nat) : Nat :=
  bindOrder
    (max
      (bindOrder
        (bindOrder
          (star_32_01_matrixOrder relationOrder identityBaseOrder
            identityExcess)
          (classSort relationOrder 0))
        .individual)
      (star_32_sgIdentityOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)

/-- The matrix `A = R⃗` printed inside ✱32·03.  Under the ✱21·01 binders the
head apparent variable is `A` and the next one is `R`; `R⃗` is not a term, it is
the ✱32·01 scope whose continuation is the identity `A = φ`. -/
def star_32_03_matrix
    (sectional : Star32SectionalVocabulary signature relationOrder
      identityBaseOrder identityExcess
      (star_32_sgIdentityOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (classMatrix : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (sgIdentity : IdentityVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      sgBaseOrder sgExcess) :
    Formula signature real
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess ::
        .function [.individual, .individual] relationOrder excess :: apparent)
      (star_32_03_matrixOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess) :=
  star_32_01 sectional.existential sectional.leftUniversal
    sectional.rightUniversal sectional.equivalenceNegation
    sectional.equivalenceDisjunction sectional.leftNegation
    sectional.rightNegation sectional.outerNegation
    sectional.conjunctionDisjunction classMatrix (.apparent (.succ .zero))
    (star_13_01 sgIdentity (.apparent (.succ .zero)) (.apparent .zero))

theorem star_32_03_matrix_unfold
    (sectional : Star32SectionalVocabulary signature relationOrder
      identityBaseOrder identityExcess
      (star_32_sgIdentityOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (classMatrix : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (sgIdentity : IdentityVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      sgBaseOrder sgExcess) :
    star_32_03_matrix (real := real) (apparent := apparent) (excess := excess)
        sectional classMatrix sgIdentity =
      star_32_01 sectional.existential sectional.leftUniversal
        sectional.rightUniversal sectional.equivalenceNegation
        sectional.equivalenceDisjunction sectional.leftNegation
        sectional.rightNegation sectional.outerNegation
        sectional.conjunctionDisjunction classMatrix (.apparent (.succ .zero))
        (star_13_01 sgIdentity (.apparent (.succ .zero))
          (.apparent .zero)) := rfl

/-- Object formula of ✱32·2 once ✱32·03, ✱32·01, ✱20·01 and ✱21·01 are
eliminated: the two-sorted ✱21·3 at the matrix `A = R⃗`, with a sectional
argument and a relation argument. -/
def star_32_2_formula
    (elimination : TwoSortedEliminationVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      (.function [.individual, .individual] relationOrder excess)
      (star_32_03_matrixOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (sectional : Star32SectionalVocabulary signature relationOrder
      identityBaseOrder identityExcess
      (star_32_sgIdentityOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (classMatrix : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (sgIdentity : IdentityVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      sgBaseOrder sgExcess)
    (sectionalArgument : Term signature real []
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess))
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess)) :=
  twoSortedEliminationFormula elimination.abstractionExistential
    elimination.leftUniversal elimination.rightUniversal
    elimination.equivalenceNegation elimination.equivalenceDisjunction
    elimination.leftNegation elimination.rightNegation
    elimination.outerNegation elimination.conjunctionDisjunction
    (star_32_03_matrix sectional classMatrix sgIdentity) sectionalArgument
    relation

/-- Audited scope reading of ✱32·2. -/
def star_32_2_reading
    (elimination : TwoSortedEliminationVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      (.function [.individual, .individual] relationOrder excess)
      (star_32_03_matrixOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (sectional : Star32SectionalVocabulary signature relationOrder
      identityBaseOrder identityExcess
      (star_32_sgIdentityOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (classMatrix : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (sgIdentity : IdentityVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      sgBaseOrder sgExcess)
    (sectionalArgument : Term signature real []
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess))
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱32·2. ⊢:A sg R.≡.A=R⃗ [*21·3.(*32·03)]"
  parsed := .assertion (star_32_2_formula elimination sectional classMatrix
    sgIdentity sectionalArgument relation)
  scopeReading := "`sg` is eliminated by ✱32·03; the two-sorted abstraction of ✱21·01 has the whole printed equivalence as its scope, and its matrix is the ✱32·01 scope of `R⃗` over the identity `A = φ`."

/-- ✱32·2, by the printed route `[✱21·3.(✱32·03)]`.  The single premise
`star_32_2_hypothesis` is ✱21·3's own missing ✱10·35 transport, inherited and
not added.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_32_2
    (elimination : TwoSortedEliminationVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      (.function [.individual, .individual] relationOrder excess)
      (star_32_03_matrixOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (sectional : Star32SectionalVocabulary signature relationOrder
      identityBaseOrder identityExcess
      (star_32_sgIdentityOrder relationOrder identityBaseOrder identityExcess
        sgBaseOrder sgExcess))
    (classMatrix : Star32ClassMatrixVocabulary signature relationOrder
      identityBaseOrder identityExcess)
    (sgIdentity : IdentityVocabulary signature
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess)
      sgBaseOrder sgExcess)
    (sectionalArgument : Term signature real []
      (star_32_sectionalSort relationOrder identityBaseOrder identityExcess))
    (relation : Term signature real []
      (.function [.individual, .individual] relationOrder excess))
    (star_32_2_hypothesis : SortedEliminationHypothesis elimination
      (star_32_03_matrix sectional classMatrix sgIdentity) sectionalArgument
      relation) :
    Derivation (star_32_2_reading elimination sectional classMatrix sgIdentity
      sectionalArgument relation).parsed := by
  have line1 := twoSortedElimination elimination
    (star_32_03_matrix sectional classMatrix sgIdentity) sectionalArgument
    relation star_32_2_hypothesis
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_32_01_matrix_unfold
#print axioms PM.RamifiedSyntax.star_32_02_matrix_unfold
#print axioms PM.RamifiedSyntax.star_32_01_unfold
#print axioms PM.RamifiedSyntax.star_32_1
#print axioms PM.RamifiedSyntax.star_32_101
#print axioms PM.RamifiedSyntax.star_32_03_matrix_unfold
#print axioms PM.RamifiedSyntax.star_32_2
