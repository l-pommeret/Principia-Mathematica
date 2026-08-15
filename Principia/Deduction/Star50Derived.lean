import Principia.Deduction.Star21Derived
import Principia.FirstEdition.Volume1.Star50Source
import Principia.Syntax.Printed

namespace PM.RamifiedSyntax

/-- T4 reading specialized to the ramified claims of ✱50. -/
structure Star50Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-!
# Derived propositions of PM I, ✱50

The identity relation of ✱50·01 is an eliminable abbreviation.  Its matrix is
the Leibniz identity of ✱13·01, and ✱50·1 is the corresponding instance of
the relation-abstraction elimination theorem ✱21·3.
-/

/-- The binary matrix printed in the definiens of ✱50·01. -/
def star_50_01_matrix
    (vocabulary : IdentityVocabulary signature .individual order excess) :
    Formula signature real [.individual, .individual]
      (bindOrder order (.function [.individual] order excess)) :=
  star_13_01 vocabulary (.apparent .zero) (.apparent (.succ .zero))

/-- ✱50·01 applied contextually to two arguments.  A printed `Df` remains
reducible, so this is the ✱21·3 formula specialized to the identity matrix. -/
def star_50_01_application
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort
        (bindOrder order (.function [.individual] order excess)) 0)
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (.function [.individual] order excess)))
    (rightUniversal : signature.Universal .individual
      (bindOrder
        (bindOrder order (.function [.individual] order excess))
        .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (.function [.individual] order excess)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder order (.function [.individual] order excess))
          .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (vocabulary : IdentityVocabulary signature .individual order excess)
    (x y : Term signature real [] .individual) :=
  star_21_3_formula abstractionExistential leftUniversal rightUniversal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction (star_50_01_matrix vocabulary) x y

/-- Audited object-syntax reading of ✱50·1. -/
def star_50_1_reading
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort
        (bindOrder order (.function [.individual] order excess)) 0)
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (.function [.individual] order excess)))
    (rightUniversal : signature.Universal .individual
      (bindOrder
        (bindOrder order (.function [.individual] order excess))
        .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (.function [.individual] order excess)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder order (.function [.individual] order excess))
          .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (vocabulary : IdentityVocabulary signature .individual order excess)
    (x y : Term signature real [] .individual) :
    Star50Reading signature real where
  printed := PM.pmPrinted
    "✱50·1. ⊢ : xIy .≡. x = y  [✱21·3.(✱50·01)]"
  parsed := .assertion (star_50_01_application abstractionExistential
    leftUniversal rightUniversal equivalenceNegation equivalenceDisjunction
    leftNegation rightNegation outerNegation conjunctionDisjunction vocabulary
    x y)
  scopeReading := "The relation abstraction of ✱50·01 is eliminated at the two displayed individual arguments."

/-- The contextual reducibility-scope transport still needed by the available
✱21·3 derivation.  The proved object theorem ✱10·35 has a `star_4_01`
conclusion at order zero; it does not reduce to this mixed implication between
the binary reducibility formula and the contextual relation abstraction. -/
structure Star50ReducibilityScopeTransport
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort
        (bindOrder order (.function [.individual] order excess)) 0)
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (reducibilityExistential : ExistentialVocabulary signature
      (relationSort
        (bindOrder order (.function [.individual] order excess)) 0)
      (bindOrder
        (bindOrder
          (bindOrder order (.function [.individual] order excess))
          .individual)
        .individual))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (.function [.individual] order excess)))
    (rightUniversal : signature.Universal .individual
      (bindOrder
        (bindOrder order (.function [.individual] order excess))
        .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (.function [.individual] order excess)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder order (.function [.individual] order excess))
          .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (relationSort
          (bindOrder order (.function [.individual] order excess)) 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder
              (bindOrder order (.function [.individual] order excess))
              .individual)
            .individual)
          (relationSort
            (bindOrder order (.function [.individual] order excess)) 0))
        (bindOrder
          (max
            (bindOrder
              (bindOrder
                (bindOrder order (.function [.individual] order excess))
                .individual)
              .individual)
            (bindOrder order (.function [.individual] order excess)))
          (relationSort
            (bindOrder order (.function [.individual] order excess)) 0))))
    (vocabulary : IdentityVocabulary signature .individual order excess)
    (x y : Term signature real [] .individual) where
  derivation :
    (⊢ᵣ star_21_3_transportFormula leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation
      conjunctionDisjunction (star_50_01_matrix vocabulary) x y) →
    ⊢ᵣ mixedImplication reducibilityOuterNegation bridgeDisjunction
      (star_12_11_formula reducibilityExistential leftUniversal
        rightUniversal equivalenceNegation equivalenceDisjunction
        (star_50_01_matrix vocabulary))
      (star_50_01_application abstractionExistential leftUniversal
        rightUniversal equivalenceNegation equivalenceDisjunction
        leftNegation rightNegation outerNegation conjunctionDisjunction
        vocabulary x y)

/-- ✱50·1, by the printed specialization `[✱21·3.(✱50·01)]`.

The available ✱21·3 remains conditional on its stronger contextual transport:
`star_12_11_formula` starts with `.sometimes reducibilityExistential`, whereas
`star_50_01_application` starts with `.sometimes abstractionExistential` and a
`mixedConjunction` body.  Those trees do not reduce to one another.
`direct_assumptions: PM1:REDUCIBILITY` records the ✱12·11 vocabulary; the
logical scope-transport premise remains explicit in the theorem signature.
`demonstration_provenance: follows-printed`. -/
theorem star_50_1
    (abstractionExistential : ExistentialVocabulary signature
      (relationSort
        (bindOrder order (.function [.individual] order excess)) 0)
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (reducibilityExistential : ExistentialVocabulary signature
      (relationSort
        (bindOrder order (.function [.individual] order excess)) 0)
      (bindOrder
        (bindOrder
          (bindOrder order (.function [.individual] order excess))
          .individual)
        .individual))
    (leftUniversal : signature.Universal .individual
      (bindOrder order (.function [.individual] order excess)))
    (rightUniversal : signature.Universal .individual
      (bindOrder
        (bindOrder order (.function [.individual] order excess))
        .individual))
    (equivalenceNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (.function [.individual] order excess)))
    (leftNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder order (.function [.individual] order excess))
          .individual)
        .individual))
    (rightNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (outerNegation : signature.Negation
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (bindOrder order (.function [.individual] order excess))))
    (reducibilityOuterNegation : signature.Negation
      (bindOrder
        (bindOrder
          (bindOrder
            (bindOrder order (.function [.individual] order excess))
            .individual)
          .individual)
        (relationSort
          (bindOrder order (.function [.individual] order excess)) 0)))
    (bridgeDisjunction : signature.Disjunction
      (max
        (bindOrder
          (bindOrder
            (bindOrder
              (bindOrder order (.function [.individual] order excess))
              .individual)
            .individual)
          (relationSort
            (bindOrder order (.function [.individual] order excess)) 0))
        (bindOrder
          (max
            (bindOrder
              (bindOrder
                (bindOrder order (.function [.individual] order excess))
                .individual)
              .individual)
            (bindOrder order (.function [.individual] order excess)))
          (relationSort
            (bindOrder order (.function [.individual] order excess)) 0))))
    (finalNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder
            (bindOrder
              (bindOrder order (.function [.individual] order excess))
              .individual)
            .individual)
          (bindOrder order (.function [.individual] order excess)))
        (relationSort
          (bindOrder order (.function [.individual] order excess)) 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder
            (bindOrder
              (bindOrder order (.function [.individual] order excess))
              .individual)
            .individual)
          (bindOrder order (.function [.individual] order excess)))
        (relationSort
          (bindOrder order (.function [.individual] order excess)) 0)))
    (vocabulary : IdentityVocabulary signature .individual order excess)
    (x y : Term signature real [] .individual)
    (reducibility_scope_transport : Star50ReducibilityScopeTransport
      abstractionExistential reducibilityExistential leftUniversal
      rightUniversal equivalenceNegation equivalenceDisjunction leftNegation
      rightNegation outerNegation conjunctionDisjunction
      reducibilityOuterNegation bridgeDisjunction vocabulary x y) :
    Derivation (.assertion (star_50_01_application abstractionExistential
      leftUniversal rightUniversal equivalenceNegation equivalenceDisjunction
      leftNegation rightNegation outerNegation conjunctionDisjunction
      vocabulary x y)) := by
  have line1 := star_21_3 abstractionExistential reducibilityExistential
    leftUniversal rightUniversal equivalenceNegation equivalenceDisjunction
    leftNegation rightNegation outerNegation conjunctionDisjunction
    reducibilityOuterNegation bridgeDisjunction finalNegation finalDisjunction
    (star_50_01_matrix vocabulary) x y reducibility_scope_transport.derivation
  exact line1

/-! ## The identity relation outside the scope of ✱50·1

✱50·1 gives the ✱50·01 abstraction the whole printed equivalence as its scope.
Every later proposition of the section needs instead the bare application
`x I y`, whose scope is the ✱21·02 application alone.  Both are built from the
same ✱13·01 matrix, so the three abbreviations below name the orders that
matrix forces. -/

/-- The assigned order of `x = y`.  ✱13·01 binds a predicative function
variable, so this order is never `0`; `star_50_matrixOrder_ne_zero` records
that fact for the kernel. -/
def star_50_matrixOrder (order excess : Nat) : Nat :=
  bindOrder order (.function [.individual] order excess)

/-- The order of the two-variable closure `(x,y) : xRy .≡. x = y`. -/
def star_50_closureOrder (order excess : Nat) : Nat :=
  bindOrder (bindOrder (star_50_matrixOrder order excess) .individual)
    .individual

/-- The order assigned to the eliminated application `x I y`. -/
def star_50_applicationOrder (order excess : Nat) : Nat :=
  bindOrder
    (max (star_50_closureOrder order excess) (star_50_matrixOrder order excess))
    (relationSort (star_50_matrixOrder order excess) 0)

/-- Binding a variable never yields order zero: `bindOrder` is a maximum one
of whose members is a successor.  This is the arithmetic obstruction behind
the whole section, because `star_9_21`--`star_9_25` and their ✱10 restatements
are available at order `0` only. -/
theorem star_50_bindOrder_ne_zero (matrixOrder : Nat) (sort : RSort) :
    bindOrder matrixOrder sort ≠ 0 := by
  unfold bindOrder Max.max Nat.instMax maxOfLe
  change (if matrixOrder ≤ Nat.succ sort.height then Nat.succ sort.height
    else matrixOrder) ≠ 0
  by_cases ordering : matrixOrder ≤ Nat.succ sort.height
  · rw [if_pos ordering]
    exact fun equality => Nat.noConfusion equality
  · rw [if_neg ordering]
    intro equality
    exact ordering (Eq.mpr (congrArg (fun n => n ≤ Nat.succ sort.height) equality)
      (Nat.zero_le _))

/-- The ✱50·01 matrix therefore never has the order at which PM's quantified
scope propositions are reconstructed. -/
theorem star_50_matrixOrder_ne_zero (order excess : Nat) :
    star_50_matrixOrder order excess ≠ 0 :=
  star_50_bindOrder_ne_zero order (.function [.individual] order excess)

/-- The ✱13·01 matrix of ✱50·01 under an arbitrary further apparent context.
`star_50_01_matrix` is its closed instance; ✱50·3 needs the general one,
because there `x I x` itself stands under the binder of `(x)`. -/
def star_50_01_matrixUnder
    (vocabulary : IdentityVocabulary signature .individual order excess) :
    Formula signature real (.individual :: .individual :: apparent)
      (star_50_matrixOrder order excess) :=
  star_13_01 vocabulary (.apparent .zero) (.apparent (.succ .zero))

theorem star_50_01_matrixUnder_unfold
    (vocabulary : IdentityVocabulary signature .individual order excess) :
    star_50_01_matrixUnder (real := real) (apparent := apparent) vocabulary =
      star_13_01 vocabulary (.apparent .zero) (.apparent (.succ .zero)) := rfl

theorem star_50_01_matrix_eq_matrixUnder
    (vocabulary : IdentityVocabulary signature .individual order excess) :
    star_50_01_matrix (real := real) vocabulary =
      star_50_01_matrixUnder (apparent := []) vocabulary := rfl

/-- The logical meanings the ✱50·01 abstraction needs when its scope is the
bare ✱21·02 application.  It is the vocabulary of `star_50_01_application`
with the scope order set to the order of the matrix. -/
structure Star50ApplicationVocabulary (signature : Signature)
    (order excess : Nat) where
  identity : IdentityVocabulary signature .individual order excess
  existential : ExistentialVocabulary signature
    (relationSort (star_50_matrixOrder order excess) 0)
    (max (star_50_closureOrder order excess) (star_50_matrixOrder order excess))
  leftUniversal : signature.Universal .individual
    (star_50_matrixOrder order excess)
  rightUniversal : signature.Universal .individual
    (bindOrder (star_50_matrixOrder order excess) .individual)
  equivalenceNegation : signature.Negation (star_50_matrixOrder order excess)
  equivalenceDisjunction : signature.Disjunction
    (star_50_matrixOrder order excess)
  leftNegation : signature.Negation (star_50_closureOrder order excess)
  rightNegation : signature.Negation (star_50_matrixOrder order excess)
  outerNegation : signature.Negation
    (max (star_50_closureOrder order excess) (star_50_matrixOrder order excess))
  conjunctionDisjunction : signature.Disjunction
    (max (star_50_closureOrder order excess) (star_50_matrixOrder order excess))

/-- The printed application `x I y`: ✱50·01 eliminated by ✱21·01, with the
✱21·02 application of the abstraction variable as its whole scope.  This is
the subject of ✱50·2 to ✱50·6; ✱50·1 is the same abstraction with the
displayed equivalence in the scope instead. -/
def star_50_relationApplication
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent (star_50_applicationOrder order excess) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_50_01_matrixUnder vocabulary.identity)
    (star_21_02 (.apparent .zero) x.weaken y.weaken)

theorem star_50_relationApplication_unfold
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (x y : Term signature real apparent .individual) :
    star_50_relationApplication vocabulary x y =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_50_01_matrixUnder vocabulary.identity)
        (star_21_02 (.apparent .zero) x.weaken y.weaken) := rfl

/-! ### ✱50·02, the printed second definition of the section -/

/-- The matrix printed in the definiens of ✱50·02.  `J = −̇I` and ✱23·04 gives
`x(−̇R)y .≡. ∼(xRy)`, so the matrix of the outer abstraction is `∼(x I y)`
with ✱50·01 already eliminated at the two abstraction variables. -/
def star_50_02_matrix
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (negation : signature.Negation (star_50_applicationOrder order excess)) :
    Formula signature real (.individual :: .individual :: apparent)
      (star_50_applicationOrder order excess) :=
  .neg negation
    (star_50_relationApplication vocabulary (.apparent .zero)
      (.apparent (.succ .zero)))

theorem star_50_02_matrix_unfold
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (negation : signature.Negation (star_50_applicationOrder order excess)) :
    star_50_02_matrix (real := real) (apparent := apparent) vocabulary negation =
      .neg negation
        (star_50_relationApplication vocabulary (.apparent .zero)
          (.apparent (.succ .zero))) := rfl

/-- The ✱21·01 vocabulary at the order the eliminated `x I y` carries.  ✱50·02
abstracts over that formula, so its abstraction lives one ramified level above
`Star50ApplicationVocabulary`. -/
structure Star50DiversityVocabulary (signature : Signature)
    (order excess scopeOrder : Nat) where
  matrixNegation : signature.Negation (star_50_applicationOrder order excess)
  existential : ExistentialVocabulary signature
    (relationSort (star_50_applicationOrder order excess) 0)
    (max
      (bindOrder
        (bindOrder (star_50_applicationOrder order excess) .individual)
        .individual)
      scopeOrder)
  leftUniversal : signature.Universal .individual
    (star_50_applicationOrder order excess)
  rightUniversal : signature.Universal .individual
    (bindOrder (star_50_applicationOrder order excess) .individual)
  equivalenceNegation : signature.Negation
    (star_50_applicationOrder order excess)
  equivalenceDisjunction : signature.Disjunction
    (star_50_applicationOrder order excess)
  leftNegation : signature.Negation
    (bindOrder (bindOrder (star_50_applicationOrder order excess) .individual)
      .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max
      (bindOrder
        (bindOrder (star_50_applicationOrder order excess) .individual)
        .individual)
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max
      (bindOrder
        (bindOrder (star_50_applicationOrder order excess) .individual)
        .individual)
      scopeOrder)

/-- ✱50·02: `J = −̇I  Df`.  Diversity is an incomplete symbol exactly as `I`
is; what the definition licenses is the ✱21·01 scope of the abstraction whose
matrix is `∼(x I y)`.  No diversity-valued `Term` is introduced. -/
def star_50_02
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (diversity : Star50DiversityVocabulary signature order excess scopeOrder)
    (continuation : Formula signature real
      (relationSort (star_50_applicationOrder order excess) 0 :: apparent)
      scopeOrder) :
    Formula signature real apparent
      (bindOrder
        (max
          (bindOrder
            (bindOrder (star_50_applicationOrder order excess) .individual)
            .individual)
          scopeOrder)
        (relationSort (star_50_applicationOrder order excess) 0)) :=
  star_21_01 diversity.existential diversity.leftUniversal
    diversity.rightUniversal diversity.equivalenceNegation
    diversity.equivalenceDisjunction diversity.leftNegation
    diversity.rightNegation diversity.outerNegation
    diversity.conjunctionDisjunction
    (star_50_02_matrix vocabulary diversity.matrixNegation) continuation

theorem star_50_02_unfold
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (diversity : Star50DiversityVocabulary signature order excess scopeOrder)
    (continuation : Formula signature real
      (relationSort (star_50_applicationOrder order excess) 0 :: apparent)
      scopeOrder) :
    star_50_02 vocabulary diversity continuation =
      star_21_01 diversity.existential diversity.leftUniversal
        diversity.rightUniversal diversity.equivalenceNegation
        diversity.equivalenceDisjunction diversity.leftNegation
        diversity.rightNegation diversity.outerNegation
        diversity.conjunctionDisjunction
        (star_50_02_matrix vocabulary diversity.matrixNegation)
        continuation := rfl

/-- Audited definitional reading of the PM-VERBATIM block ✱50·02. -/
def star_50_02_reading
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (diversity : Star50DiversityVocabulary signature order excess scopeOrder)
    (continuation : Formula signature real
      [relationSort (star_50_applicationOrder order excess) 0] scopeOrder) :
    Star50Reading signature real where
  printed := PM.pmPrinted "✱50·02. J = −̇I  Df"
  parsed := .assertion (star_50_02 vocabulary diversity continuation)
  scopeReading := "The complement abstraction of ✱23·04 has the scope supplied by the continuation; its matrix is the eliminated ∼(xIy)."

/-! ### ✱50·3, printed without a demonstration -/

/-- Object formula of ✱50·3, `(x).xIx`.  The application of the incomplete
symbol stands under the binder, so its matrix is `star_50_01_matrixUnder` at
the extended apparent context. -/
def star_50_3_formula
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (universal : signature.Universal .individual
      (star_50_applicationOrder order excess)) :
    Formula signature real []
      (bindOrder (star_50_applicationOrder order excess) .individual) :=
  .always universal
    (star_50_relationApplication vocabulary
      (.apparent (.zero : Var [RSort.individual] .individual))
      (.apparent (.zero : Var [RSort.individual] .individual)))

theorem star_50_3_formula_unfold
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (universal : signature.Universal .individual
      (star_50_applicationOrder order excess)) :
    star_50_3_formula (real := real) vocabulary universal =
      .always universal
        (star_50_relationApplication vocabulary
          (.apparent (.zero : Var [RSort.individual] .individual))
          (.apparent (.zero : Var [RSort.individual] .individual))) := rfl

/-- Audited reading of ✱50·3. -/
def star_50_3_reading
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (universal : signature.Universal .individual
      (star_50_applicationOrder order excess)) :
    Star50Reading signature real where
  printed := PM.pmPrinted "✱50·3. ⊢ . (x).xIx"
  parsed := .assertion (star_50_3_formula vocabulary universal)
  scopeReading := "The apparent x of the printed generalization is the argument of both places of the eliminated identity relation."

/-! ### Why ✱50·2--✱50·6 do not close: two obstructions, both kernel-visible -/

/-- The seven roots of `Formula`, used below to compare the tree PM's later
sections require with the tree ✱50·01 actually produces. -/
private inductive Star50Root where
  | proposition
  | apply
  | neg
  | disj
  | always
  | incompleteScope
  | descriptionScope

private def star50Root :
    Formula signature real apparent order → Star50Root
  | .proposition _ => .proposition
  | .apply _ _ => .apply
  | .neg _ _ => .neg
  | .disj _ _ _ => .disj
  | .always _ _ => .always
  | .incompleteScope _ _ _ _ _ _ _ => .incompleteScope
  | .descriptionScope _ _ _ _ _ => .descriptionScope

/-- First obstruction, at the level of `Term`.  Every term of relation sort is
a real variable, an apparent variable, or a signature symbol: `Term` has no
abstraction constructor.  `Cnv` (✱31·02), the relative product (✱34·01) and
the restrictions (✱35·01--·02) all take a relation `Term` as argument, so the
incomplete symbol `I` can never be supplied to them, and the printed subjects
`CnvʻI`, `R | I`, `α ◁ I`, `I ▷ α` are not formable at all. -/
theorem star_50_relation_terms_are_atomic
    (relation : Term signature real apparent
      (relationSort resultOrder relationExcess)) :
    (∃ v : Var real (relationSort resultOrder relationExcess),
        relation = .real v) ∨
      (∃ v : Var apparent (relationSort resultOrder relationExcess),
        relation = .apparent v) ∨
      (∃ s : signature.Symbol (relationSort resultOrder relationExcess),
        relation = .symbol s) := by
  cases relation with
  | real v => exact Or.inl ⟨v, rfl⟩
  | apparent v => exact Or.inr (Or.inl ⟨v, rfl⟩)
  | symbol payload => exact Or.inr (Or.inr ⟨payload, rfl⟩)

/-- Second obstruction, at the level of `Formula`.  The eliminated `x I y` is
rooted at `Formula.neg`, because ✱10·01 turns the ✱21·01 existential into
`∼(R).∼…`. -/
theorem star_50_relationApplication_root
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (x y : Term signature real apparent .individual) :
    star50Root (star_50_relationApplication vocabulary x y) = .neg := rfl

/-- A genuine relation application ✱21·02 is rooted at `Formula.apply`.  Hence
no unfolding identifies `x I y` with an application of a relation term: the
two trees differ at the root constructor. -/
theorem star_50_relationApplication_ne_star_21_02
    (vocabulary : Star50ApplicationVocabulary signature order excess)
    (relation : Term signature real apparent
      (relationSort (star_50_applicationOrder order excess) 0))
    (x y u v : Term signature real apparent .individual) :
    star_50_relationApplication vocabulary x y ≠ star_21_02 relation u v := by
  intro equality
  have rootEquality := congrArg star50Root equality
  cases rootEquality

/-!
## Exact stopping point for ✱50·2--✱50·6

Nothing from this range is asserted, and the two theorems above say why.

*Not formable.*  ✱50·2 (`I = CnvʻI`), ✱50·4 (`R | I = I | R = R`),
✱50·5 (`α ◁ I = I ▷ α = α ◁ I ▷ α`) and ✱50·6 (`R | (I ▷ α) = R ▷ α`) all put
`I` in an argument place that the ramified syntax reserves for a `Term` of
relation sort — `star_31_02`, `star_34_01`, `star_35_01` and `star_35_02` are
each declared with `relation : Term signature real apparent (relationSort …)`.
By `star_50_relation_terms_are_atomic` such a term is a variable or a symbol,
while `star_50_relationApplication` is a `Formula` rooted at `Formula.neg`
(`star_50_relationApplication_root`).  The printed subject therefore has no
AST here, and no equality between trees is even statable.  Supplying a fresh
relation symbol for `I` would be exactly the move ✱50·01 forbids: PM defines
`I` by a `Df`, so it is an incomplete symbol, not a primitive.

*Formable but not derivable.*  ✱50·3 is `star_50_3_formula`, exactly the tree
above, and it is the one printed proposition of the range with no `Dem.`  The
route an editorial reconstruction has to take is: ✱12·11 gives
`(∃f) : (z,w). (z = w) .≡. f(z,w)`; ✱11·1 gives, for a real relation variable
`R`, `(z,w) : (z = w) .≡. R(z,w) : ⊃ : (x = x) .≡. R(x,x)`; ✱13·15 gives
`x = x`; so `R(x,x)` follows for that real `R`, and ✱10·11 generalizes it.
The step that then has to be made is from `(∃f). Φf` to `(∃R). Ψ R` given
`(R). Φ R ⊃ Ψ R`, i.e. ✱10·28.  In this reconstruction `star_10_28` is
`star_9_22`, and `star_9_22` — like `star_9_21`, `star_9_23`, `star_9_24`,
`star_9_25` and every ✱9·3--✱9·5 restatement — is declared with
`universal : signature.Universal argument 0`: it exists at matrix order `0`
alone.  The matrix here is `star_50_01_matrix`, whose order is
`star_50_matrixOrder order excess`, and `star_50_matrixOrder_ne_zero` shows
that order is never `0`.  So the printed inference has no instance at the
order PM's own ✱13·01 forces, and ✱50·3 is left underived rather than
assumed.

The same arithmetic is what keeps ✱50·1 conditional: its
`Star50ReducibilityScopeTransport` premise is an instance of exactly that
scope inference, taken at `star_50_matrixOrder order excess` rather than at
`0`, and it is left standing rather than assumed away.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_50_1
#print axioms PM.RamifiedSyntax.star_50_bindOrder_ne_zero
#print axioms PM.RamifiedSyntax.star_50_matrixOrder_ne_zero
#print axioms PM.RamifiedSyntax.star_50_01_matrixUnder_unfold
#print axioms PM.RamifiedSyntax.star_50_01_matrix_eq_matrixUnder
#print axioms PM.RamifiedSyntax.star_50_relationApplication_unfold
#print axioms PM.RamifiedSyntax.star_50_02_matrix_unfold
#print axioms PM.RamifiedSyntax.star_50_02_unfold
#print axioms PM.RamifiedSyntax.star_50_02_reading
#print axioms PM.RamifiedSyntax.star_50_3_formula_unfold
#print axioms PM.RamifiedSyntax.star_50_3_reading
#print axioms PM.RamifiedSyntax.star_50_relation_terms_are_atomic
#print axioms PM.RamifiedSyntax.star_50_relationApplication_root
#print axioms PM.RamifiedSyntax.star_50_relationApplication_ne_star_21_02
