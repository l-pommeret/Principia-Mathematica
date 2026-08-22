import Principia.Deduction.Star10Derived
import Principia.Deduction.Star12Derived
import Principia.Deduction.Star20Derived
import Principia.FirstEdition.Volume1.Star52Source
import Principia.Syntax.Printed

namespace PM.RamifiedSyntax

/-- T4 reading specialized to the ramified claims of ✱52. -/
structure Star52Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-!
# Derived propositions of PM I, ✱52

✱52·01 is the systematic-ambiguity instance of class abstraction whose
argument is itself a class.  The unary abstraction machinery is therefore
written with its argument sort explicit; no class-valued `Term` or new
primitive is introduced.
-/

/-- ✱52·01: the contextual class abstraction of the displayed matrix
`(∃x). α = ιʻx`.  The matrix is syntax data supplied at its exact ramified
order; the abstraction remains an incomplete symbol with a continuation. -/
def star_52_01
    (existential : ExistentialVocabulary signature
      (.function [elementSort] resultOrder 0)
      (max (bindOrder resultOrder elementSort) scopeOrder))
    (universal : signature.Universal elementSort resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder elementSort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder elementSort) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder elementSort) scopeOrder))
    (matrix : Formula signature real (elementSort :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [elementSort] resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder (max (bindOrder resultOrder elementSort) scopeOrder)
        (.function [elementSort] resultOrder 0)) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      continuation)

/-- The printed definition ✱52·01 is eliminable. -/
theorem star_52_01_unfold
    (existential : ExistentialVocabulary signature
      (.function [elementSort] resultOrder 0)
      (max (bindOrder resultOrder elementSort) scopeOrder))
    (universal : signature.Universal elementSort resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder elementSort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder elementSort) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder elementSort) scopeOrder))
    (matrix : Formula signature real (elementSort :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [elementSort] resultOrder 0 :: apparent) scopeOrder) :
    star_52_01 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          (.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (matrix.rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

/-- The predicative class variable used on the ✱10·43 specialization line
of the systematic-ambiguity instance of ✱20·3. -/
def star_52_1_predicateMatrix
    (_matrix : Formula signature real [elementSort] resultOrder) :
    Formula signature
      (.function [elementSort] resultOrder 0 :: real) [elementSort]
      resultOrder :=
  applyUnary
    (.real (.zero : Var
      (.function [elementSort] resultOrder 0 :: real)
      (.function [elementSort] resultOrder 0)))
    (.apparent .zero)

/-- Exact ✱10·43 specialization used in ✱52·1. -/
def star_52_1_transportFormula
    (universal : signature.Universal elementSort resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (outerNegation : signature.Negation
      (bindOrder resultOrder elementSort))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder resultOrder elementSort) resultOrder))
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) :
    Formula signature
      (.function [elementSort] resultOrder 0 :: real) []
      (max (bindOrder resultOrder elementSort) resultOrder) :=
  mixedImplication outerNegation outerDisjunction
    (.always universal
      (equivalence equivalenceNegation equivalenceDisjunction
        (star_52_1_predicateMatrix matrix) matrix.weakenReal))
    ((equivalence equivalenceNegation equivalenceDisjunction
      (star_52_1_predicateMatrix matrix) matrix.weakenReal).instantiate
        element.weakenReal)

/-- The continuation `α ∈ 1 ≡ (∃x).α=ιʻx` obtained from membership
and the matrix of ✱52·01. -/
def star_52_1_continuation
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) :
    Formula signature real
      [.function [elementSort] resultOrder 0] resultOrder :=
  equivalence equivalenceNegation equivalenceDisjunction
    (applyUnary (.apparent .zero) element.weaken)
    ((matrix.instantiate element).rename
      (emptyRenaming
        (target := [.function [elementSort] resultOrder 0])))

/-- Object formula of ✱52·1 after eliminating ✱52·01. -/
def star_52_1_formula
    (existential : ExistentialVocabulary signature
      (.function [elementSort] resultOrder 0)
      (max (bindOrder resultOrder elementSort) resultOrder))
    (universal : signature.Universal elementSort resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder elementSort))
    (rightNegation : signature.Negation resultOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder elementSort) resultOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder elementSort) resultOrder))
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) :=
  star_52_01 existential universal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction matrix
    (star_52_1_continuation equivalenceNegation equivalenceDisjunction
      matrix element)

/-- The full vocabulary required by the ✱52·1 instance of ✱20·3. -/
structure Star52EliminationVocabulary (signature : Signature)
    (elementSort : RSort) (resultOrder : Nat) where
  abstractionExistential : ExistentialVocabulary signature
    (.function [elementSort] resultOrder 0)
    (max (bindOrder resultOrder elementSort) resultOrder)
  reducibilityExistential : ExistentialVocabulary signature
    (.function [elementSort] resultOrder 0)
    (bindOrder resultOrder elementSort)
  universal : signature.Universal elementSort resultOrder
  equivalenceNegation : signature.Negation resultOrder
  equivalenceDisjunction : signature.Disjunction resultOrder
  leftNegation : signature.Negation
    (bindOrder resultOrder elementSort)
  rightNegation : signature.Negation resultOrder
  outerNegation : signature.Negation
    (max (bindOrder resultOrder elementSort) resultOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder resultOrder elementSort) resultOrder)
  reducibilityOuterNegation : signature.Negation
    (bindOrder (bindOrder resultOrder elementSort)
      (.function [elementSort] resultOrder 0))
  bridgeDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder resultOrder elementSort)
        (.function [elementSort] resultOrder 0))
      (bindOrder (max (bindOrder resultOrder elementSort) resultOrder)
        (.function [elementSort] resultOrder 0)))
  finalNegation : signature.Negation
    (bindOrder (max (bindOrder resultOrder elementSort) resultOrder)
      (.function [elementSort] resultOrder 0))
  finalDisjunction : signature.Disjunction
    (bindOrder (max (bindOrder resultOrder elementSort) resultOrder)
      (.function [elementSort] resultOrder 0))

/-- The still-missing contextual transport from unary reducibility to the
expanded ✱52·01 abstraction.  It is stronger than the proved order-zero
object equivalence ✱10·35. -/
def Star52ReducibilityScopeTransport
    (vocabulary : Star52EliminationVocabulary signature elementSort resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) : Prop :=
  (⊢ᵣ star_52_1_transportFormula vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.conjunctionDisjunction matrix element) →
  ⊢ᵣ mixedImplication vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction
    (star_12_1_formula vocabulary.reducibilityExistential
      vocabulary.universal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction matrix)
    (star_52_1_formula vocabulary.abstractionExistential
      vocabulary.universal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction matrix element)

/-- Audited reading of ✱52·1. -/
def star_52_1_reading
    (vocabulary : Star52EliminationVocabulary signature elementSort resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) :
    Star52Reading signature real where
  printed := PM.pmPrinted
    "✱52·1.  ⊢ : α ∈ 1 .≡. (∃x). α = ιʻx  [✱20·3.(✱52·01)]"
  parsed := .assertion
    (star_52_1_formula vocabulary.abstractionExistential
      vocabulary.universal vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction vocabulary.leftNegation
      vocabulary.rightNegation vocabulary.outerNegation
      vocabulary.conjunctionDisjunction matrix element)
  scopeReading := "The abstraction variable α has the assigned class sort; ✱20·3 is instantiated by systematic ambiguity at that sort."

/-- ✱52·1, by the printed `[✱20·3.(✱52·01)]` route.

The generalized ✱20·3 is instantiated at `elementSort`; unfolding ✱52·01
then identifies its contextual abstraction with the displayed formula.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`.
`demonstration_provenance: follows-printed`. -/
theorem star_52_1
    (vocabulary : Star52EliminationVocabulary signature elementSort resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort)
    (reducibility_scope_transport : PM.RamifiedSyntax.Star52ReducibilityScopeTransport vocabulary
      matrix element) :
    Derivation (.assertion
      (star_52_1_formula vocabulary.abstractionExistential
        vocabulary.universal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction matrix element)) := by
  have line1 := star_20_3 vocabulary.abstractionExistential
    vocabulary.reducibilityExistential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction vocabulary.reducibilityOuterNegation
    vocabulary.bridgeDisjunction vocabulary.finalNegation
    vocabulary.finalDisjunction matrix element reducibility_scope_transport
  have line2 := congrArg
    (fun continuation =>
      star_52_01 vocabulary.abstractionExistential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction matrix
        continuation)
    (show star_52_1_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction matrix element =
      star_20_3_continuation vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction matrix element from rfl)
  exact Derivation.castAssertion line2 line1

/-! ## The membership formula the later propositions are about

✱52·1 gives the ✱52·01 abstraction the whole printed equivalence as its scope.
✱52·2 and everything after it need instead the bare membership `α ∈ 1`, whose
scope is the ✱20·02 application alone. -/

/-- `α ∈ 1`: ✱52·01 eliminated by ✱20·01, with the ✱20·02 application of the
abstraction variable as its whole scope.  As in ✱52·1 the matrix is supplied
as syntax data, because `(∃x). α = ιʻx` still needs the descriptive function
`ιʻ` of ✱30·01 and ✱51·11. -/
def star_52_membership
    (vocabulary : Star52EliminationVocabulary signature elementSort resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) :=
  star_52_01 vocabulary.abstractionExistential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction matrix
    (applyUnary (.apparent .zero) element.weaken)

theorem star_52_membership_unfold
    (vocabulary : Star52EliminationVocabulary signature elementSort resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) :
    star_52_membership vocabulary matrix element =
      star_52_01 vocabulary.abstractionExistential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction matrix
        (applyUnary (.apparent .zero) element.weaken) := rfl

/-! ### Why ✱52·2--✱52·4 do not close -/

/-- The seven roots of `Formula`. -/
private inductive Star52Root where
  | proposition
  | apply
  | neg
  | disj
  | always
  | incompleteScope
  | descriptionScope

private def star52Root :
    Formula signature real apparent order → Star52Root
  | .proposition _ => .proposition
  | .apply _ _ => .apply
  | .neg _ _ => .neg
  | .disj _ _ _ => .disj
  | .always _ _ => .always
  | .incompleteScope _ _ _ _ _ _ _ => .incompleteScope
  | .descriptionScope _ _ _ _ _ => .descriptionScope

/-- `Term` has exactly three constructors and none of them is an abstraction.
Whatever the sort — including a class of classes — a term is a real variable,
an apparent variable, or a signature symbol. -/
theorem star_52_terms_are_atomic
    (term : Term signature real apparent sort) :
    (∃ v : Var real sort, term = .real v) ∨
      (∃ v : Var apparent sort, term = .apparent v) ∨
      (∃ s : signature.Symbol sort, term = .symbol s) := by
  cases term with
  | real v => exact Or.inl ⟨v, rfl⟩
  | apparent v => exact Or.inr (Or.inl ⟨v, rfl⟩)
  | symbol payload => exact Or.inr (Or.inr ⟨payload, rfl⟩)

/-- `α ∈ 1` is rooted at `Formula.neg`: ✱10·01 turns the ✱20·01 existential
into `∼(φ).∼…`. -/
theorem star_52_membership_root
    (vocabulary : Star52EliminationVocabulary signature elementSort resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort) :
    star52Root (star_52_membership vocabulary matrix element) = .neg := rfl

/-- A genuine ✱20·02 membership is rooted at `Formula.apply`.  So `1` is not
the class term that ✱22·01 inclusion, ✱22·02 intersection and ✱22·03 union
require in ✱52·2, ✱52·3 and ✱52·4: the two trees differ at the root. -/
theorem star_52_membership_ne_application
    (vocabulary : Star52EliminationVocabulary signature elementSort resultOrder)
    (matrix : Formula signature real [elementSort] resultOrder)
    (element : Term signature real [] elementSort)
    (classTerm : Term signature real []
      (.function [elementSort]
        (bindOrder (max (bindOrder resultOrder elementSort) resultOrder)
          (.function [elementSort] resultOrder 0)) 0))
    (argument : Term signature real [] elementSort) :
    star_52_membership vocabulary matrix element ≠
      applyUnary classTerm argument := by
  intro equality
  have rootEquality := congrArg star52Root equality
  cases rootEquality

/-!
## Exact stopping point for ✱52·2--✱52·4

✱52·2 reads `1 ⊂ Cls`.  Inclusion is ✱22·01, whose reconstruction is
`.always universal (implication … (star_20_02 alpha.weaken _) (star_20_02
beta.weaken _))` with `alpha beta : Term signature real [] (classSort order 0)`.
Both `1` (✱52·01) and `Cls` (✱20·03) are contextual class abstractions, hence
`Formula`s rooted at `Formula.neg` — `star_52_membership_root` — and by
`star_52_terms_are_atomic` no term of any sort can be one of them.  So the
printed subject of ✱52·2 has no AST here at all, and
`star_52_membership_ne_application` shows that supplying a class term instead
would assert a different tree.  The same holds of ✱52·21 (`Λ ∼∈ 1`), ✱52·23
(`∃!1 . ∃!−1`), ✱52·3 (`ιʻʻα ⊂ 1`), ✱52·31 and ✱52·4 (`α ∈ 1 ∪ ιʻΛ`), each of
which places `1`, `Λ`, `ιʻx` or `ιʻʻα` in a class-`Term` argument place.

✱52·22 (`ιʻx ∈ 1`) is the one member of the range whose subject could be
formed, since `star_52_membership` takes its element as a term; but its
printed citation is `[✱51·12.✱14·28.✱10·24.✱52·1]`, and `Star51Derived`
declares no `star_51_12` — `E!ιʻx` needs the descriptive function ✱30·01 with
✱30·3, which `Star30Derived` stops short of.

Underneath all of this is the same arithmetic recorded at the end of
`Star50Derived`: PM's scope propositions ✱10·27 and ✱10·28 are reconstructed
here as `star_9_21` and `star_9_22`, both declared at matrix order `0` only,
whereas every matrix in ✱50 to ✱52 is built over a ✱13·01 identity whose order
is a `bindOrder` and therefore never `0`.  That is why ✱52·1 itself keeps its
`Star52ReducibilityScopeTransport` premise, and why nothing after it is
asserted.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_52_01_unfold
#print axioms PM.RamifiedSyntax.star_52_1
#print axioms PM.RamifiedSyntax.star_52_membership_unfold
#print axioms PM.RamifiedSyntax.star_52_terms_are_atomic
#print axioms PM.RamifiedSyntax.star_52_membership_root
#print axioms PM.RamifiedSyntax.star_52_membership_ne_application
