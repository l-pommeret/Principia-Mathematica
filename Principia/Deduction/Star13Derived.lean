import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star10Derived
import Principia.Deduction.Star12Derived
import Principia.FirstEdition.Volume1.Star13

namespace PM.RamifiedSyntax

private theorem star13_detach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons head tail => exact Derivation.star_1_11_same negation disjunction

/-! The full-scope ✱10·3 matrix used in the printed proof of ✱13·17. -/

private def star13_apparentConjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation left) (.neg negation right))

private theorem star13_apparentConjunction_weakenReal
    {fresh : RSort}
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (star13_apparentConjunction negation disjunction left right).weakenReal
        (fresh := fresh) =
      star13_apparentConjunction negation disjunction
        (left.weakenReal (fresh := fresh))
        (right.weakenReal (fresh := fresh)) := by
  unfold star13_apparentConjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  rfl

private theorem star13_apparentConjunction_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (star13_apparentConjunction negation disjunction left right).substitute sigma =
      star13_apparentConjunction negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold star13_apparentConjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).substitute sigma) = _
  rw [sameDisjunction_substitute]
  rfl

private def star13_star_10_3_formula
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [argument] order) :
    Formula signature real [] (bindOrder order argument) :=
  .always universal
    (implication negation disjunction
      (star13_apparentConjunction negation disjunction
        (implication negation disjunction phi psi)
        (implication negation disjunction psi chi))
      (implication negation disjunction phi chi))

/-- The ✱10·3 instance needed at ✱13·17, reconstructed by pointwise
`Syll` and the primitive generalization rule ✱10·11. -/
private theorem star13_star_10_3
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [argument] order) :
    ⊢ᵣ star13_star_10_3_formula universal negation disjunction phi psi chi := by
  let body := implication negation disjunction
    (star13_apparentConjunction negation disjunction
      (implication negation disjunction phi psi)
      (implication negation disjunction psi chi))
    (implication negation disjunction phi chi)
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 : ⊢ᵣ body.weakenReal.instantiate value := by
    unfold body
    rw [implication_weakenReal, star13_apparentConjunction_weakenReal,
      Formula.instantiate, implication_substitute,
      star13_apparentConjunction_substitute]
    unfold star13_apparentConjunction
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    exact star_3_33 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/-!
# Definitions of PM I, ✱13

Identity itself remains exactly `star_13_01`, the reducible Leibniz
definition in `Principia.Syntax.Ramified`.  The two following declarations are
likewise eliminable definitions; neither adds a constructor to `Derivation`.
-/

/-- ✱13·02: diversity is the eliminable negation of Leibniz identity. -/
def star_13_02
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real apparent sort) :
    Formula signature real apparent
      (bindOrder order (.function [sort] order excess)) :=
  .neg negation (star_13_01 vocabulary x y)

/-- ✱13·03: chained identity is the eliminable conjunction of the two
adjacent Leibniz identities. -/
def star_13_03
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real apparent sort) :
    Formula signature real apparent
      (bindOrder order (.function [sort] order excess)) :=
  .neg negation (sameDisjunction disjunction
    (.neg negation (star_13_01 vocabulary x y))
    (.neg negation (star_13_01 vocabulary y z)))

/-- Audited scope reading of ✱13·01.  Identity is the reducible Leibniz
definition, not Lean equality. -/
def star_13_01_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "x = y .=: (φ) : φ!x .⊃ . φ!y  Df"
  parsed := .assertion (star_13_01 vocabulary x y)

/-- Audited scope reading of ✱13·02. -/
def star_13_02_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "x ≠ y .=. ∼(x = y)  Df"
  parsed := .assertion (star_13_02 vocabulary negation x y)

/-- Audited scope reading of ✱13·03. -/
def star_13_03_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort) : ClaimReading signature real where
  printed := "x = y = z .=. x = y . y = z  Df"
  parsed := .assertion (star_13_03 vocabulary negation disjunction x y z)

/-- Printed left member of ✱13·1, built from the defined identity sign. -/
def star_13_1_left
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) :=
  star_13_01 vocabulary x y

/-- Printed right member of ✱13·1, built directly as Leibniz's quantified
implication rather than by reusing the left-member definition. -/
def star_13_1_right
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (bindOrder order (.function [sort] order excess)) :=
  .always vocabulary.universal
    (implication vocabulary.negation vocabulary.disjunction
      (applyUnary (.apparent .zero) x.weaken)
      (applyUnary (.apparent .zero) y.weaken))

theorem star_13_1_left_unfold
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) :
    star_13_1_left vocabulary x y = star_13_1_right vocabulary x y := rfl

/-- Audited scope reading of ✱13·1. -/
def star_13_1_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ :: x = y .≡ : φ!x .⊃φ . φ!y"
  parsed := .assertion (star_4_01 negation disjunction
    (star_13_1_left vocabulary x y) (star_13_1_right vocabulary x y))

/-- ✱13·1, exactly ✱4·2 after unfolding the Leibniz definition ✱13·01.
`demonstration_provenance: follows-printed`. -/
theorem star_13_1
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) :
    Derivation (star_13_1_reading vocabulary negation disjunction x y).parsed := by
  have line1 := star_4_2 negation disjunction (star_13_1_right vocabulary x y)
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_13_1_left vocabulary x y) (star_13_1_right vocabulary x y)))
  rw [star_13_1_left_unfold]
  exact line1

/-- Object formula asserted at ✱13·101.  The arbitrary `ψ` has the order
used by the predicative representative supplied through ✱12·1. -/
def star_13_101_formula
    (vocabulary : IdentityVocabulary signature sort order 0)
    (outerNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (max (bindOrder order (.function [sort] order 0)) order) :=
  mixedImplication outerNegation outerDisjunction
    (star_13_01 vocabulary x y)
    (implication vocabulary.negation vocabulary.disjunction
      (psi.instantiate x) (psi.instantiate y))

/-- Audited scope reading of ✱13·101. -/
def star_13_101_reading
    (vocabulary : IdentityVocabulary signature sort order 0)
    (outerNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y .⊃ . ψx .⊃ . ψy"
  parsed := .assertion (star_13_101_formula vocabulary outerNegation
    outerDisjunction psi x y)

/-- ✱13·101, with printed line (1) discharged by ✱12·1.

`star_10_27_hypothesis` is the still-missing specialized line (2), whose
printed construction is ✱13·1, ✱4·84·85, ✱10·27 and ✱10·23.  It is an
implication from the exact ✱12·1 existential assertion, not an assumption of
the conclusion itself.  `assumptions: PM1:REDUCIBILITY` records the
non-logical primitive used on line (1).
`demonstration_provenance: follows-printed`. -/
theorem star_13_101
    (vocabulary : IdentityVocabulary signature sort order 0)
    (reducibilityExistential : ExistentialVocabulary signature
      (.function [sort] order 0) (bindOrder order sort))
    (argumentUniversal : signature.Universal sort order)
    (outerNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order 0)) order))
    (reducibilityNegation : signature.Negation
      (bindOrder (bindOrder order sort) (.function [sort] order 0)))
    (bridgeDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder order sort) (.function [sort] order 0))
        (max (bindOrder order (.function [sort] order 0)) order)))
    (psi : Formula signature real [sort] order)
    (x y : Term signature real [] sort)
    (star_10_27_hypothesis : ⊢ᵣ mixedImplication reducibilityNegation
      bridgeDisjunction
      (star_12_1_formula reducibilityExistential argumentUniversal
        vocabulary.negation vocabulary.disjunction psi)
      (star_13_101_formula vocabulary outerNegation outerDisjunction
        psi x y)) :
    Derivation (star_13_101_reading vocabulary outerNegation
      outerDisjunction psi x y).parsed := by
  have line1 := star_12_1 reducibilityExistential argumentUniversal
    vocabulary.negation vocabulary.disjunction psi
  have line2 := star_10_27_hypothesis
  exact Derivation.star_9_12 reducibilityNegation bridgeDisjunction line1 line2

/-- Audited scope reading of ✱13·15. -/
def star_13_15_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ . x = x"
  parsed := .assertion (star_13_01 vocabulary x x)

/-- ✱13·15.  This follows the printed `Id.✱10·11.✱13·1` citation.
`demonstration_provenance: follows-printed`. -/
theorem star_13_15
    (vocabulary : IdentityVocabulary signature sort order excess)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x : Term signature real [] sort) :
    Derivation (star_13_15_reading vocabulary x).parsed := by
  let predicate : Term signature real
      (.function [sort] order excess :: [])
      (.function [sort] order excess) := .apparent .zero
  let body := implication vocabulary.negation vocabulary.disjunction
    (applyUnary predicate x.weaken) (applyUnary predicate x.weaken)
  let value : Term signature (.function [sort] order excess :: real) []
      (.function [sort] order excess) :=
    .real (.zero : Var (.function [sort] order excess :: real)
      (.function [sort] order excess))
  let matrixInstance := (applyUnary predicate x.weaken).weakenReal.instantiate value
  have matrixEq : body.weakenReal.instantiate value =
      implication vocabulary.negation vocabulary.disjunction matrixInstance matrixInstance := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    rfl
  have line1 : ⊢ᵣ body.weakenReal.instantiate value := by
    exact Derivation.castAssertion matrixEq
      (star_2_08 vocabulary.negation vocabulary.disjunction matrixInstance)
  have line2 : ⊢ᵣ star_13_01 vocabulary x x := by
    exact star_10_11 vocabulary.universal body line1
  have line3 := star_13_1 vocabulary identityNegation
    identityDisjunction x x
  exact star13_detach identityNegation identityDisjunction _ _ line2
    (star13_detach identityNegation identityDisjunction _ _ line3
      (star_3_26 identityNegation identityDisjunction _ _))

/-!
The remaining assertions in this section are recorded at their exact
ramified propositional envelopes.  Their named hypotheses are intentional:
the unconditional ✱13·101 substitution theorem, on which the printed chain
depends, has not yet been reconstructed in `Derivation`.  Consequently none
of these declarations is presented as an unconditional derivation.
-/

/-- Audited scope reading of ✱13·11. -/
def star_13_11_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (formallyEquivalentUnderPhi : Formula signature real []
      (bindOrder order (.function [sort] order excess))) :
    ClaimReading signature real where
  printed := "⊢ :: x = y .≡ : φ!x .≡φ . φ!y"
  parsed := .assertion (star_4_01 negation disjunction
    (star_13_01 vocabulary x y) formallyEquivalentUnderPhi)

/-- ✱13·11 remains explicitly asserted pending the printed ✱13·101 chain.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_11
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (formallyEquivalentUnderPhi : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (star_13_11_hypothesis : Derivation
      (star_13_11_reading vocabulary negation disjunction x y
        formallyEquivalentUnderPhi).parsed) :
    Derivation (star_13_11_reading vocabulary negation disjunction x y
      formallyEquivalentUnderPhi).parsed := by
  have line1 := star_13_11_hypothesis
  exact line1

/-- Audited scope reading of ✱13·12. -/
def star_13_12_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (psiX psiY : Formula signature real []
      (bindOrder order (.function [sort] order excess))) :
    ClaimReading signature real where
  printed := "⊢ : x = y .⊃ . ψx .≡ . ψy"
  parsed := .assertion (implication negation disjunction
    (star_13_01 vocabulary x y)
    (star_4_01 negation disjunction psiX psiY))

/-- ✱13·12 remains explicitly asserted pending ✱13·101.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_12
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (psiX psiY : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (star_13_12_hypothesis : Derivation
      (star_13_12_reading vocabulary negation disjunction x y psiX psiY).parsed) :
    Derivation
      (star_13_12_reading vocabulary negation disjunction x y psiX psiY).parsed := by
  have line1 := star_13_12_hypothesis
  exact line1

/-- Audited scope reading of ✱13·16. -/
def star_13_16_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y .≡ . y = x"
  parsed := .assertion (star_4_01 negation disjunction
    (star_13_01 vocabulary x y) (star_13_01 vocabulary y x))

/-- ✱13·16, explicitly asserted until the ✱13·12 instance is available.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_16
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (star_13_16_hypothesis : Derivation
      (star_13_16_reading vocabulary negation disjunction x y).parsed) :
    Derivation (star_13_16_reading vocabulary negation disjunction x y).parsed := by
  have line1 := star_13_16_hypothesis
  exact line1

/-- Audited scope reading of ✱13·17. -/
def star_13_17_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y z : Term signature real [] sort) : ClaimReading signature real :=
  let predicate : Term signature real
      [.function [sort] order excess]
      (.function [sort] order excess) := .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let phiZ := applyUnary predicate z.weaken
  {
    printed := "⊢ : x = y . y = z .⊃ . x = z"
    parsed := .assertion (star13_star_10_3_formula vocabulary.universal
      vocabulary.negation vocabulary.disjunction phiX phiY phiZ)
  }

/-- ✱13·17, following the printed ✱13·1, ✱10·3 chain.  Unfolding the
Leibniz definition turns the assertion into the full-scope `Syll` matrix;
✱10·11 then generalizes over the same bound propositional function.
`demonstration_provenance: follows-printed`. -/
theorem star_13_17
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y z : Term signature real [] sort) :
    Derivation (star_13_17_reading vocabulary x y z).parsed := by
  let predicate : Term signature real
      [.function [sort] order excess]
      (.function [sort] order excess) := .apparent .zero
  let phiX := applyUnary predicate x.weaken
  let phiY := applyUnary predicate y.weaken
  let phiZ := applyUnary predicate z.weaken
  have line1 := star13_star_10_3 vocabulary.universal vocabulary.negation
    vocabulary.disjunction phiX phiY phiZ
  exact line1

/-- Audited scope reading of ✱13·171. -/
def star_13_171_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y . x = z .⊃ . y = z"
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction
      (star_13_01 vocabulary x y) (star_13_01 vocabulary x z))
    (star_13_01 vocabulary y z))

/-- ✱13·171 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_171
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort)
    (star_13_171_hypothesis : Derivation
      (star_13_171_reading vocabulary negation disjunction x y z).parsed) :
    Derivation
      (star_13_171_reading vocabulary negation disjunction x y z).parsed := by
  have line1 := star_13_171_hypothesis
  exact line1

/-- Audited scope reading of ✱13·18. -/
def star_13_18_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y . x ≠ z .⊃ . y ≠ z"
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction
      (star_13_01 vocabulary x y)
      (star_13_02 vocabulary negation x z))
    (star_13_02 vocabulary negation y z))

/-- ✱13·18 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_18
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort)
    (star_13_18_hypothesis : Derivation
      (star_13_18_reading vocabulary negation disjunction x y z).parsed) :
    Derivation
      (star_13_18_reading vocabulary negation disjunction x y z).parsed := by
  have line1 := star_13_18_hypothesis
  exact line1

/-- Audited scope reading of ✱13·181. -/
def star_13_181_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : x = y . y ≠ z .⊃ . x ≠ z"
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction
      (star_13_01 vocabulary x y)
      (star_13_02 vocabulary negation y z))
    (star_13_02 vocabulary negation x z))

/-- ✱13·181 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_181
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y z : Term signature real [] sort)
    (star_13_181_hypothesis : Derivation
      (star_13_181_reading vocabulary negation disjunction x y z).parsed) :
    Derivation
      (star_13_181_reading vocabulary negation disjunction x y z).parsed := by
  have line1 := star_13_181_hypothesis
  exact line1

/-- Audited scope reading of ✱13·19. -/
def star_13_19_reading
    (existential : ExistentialVocabulary signature sort
      (bindOrder order (.function [sort] order excess)))
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ . (∃y). y = x"
  parsed := .assertion (.sometimes existential
    (star_13_01 vocabulary
      (.apparent (.zero : Var [sort] sort)) x.weaken))

/-- ✱13·19, following the printed ✱13·15, ✱10·24 citation.  The
specialization equation below only verifies that the displayed witness is
exactly `x`.
`demonstration_provenance: follows-printed`. -/
theorem star_13_19
    (existential : ExistentialVocabulary signature sort
      (bindOrder order (.function [sort] order excess)))
    (vocabulary : IdentityVocabulary signature sort order excess)
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (existentialDisjunction : signature.Disjunction
      (max (bindOrder order (.function [sort] order excess))
        (bindOrder (bindOrder order (.function [sort] order excess)) sort)))
    (x : Term signature real [] sort) :
    Derivation (star_13_19_reading existential vocabulary x).parsed := by
  let body := star_13_01 vocabulary
    (.apparent (.zero : Var [sort] sort)) x.weaken
  have line1 := star_13_15 vocabulary identityNegation
    identityDisjunction x
  have line2 := star_10_24 existential identityNegation
    existentialDisjunction body x
  have bodyEq : body.instantiate x = star_13_01 vocabulary x x := by
    unfold body star_13_01
    rw [Formula.instantiate, substitute_always, implication_substitute]
    cases x <;> rfl
  have line2' := Derivation.castAssertion
    (congrArg (fun antecedent => mixedImplication identityNegation
      existentialDisjunction antecedent (.sometimes existential body)) bodyEq).symm
    line2
  exact Derivation.star_9_12 identityNegation existentialDisjunction line1 line2'

/-- Audited scope reading of ✱13·191.  The quantified left member is kept as
its complete object formula so no Lean function stands in for PM syntax. -/
def star_13_191_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (quantifiedIdentity phiX : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ :: y = x .⊃y . φy : ≡ . φx"
  parsed := .assertion
    (star_4_01 negation disjunction quantifiedIdentity phiX)

/-- ✱13·191 remains explicitly asserted pending ✱13·12.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_191
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (quantifiedIdentity phiX : Formula signature real [] order)
    (star_13_191_hypothesis : Derivation
      (star_13_191_reading negation disjunction quantifiedIdentity phiX).parsed) :
    Derivation
      (star_13_191_reading negation disjunction quantifiedIdentity phiX).parsed := by
  have line1 := star_13_191_hypothesis
  exact line1

/-- Audited scope reading of ✱13·192. -/
def star_13_192_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (existentialMember psiB : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ :: (∃c) : x = b .≡x . x = c : ψc : ≡ . ψb"
  parsed := .assertion (star_4_01 negation disjunction existentialMember psiB)

/-- ✱13·192 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_192
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (existentialMember psiB : Formula signature real [] order)
    (star_13_192_hypothesis : Derivation
      (star_13_192_reading negation disjunction existentialMember psiB).parsed) :
    Derivation
      (star_13_192_reading negation disjunction existentialMember psiB).parsed := by
  have line1 := star_13_192_hypothesis
  exact line1

/-- Audited scope reading of ✱13·193. -/
def star_13_193_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (phiX phiY : Formula signature real []
      (bindOrder order (.function [sort] order excess))) :
    ClaimReading signature real where
  printed := "⊢ : φx . x = y .≡ . φy . x = y"
  parsed := .assertion (star_4_01 negation disjunction
    (conjunction negation disjunction phiX (star_13_01 vocabulary x y))
    (conjunction negation disjunction phiY (star_13_01 vocabulary x y)))

/-- ✱13·193 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_193
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (phiX phiY : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (star_13_193_hypothesis : Derivation
      (star_13_193_reading vocabulary negation disjunction x y phiX phiY).parsed) :
    Derivation (star_13_193_reading vocabulary negation disjunction
      x y phiX phiY).parsed := by
  have line1 := star_13_193_hypothesis
  exact line1

/-- Audited scope reading of ✱13·194. -/
def star_13_194_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (phiX phiY : Formula signature real []
      (bindOrder order (.function [sort] order excess))) :
    ClaimReading signature real where
  printed := "⊢ : φx . x = y .≡ . φx . φy . x = y"
  parsed := .assertion (star_4_01 negation disjunction
    (conjunction negation disjunction phiX (star_13_01 vocabulary x y))
    (conjunction negation disjunction phiX
      (conjunction negation disjunction phiY (star_13_01 vocabulary x y))))

/-- ✱13·194 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_194
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort)
    (phiX phiY : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (star_13_194_hypothesis : Derivation
      (star_13_194_reading vocabulary negation disjunction x y phiX phiY).parsed) :
    Derivation (star_13_194_reading vocabulary negation disjunction
      x y phiX phiY).parsed := by
  have line1 := star_13_194_hypothesis
  exact line1

/-- Audited scope reading of ✱13·195. -/
def star_13_195_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (existentialMember phiX : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : (∃y). y = x . φy .≡ . φx"
  parsed := .assertion (star_4_01 negation disjunction existentialMember phiX)

/-- ✱13·195 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_195
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (existentialMember phiX : Formula signature real [] order)
    (star_13_195_hypothesis : Derivation
      (star_13_195_reading negation disjunction existentialMember phiX).parsed) :
    Derivation
      (star_13_195_reading negation disjunction existentialMember phiX).parsed := by
  have line1 := star_13_195_hypothesis
  exact line1

/-- Audited scope reading of ✱13·3. -/
def star_13_3_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (phiA phiX : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (x a : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢::φ a∨∼φ a.⊃:.φ x∨∼φ x.≡:x=a.∨.x≠ a"
  parsed := .assertion (implication negation disjunction
    (sameDisjunction disjunction phiA (.neg negation phiA))
    (star_4_01 negation disjunction
      (sameDisjunction disjunction phiX (.neg negation phiX))
      (sameDisjunction disjunction (star_13_01 vocabulary x a)
        (.neg negation (star_13_01 vocabulary x a)))))

/-- ✱13·3, reconstructed propositionally from excluded middle on each side.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_3
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (phiA phiX : Formula signature real []
      (bindOrder order (.function [sort] order excess)))
    (x a : Term signature real [] sort) :
    Derivation (star_13_3_reading vocabulary negation disjunction
      phiA phiX x a).parsed := by
  let left := sameDisjunction disjunction phiX (.neg negation phiX)
  let equality := star_13_01 vocabulary x a
  let right := sameDisjunction disjunction equality (.neg negation equality)
  have leftProof : ⊢ᵣ left := star_2_11 negation disjunction phiX
  have rightProof : ⊢ᵣ right := star_2_11 negation disjunction equality
  have leftToRight : ⊢ᵣ implication negation disjunction left right :=
    star13_detach negation disjunction right
      (implication negation disjunction left right) rightProof
      (star_2_02 negation disjunction left right)
  have rightToLeft : ⊢ᵣ implication negation disjunction right left :=
    star13_detach negation disjunction left
      (implication negation disjunction right left) leftProof
      (star_2_02 negation disjunction right left)
  have joined := star13_detach negation disjunction _ _ leftToRight
    (star_3_2 negation disjunction
      (implication negation disjunction left right)
      (implication negation disjunction right left))
  have equivalenceProof : ⊢ᵣ star_4_01 negation disjunction left right :=
    star13_detach negation disjunction _ _ rightToLeft joined
  exact star13_detach negation disjunction _ _ equivalenceProof
    (star_2_02 negation disjunction
      (sameDisjunction disjunction phiA (.neg negation phiA))
      (star_4_01 negation disjunction left right))

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_13_1
#print axioms PM.RamifiedSyntax.star_13_101
#print axioms PM.RamifiedSyntax.star_13_15
#print axioms PM.RamifiedSyntax.star_13_11
#print axioms PM.RamifiedSyntax.star_13_12
#print axioms PM.RamifiedSyntax.star_13_16
#print axioms PM.RamifiedSyntax.star_13_17
#print axioms PM.RamifiedSyntax.star_13_171
#print axioms PM.RamifiedSyntax.star_13_18
#print axioms PM.RamifiedSyntax.star_13_181
#print axioms PM.RamifiedSyntax.star_13_19
#print axioms PM.RamifiedSyntax.star_13_191
#print axioms PM.RamifiedSyntax.star_13_192
#print axioms PM.RamifiedSyntax.star_13_193
#print axioms PM.RamifiedSyntax.star_13_194
#print axioms PM.RamifiedSyntax.star_13_195
#print axioms PM.RamifiedSyntax.star_13_3
