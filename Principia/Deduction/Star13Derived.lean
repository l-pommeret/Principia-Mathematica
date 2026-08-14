import Principia.Deduction.Star4Ramified
import Principia.FirstEdition.Volume1.Star13

namespace PM.RamifiedSyntax

private theorem star13_detach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1 negation disjunction
  | cons head tail => exact Derivation.star_1_11 negation disjunction

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
    (star_13_01 vocabulary x y) (star_13_01 vocabulary x y))

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
  have line1 := star_4_2 negation disjunction (star_13_01 vocabulary x y)
  exact line1

/-- Audited scope reading of ✱13·15. -/
def star_13_15_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ . x = x"
  parsed := .assertion (star_13_01 vocabulary x x)

/-- ✱13·15.  Reflexivity follows by `Id` on the matrix of the Leibniz
definition and ✱9·13 generalization over the predicative function variable.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_13_15
    (vocabulary : IdentityVocabulary signature sort order excess)
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
  have line2 := Derivation.star_9_13 vocabulary.universal body line1
  exact line2

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
#print axioms PM.RamifiedSyntax.star_13_15
#print axioms PM.RamifiedSyntax.star_13_3
