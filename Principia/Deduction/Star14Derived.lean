import Principia.Deduction.Star4Ramified
import Principia.FirstEdition.Volume1.Star14Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱14

Descriptions remain contextual; no description-valued `Term` is introduced.
-/

/-- Audited scope reading of ✱14·1.  The left-hand description scope is
the contextual expansion `star_14_01`; its definiens is the same AST on the
right after unfolding ✱14·01. -/
def star_14_1_reading
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    ClaimReading signature real where
  printed := "⊢ : [(ℙx)(φx)] . ψ(ℙx)(φx) .≡ : (∃b) : φx .≡ₓ. x = b : ψb"
  parsed := .assertion
    (star_4_01 negation disjunction scopeExpansion scopeExpansion)

/-- ✱14·1, exactly the printed `✱4·2.(✱14·01)` instance.
`scopeExpansion` is necessarily a formula, never a description-valued term.
`demonstration_provenance: follows-printed`. -/
theorem star_14_1
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    Derivation
      (star_14_1_reading scopeExpansion negation disjunction).parsed := by
  have line1 := star_4_2 negation disjunction scopeExpansion
  exact line1

/-- Audited scope reading of ✱14·101.  Omitting the explicit scope bracket
does not turn the description into a term: the complete contextual expansion
remains the AST on both sides. -/
def star_14_101_reading
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    ClaimReading signature real where
  printed := "⊢ : ψ(ℙx)(φx) .≡ : (∃b) : φx .≡ₓ. x = b : ψb"
  parsed := .assertion
    (star_4_01 negation disjunction scopeExpansion scopeExpansion)

/-- ✱14·101, the printed one-line appeal to ✱14·1.
`demonstration_provenance: follows-printed`. -/
theorem star_14_101
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    Derivation
      (star_14_101_reading scopeExpansion negation disjunction).parsed := by
  have line1 := star_14_1 scopeExpansion negation disjunction
  exact line1

/-- Audited scope reading of ✱14·11. -/
def star_14_11_reading
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (uniquenessMatrix : Formula signature real [sort] matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder sort))
    (disjunction : signature.Disjunction (bindOrder matrixOrder sort)) :
    ClaimReading signature real where
  printed := "⊢ : E!(℩x)(φx) .≡ : (∃b) : φx .≡ₓ. x = b"
  parsed := .assertion
    (star_4_01 negation disjunction
      (star_14_02 existential uniquenessMatrix)
      (star_14_02 existential uniquenessMatrix))

/-- ✱14·11, the printed ✱4·2 instance after unfolding ✱14·02.
`demonstration_provenance: follows-printed`. -/
theorem star_14_11
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (uniquenessMatrix : Formula signature real [sort] matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder sort))
    (disjunction : signature.Disjunction (bindOrder matrixOrder sort)) :
    Derivation
      (star_14_11_reading existential uniquenessMatrix negation disjunction).parsed := by
  have line1 := star_4_2 negation disjunction
    (star_14_02 existential uniquenessMatrix)
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_14_11
#print axioms PM.RamifiedSyntax.star_14_1
#print axioms PM.RamifiedSyntax.star_14_101
