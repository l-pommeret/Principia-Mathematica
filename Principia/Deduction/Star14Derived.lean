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

/-!
The following contextual envelopes are object-language formulae in
`Derivation`, but their proofs remain explicit named assumptions.  This keeps
the catalogue honest while the missing ✱13 substitution chain and the
unexported quantifier steps in the printed demonstrations are reconstructed.
-/

/-- Audited scope reading of ✱14·12. -/
def star_14_12_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists uniqueness : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : E!(℩x)(φx) .⊃ : φx . φy .⊃ₓ,ᵧ. x = y"
  parsed := .assertion
    (implication negation disjunction descriptionExists uniqueness)

/-- ✱14·12 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_12
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists uniqueness : Formula signature real [] order)
    (star_14_12_hypothesis : Derivation
      (star_14_12_reading negation disjunction
        descriptionExists uniqueness).parsed) :
    Derivation (star_14_12_reading negation disjunction
      descriptionExists uniqueness).parsed := by
  have line1 := star_14_12_hypothesis
  exact line1

/-- Audited scope reading of ✱14·13. -/
def star_14_13_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (equalsDescription descriptionEquals : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : a = (℩x)(φx) .≡ . (℩x)(φx) = a"
  parsed := .assertion (star_4_01 negation disjunction
    equalsDescription descriptionEquals)

/-- ✱14·13 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_13
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (equalsDescription descriptionEquals : Formula signature real [] order)
    (star_14_13_hypothesis : Derivation
      (star_14_13_reading negation disjunction
        equalsDescription descriptionEquals).parsed) :
    Derivation (star_14_13_reading negation disjunction
      equalsDescription descriptionEquals).parsed := by
  have line1 := star_14_13_hypothesis
  exact line1

/-- Audited scope reading of ✱14·14. -/
def star_14_14_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (identityAB identityBDescription identityADescription :
      Formula signature real [] order) : ClaimReading signature real where
  printed := "⊢ : a = b . b = (℩x)(φx) .⊃ . a = (℩x)(φx)"
  parsed := .assertion (implication negation disjunction
    (conjunction negation disjunction identityAB identityBDescription)
    identityADescription)

/-- ✱14·14 remains explicitly asserted pending ✱13·13.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_14
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (identityAB identityBDescription identityADescription :
      Formula signature real [] order)
    (star_14_14_hypothesis : Derivation
      (star_14_14_reading negation disjunction identityAB
        identityBDescription identityADescription).parsed) :
    Derivation (star_14_14_reading negation disjunction identityAB
      identityBDescription identityADescription).parsed := by
  have line1 := star_14_14_hypothesis
  exact line1

/-- Audited scope reading of ✱14·15. -/
def star_14_15_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionIdentity psiDescription psiB : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : (℩x)(φx) = b .⊃ : ψ{(℩x)(φx)} .≡ . ψb"
  parsed := .assertion (implication negation disjunction descriptionIdentity
    (star_4_01 negation disjunction psiDescription psiB))

/-- ✱14·15 remains explicitly asserted pending ✱13·192.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_15
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionIdentity psiDescription psiB : Formula signature real [] order)
    (star_14_15_hypothesis : Derivation
      (star_14_15_reading negation disjunction descriptionIdentity
        psiDescription psiB).parsed) :
    Derivation (star_14_15_reading negation disjunction descriptionIdentity
      psiDescription psiB).parsed := by
  have line1 := star_14_15_hypothesis
  exact line1

/-- Audited scope reading of ✱14·16. -/
def star_14_16_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionIdentity chiLeft chiRight : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : (℩x)(φx) = (℩x)(ψx) .⊃ : χ{(℩x)(φx)} .≡ . χ{(℩x)(ψx)}"
  parsed := .assertion (implication negation disjunction descriptionIdentity
    (star_4_01 negation disjunction chiLeft chiRight))

/-- ✱14·16 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_16
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionIdentity chiLeft chiRight : Formula signature real [] order)
    (star_14_16_hypothesis : Derivation
      (star_14_16_reading negation disjunction descriptionIdentity
        chiLeft chiRight).parsed) :
    Derivation (star_14_16_reading negation disjunction descriptionIdentity
      chiLeft chiRight).parsed := by
  have line1 := star_14_16_hypothesis
  exact line1

/-- Audited scope reading of ✱14·17. -/
def star_14_17_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionIdentity formallyEquivalent : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : (℩x)(φx) = b .≡ : ψ!(℩x)(φx) .≡_ψ . ψ!b"
  parsed := .assertion (star_4_01 negation disjunction
    descriptionIdentity formallyEquivalent)

/-- ✱14·17 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_17
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionIdentity formallyEquivalent : Formula signature real [] order)
    (star_14_17_hypothesis : Derivation
      (star_14_17_reading negation disjunction
        descriptionIdentity formallyEquivalent).parsed) :
    Derivation (star_14_17_reading negation disjunction
      descriptionIdentity formallyEquivalent).parsed := by
  have line1 := star_14_17_hypothesis
  exact line1

/-- Audited scope reading of ✱14·18. -/
def star_14_18_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists universalPsi psiDescription :
      Formula signature real [] order) : ClaimReading signature real where
  printed := "⊢ :: E!(℩x)(φx) .⊃ : (x) . ψx .⊃ . ψ(℩x)(φx)"
  parsed := .assertion (implication negation disjunction descriptionExists
    (implication negation disjunction universalPsi psiDescription))

/-- ✱14·18 remains explicitly asserted; in particular no hidden ✱10·35
bridge is introduced. `demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_18
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists universalPsi psiDescription :
      Formula signature real [] order)
    (star_14_18_hypothesis : Derivation
      (star_14_18_reading negation disjunction descriptionExists
        universalPsi psiDescription).parsed) :
    Derivation (star_14_18_reading negation disjunction descriptionExists
      universalPsi psiDescription).parsed := by
  have line1 := star_14_18_hypothesis
  exact line1

/-- Audited scope reading of ✱14·21. -/
def star_14_21_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (psiDescription descriptionExists : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : ψ(℩x)(φx) .⊃ . E!(℩x)(φx)"
  parsed := .assertion
    (implication negation disjunction psiDescription descriptionExists)

/-- ✱14·21 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_21
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (psiDescription descriptionExists : Formula signature real [] order)
    (star_14_21_hypothesis : Derivation
      (star_14_21_reading negation disjunction
        psiDescription descriptionExists).parsed) :
    Derivation (star_14_21_reading negation disjunction
      psiDescription descriptionExists).parsed := by
  have line1 := star_14_21_hypothesis
  exact line1

/-- Audited scope reading of ✱14·22. -/
def star_14_22_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists phiDescription : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "⊢ : E!(℩x)(φx) .≡ . φ(℩x)(φx)"
  parsed := .assertion (star_4_01 negation disjunction
    descriptionExists phiDescription)

/-- ✱14·22 remains explicitly asserted.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_22
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists phiDescription : Formula signature real [] order)
    (star_14_22_hypothesis : Derivation
      (star_14_22_reading negation disjunction
        descriptionExists phiDescription).parsed) :
    Derivation (star_14_22_reading negation disjunction
      descriptionExists phiDescription).parsed := by
  have line1 := star_14_22_hypothesis
  exact line1

/-- Audited scope reading of ✱14·31. -/
def star_14_31_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists scopedDisjunction disjunctionScoped :
      Formula signature real [] order) : ClaimReading signature real where
  printed := "⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ∨ χ(℩x)(φx) .≡ : p ∨ [(℩x)(φx)] . χ(℩x)(φx)"
  parsed := .assertion (implication negation disjunction descriptionExists
    (star_4_01 negation disjunction scopedDisjunction disjunctionScoped))

/-- ✱14·31 remains explicitly asserted; this declaration supplies only the
object target expected by ✱30. `demonstration_provenance: editorial-reconstruction`. -/
theorem star_14_31
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (descriptionExists scopedDisjunction disjunctionScoped :
      Formula signature real [] order)
    (star_14_31_hypothesis : Derivation
      (star_14_31_reading negation disjunction descriptionExists
        scopedDisjunction disjunctionScoped).parsed) :
    Derivation (star_14_31_reading negation disjunction descriptionExists
      scopedDisjunction disjunctionScoped).parsed := by
  have line1 := star_14_31_hypothesis
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_14_11
#print axioms PM.RamifiedSyntax.star_14_1
#print axioms PM.RamifiedSyntax.star_14_101
#print axioms PM.RamifiedSyntax.star_14_12
#print axioms PM.RamifiedSyntax.star_14_13
#print axioms PM.RamifiedSyntax.star_14_14
#print axioms PM.RamifiedSyntax.star_14_15
#print axioms PM.RamifiedSyntax.star_14_16
#print axioms PM.RamifiedSyntax.star_14_17
#print axioms PM.RamifiedSyntax.star_14_18
#print axioms PM.RamifiedSyntax.star_14_21
#print axioms PM.RamifiedSyntax.star_14_22
#print axioms PM.RamifiedSyntax.star_14_31
