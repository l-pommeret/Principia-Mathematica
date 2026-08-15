import Principia.Deduction.Star10Derived
import Principia.FirstEdition.Volume1.Star14Source
import Principia.Syntax.Printed

namespace PM.RamifiedSyntax

/-- Printed-to-AST witness for ramified description propositions. -/
structure Star14Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-!
# Derived propositions of PM I, ✱14

Descriptions remain contextual; no description-valued `Term` is introduced.
-/

private theorem star14_uncastAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) equality) formula)) →
      Derivation (.assertion formula) := by
  cases equality
  exact fun derivation => derivation

/-- Matrix-level product used beneath the description candidate binder.
Unlike `conjunction`, it deliberately retains an arbitrary apparent context. -/
private def star14_matrixConjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation p) (.neg negation q))

/-- The heterogeneous `Syll` instance needed when existential introduction
raises the order of the consequent.  It is the independent-order primitive
✱1·6, followed twice by detachment. -/
private theorem star14_mixedSyllSameLeft
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (rightDisjunction : signature.Disjunction (max order rightOrder))
    (outerNegation : signature.Negation (max order rightOrder))
    (innerDisjunction : signature.Disjunction
      (max (max order order) (max order rightOrder)))
    (outerDisjunction : signature.Disjunction
      (max (max order rightOrder)
        (max (max order order) (max order rightOrder))))
    (p q : Formula signature real [] order)
    (r : Formula signature real [] rightOrder)
    (line1 : ⊢ᵣ implication negation disjunction p q)
    (line2 : ⊢ᵣ mixedImplication negation rightDisjunction q r) :
    ⊢ᵣ mixedImplication negation rightDisjunction p r := by
  let sameOrder := natMaxSelf order
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction sameOrder.symm) disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation sameOrder.symm) negation
  let rawPremise : Formula signature real [] (max order order) :=
    mixedImplication negation pairDisjunction p q
  have normalizedPremise :
      Eq.mp (congrArg (Formula signature real []) sameOrder) rawPremise =
        implication negation disjunction p q := by
    exact mixedImplication_normalizeSameOrder rfl rfl
      negation disjunction p q
  have castPremise : ⊢ᵣ Eq.mp
      (congrArg (Formula signature real []) sameOrder) rawPremise :=
    Derivation.castAssertion normalizedPremise line1
  have rawLine1 : ⊢ᵣ rawPremise :=
    star14_uncastAssertionOrder sameOrder rawPremise castPremise
  have syllogism := Derivation.star_1_6 negation rightDisjunction
    outerNegation pairNegation pairDisjunction rightDisjunction
    innerDisjunction outerDisjunction (.neg negation p) q r
  have line3 := Derivation.star_9_12 outerNegation outerDisjunction
    line2 syllogism
  have line4 := Derivation.star_9_12 pairNegation innerDisjunction
    rawLine1 line3
  exact line4

/-- Same-order syllogistic composition, kept local so contextual description
proofs never appeal to a host-level implication eliminator. -/
private theorem star14_composeSame
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : ⊢ᵣ implication negation disjunction p q)
    (line2 : ⊢ᵣ implication negation disjunction q r) :
    ⊢ᵣ implication negation disjunction p r := by
  have syll := star_2_05 negation disjunction p q r
  have step := Derivation.star_9_12_same negation disjunction line2 syll
  exact Derivation.star_9_12_same negation disjunction line1 step

/-- Pair two consequences beneath their common antecedent (`Fact`). -/
private theorem star14_joinUnder
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : ⊢ᵣ implication negation disjunction p q)
    (line2 : ⊢ᵣ implication negation disjunction p r) :
    ⊢ᵣ implication negation disjunction p
      (conjunction negation disjunction q r) := by
  have paired := star_10_13 negation disjunction
    (implication negation disjunction p q)
    (implication negation disjunction p r) line1 line2
  have fact := star_3_47 negation disjunction p p q r
  have pairedFact := Derivation.star_9_12_same negation disjunction paired fact
  have duplicateEquivalence := star_4_24 negation disjunction p
  have duplicate := Derivation.star_9_12_same negation disjunction
    duplicateEquivalence
    (star_3_26 negation disjunction
      (implication negation disjunction p
        (conjunction negation disjunction p p))
      (implication negation disjunction
        (conjunction negation disjunction p p) p))
  exact star14_composeSame negation disjunction _ _ _ duplicate pairedFact

/-- Put an already derived proposition beneath an arbitrary antecedent. -/
private theorem star14_under
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (line : ⊢ᵣ q) :
    ⊢ᵣ implication negation disjunction p q := by
  have introduction := star_2_02 negation disjunction p q
  exact Derivation.star_9_12_same negation disjunction line introduction

private theorem star14_scopedMixedImplication_instantiate
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (matrix : Formula signature real [argument] matrixOrder)
    (fixed : Formula signature real [] fixedOrder)
    (value : Term signature (argument :: real) [] argument) :
    (mixedImplication negation disjunction matrix
      (fixed.rename (fun v => .succ v))).weakenReal.instantiate value =
      mixedImplication negation disjunction
        (matrix.weakenReal.instantiate value) fixed.weakenReal := by
  unfold mixedImplication Formula.instantiate
  change Formula.disj disjunction
    (.neg negation (matrix.weakenReal.substitute (instantiateSubstitution value)))
    (((fixed.rename (fun v => .succ v)).weakenReal).substitute
      (instantiateSubstitution value)) = _
  rw [Formula.closed_weakenReal_instantiateSubstitution]

private theorem star14_matrixConjunction_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [argument] order)
    (value : Term signature (argument :: real) [] argument) :
    (star14_matrixConjunction negation disjunction left right).weakenReal.instantiate value =
      star14_matrixConjunction negation disjunction
        (left.weakenReal.instantiate value)
        (right.weakenReal.instantiate value) := by
  unfold star14_matrixConjunction Formula.instantiate
  change Formula.neg negation
    (Formula.substitute (instantiateSubstitution value)
      ((sameDisjunction disjunction (.neg negation left)
        (.neg negation right)).weakenReal)) = _
  rw [sameDisjunction_weakenReal, sameDisjunction_substitute]
  rfl

private theorem star14_equivalence_weakenReal
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [] order) :
    (star_4_01 negation disjunction left right).weakenReal
      (fresh := fresh) =
    star_4_01 negation disjunction left.weakenReal right.weakenReal := by
  unfold star_4_01 conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).weakenReal))
      (.neg negation
        ((implication negation disjunction right left).weakenReal))) = _
  rw [implication_weakenReal, implication_weakenReal]

private theorem star14_castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

/-- At the least order admitted by `sort`, binding one variable has the same
assigned order.  This is the pure kernel calculation used for ✱14·18. -/
private theorem star14_bindOrderHeight (sort : RSort) :
    bindOrder (Nat.succ sort.height) sort = Nat.succ sort.height := by
  unfold bindOrder
  exact natMaxSelf _

private def star14_stableUniversal
    (universal : signature.Universal sort (Nat.succ sort.height))
    (body : Formula signature real [sort] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Eq.mp (congrArg (Formula signature real []) (star14_bindOrderHeight sort))
    (.always universal body)

private def star14_stableExistential
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (body : Formula signature real [sort] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Eq.mp (congrArg (Formula signature real []) (star14_bindOrderHeight sort))
    (.sometimes existential body)

/-- The ✱10·1 specialization used on the first printed line of ✱14·18,
normalized only along the computed equality of assigned orders. -/
private theorem star14_stableSpecialize
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (body : Formula signature real [sort] (Nat.succ sort.height))
    (value : Term signature real [] sort) :
    ⊢ᵣ implication negation disjunction
      (star14_stableUniversal universal body) (body.instantiate value) := by
  let bindEq := star14_bindOrderHeight sort
  let resultEq := natMaxCongr bindEq rfl
  let rawNegation :=
    Eq.mp (congrArg signature.Negation bindEq.symm) negation
  let rawDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let rawFormula := mixedImplication rawNegation rawDisjunction
    (.always universal body) (body.instantiate value)
  have rawLine : ⊢ᵣ rawFormula :=
    Derivation.star_10_1 universal rawNegation rawDisjunction body value
  have castLine : ⊢ᵣ Eq.mp
      (congrArg (Formula signature real []) resultEq) rawFormula :=
    star14_castAssertionOrder resultEq rawFormula rawLine
  have normalized :
      Eq.mp (congrArg (Formula signature real []) resultEq) rawFormula =
        implication negation disjunction
          (star14_stableUniversal universal body) (body.instantiate value) := by
    exact mixedImplication_normalizeSameOrder bindEq rfl
      negation disjunction (.always universal body) (body.instantiate value)
  exact Derivation.castAssertion normalized.symm castLine

/-- Existential introduction ✱9·1, normalized at the same least assigned
order. -/
private theorem star14_stableExistentialIntroduction
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (body : Formula signature real [sort] (Nat.succ sort.height))
    (value : Term signature real [] sort) :
    ⊢ᵣ implication negation disjunction
      (body.instantiate value) (star14_stableExistential existential body) := by
  let bindEq := star14_bindOrderHeight sort
  let resultEq := natMaxCongr rfl bindEq
  let rawDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let rawFormula := mixedImplication negation rawDisjunction
    (body.instantiate value) (.sometimes existential body)
  have rawLine : ⊢ᵣ rawFormula :=
    Derivation.star_9_1 existential negation rawDisjunction body value
  have castLine : ⊢ᵣ Eq.mp
      (congrArg (Formula signature real []) resultEq) rawFormula :=
    star14_castAssertionOrder resultEq rawFormula rawLine
  have normalized :
      Eq.mp (congrArg (Formula signature real []) resultEq) rawFormula =
        implication negation disjunction
          (body.instantiate value)
          (star14_stableExistential existential body) := by
    exact mixedImplication_normalizeSameOrder rfl bindEq
      negation disjunction (body.instantiate value) (.sometimes existential body)
  exact Derivation.castAssertion normalized.symm castLine

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

/-- Printed left member of ✱14·11, built through the existence sign defined
at ✱14·02. -/
def star_14_11_left
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (uniquenessMatrix : Formula signature real [sort] matrixOrder) :=
  star_14_02 existential uniquenessMatrix

/-- Printed right member of ✱14·11, built independently as the existential
closure of the displayed uniqueness matrix. -/
def star_14_11_right
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (uniquenessMatrix : Formula signature real [sort] matrixOrder) :
    Formula signature real [] (bindOrder matrixOrder sort) :=
  .sometimes existential uniquenessMatrix

theorem star_14_11_left_unfold
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (uniquenessMatrix : Formula signature real [sort] matrixOrder) :
    star_14_11_left existential uniquenessMatrix =
      star_14_11_right existential uniquenessMatrix := rfl

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
      (star_14_11_left existential uniquenessMatrix)
      (star_14_11_right existential uniquenessMatrix))

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
    (star_14_11_right existential uniquenessMatrix)
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_14_11_left existential uniquenessMatrix)
    (star_14_11_right existential uniquenessMatrix)))
  rw [star_14_11_left_unfold]
  exact line1

/-!
The contextual envelopes ✱14·12--·17 below are object-language formulae in
`Derivation`, but their proofs remain explicit named assumptions.  This keeps
the catalogue honest while the missing ✱13 substitution chain in their
printed demonstrations is reconstructed.
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

/-- Primitive real-scope normal form of ✱14·18 at the least order admitted
by the described sort.  The outer universal is the ✱10·23 presentation of
the existential antecedent after `Fact` and ✱10·35; both apparent occurrences
of the candidate remain bound. -/
def star_14_18_formula
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix psi :
      Formula signature real [sort] (Nat.succ sort.height)) :
    Formula signature real []
      (bindOrder (Nat.succ sort.height) sort) :=
  .always universal
    (implication negation disjunction
      (star14_matrixConjunction negation disjunction uniquenessMatrix
        ((star14_stableUniversal universal psi).rename (fun v => .succ v)))
      ((star14_stableExistential existential
        (star14_matrixConjunction negation disjunction uniquenessMatrix psi)).rename
          (fun v => .succ v)))

/-- Audited scope reading of ✱14·18. -/
def star_14_18_reading
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix psi :
      Formula signature real [sort] (Nat.succ sort.height)) :
    Star14Reading signature real where
  printed := PM.pmPrinted
    "⊢ :: E!(℩x)(φx) .⊃ : (x) . ψx .⊃ . ψ(℩x)(φx)"
  parsed := .assertion
    (star_14_18_formula existential universal negation disjunction
      uniquenessMatrix psi)
  scopeReading := "After ✱14·1 and ✱14·11, `Fact`, ✱10·11·28, and ✱10·35 put the independent universal premise and the uniqueness matrix beneath the bound description candidate."

/-- ✱14·18, unconditionally at the least admissible assigned order.
The proof follows the five printed lines: ✱10·1 specializes the universal
premise; `Fact` retains the uniqueness matrix; existential introduction plus
generalization realizes ✱10·11·28; and the last real-scope form is exactly
the ✱10·35/✱14·1/✱14·11 expansion.
`demonstration_provenance: follows-printed`. -/
private theorem star14_18_core
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix psi :
      Formula signature real [sort] (Nat.succ sort.height)) :
    Derivation (.assertion
      (star_14_18_formula existential universal negation disjunction
        uniquenessMatrix psi)) := by
  let witness : Term signature (sort :: real) [] sort :=
    .real (.zero : Var (sort :: real) sort)
  let uniquenessAtWitness := uniquenessMatrix.weakenReal.instantiate witness
  let psiAtWitness := psi.weakenReal.instantiate witness
  let universalPsi := star14_stableUniversal universal psi
  let describedPsi := star14_stableExistential existential
    (star14_matrixConjunction negation disjunction uniquenessMatrix psi)
  have specialization := star14_stableSpecialize universal negation disjunction
    (psi.weakenReal (fresh := sort)) witness
  have universalEq :
      star14_stableUniversal universal (psi.weakenReal (fresh := sort)) =
        universalPsi.weakenReal (fresh := sort) := by
    unfold star14_stableUniversal universalPsi
    exact (Formula.weakenReal_cast (star14_bindOrderHeight sort)
      (.always universal psi)).symm
  have line1 : ⊢ᵣ implication negation disjunction
      (universalPsi.weakenReal (fresh := sort)) psiAtWitness :=
    Derivation.castAssertion
      (congrArg (fun antecedent => implication negation disjunction
        antecedent psiAtWitness) universalEq.symm) specialization
  have identity := star_2_08 negation disjunction uniquenessAtWitness
  have paired := star_10_13 negation disjunction
    (implication negation disjunction uniquenessAtWitness uniquenessAtWitness)
    (implication negation disjunction
      (universalPsi.weakenReal (fresh := sort)) psiAtWitness)
    identity line1
  have fact := star_3_47 negation disjunction
    uniquenessAtWitness (universalPsi.weakenReal (fresh := sort))
    uniquenessAtWitness psiAtWitness
  have line2 := Derivation.star_9_12_same negation disjunction paired fact
  have introduction := star14_stableExistentialIntroduction existential
    negation disjunction
    ((star14_matrixConjunction negation disjunction uniquenessMatrix psi).weakenReal
      (fresh := sort)) witness
  have sourceEq := star14_matrixConjunction_instantiate negation disjunction
    uniquenessMatrix psi witness
  have describedEq :
      star14_stableExistential existential
        ((star14_matrixConjunction negation disjunction uniquenessMatrix psi).weakenReal
          (fresh := sort)) =
      describedPsi.weakenReal (fresh := sort) := by
    unfold star14_stableExistential describedPsi
    exact (Formula.weakenReal_cast (star14_bindOrderHeight sort)
      (.sometimes existential
        (star14_matrixConjunction negation disjunction uniquenessMatrix psi))).symm
  have line3 : ⊢ᵣ implication negation disjunction
      (star14_matrixConjunction negation disjunction
        uniquenessAtWitness psiAtWitness)
      (describedPsi.weakenReal (fresh := sort)) :=
    let sourceCast := congrArg
      (fun antecedent => implication negation disjunction antecedent
        (describedPsi.weakenReal (fresh := sort))) sourceEq.symm
    let consequentCast := congrArg
      (implication negation disjunction
        (((star14_matrixConjunction negation disjunction
          uniquenessMatrix psi).weakenReal (fresh := sort)).instantiate witness))
      describedEq.symm
    Derivation.castAssertion (Eq.trans sourceCast consequentCast) introduction
  have syll := star_2_05 negation disjunction
    (star14_matrixConjunction negation disjunction uniquenessAtWitness
      (universalPsi.weakenReal (fresh := sort)))
    (star14_matrixConjunction negation disjunction
      uniquenessAtWitness psiAtWitness)
    (describedPsi.weakenReal (fresh := sort))
  have step := Derivation.star_9_12_same negation disjunction line3 syll
  have existentialLift := Derivation.star_9_12_same negation disjunction line2 step
  have matrixEq :
      (implication negation disjunction
        (star14_matrixConjunction negation disjunction uniquenessMatrix
          (universalPsi.rename (fun v => .succ v)))
        (describedPsi.rename (fun v => .succ v))).weakenReal.instantiate witness =
      implication negation disjunction
        (star14_matrixConjunction negation disjunction uniquenessAtWitness
          (universalPsi.weakenReal (fresh := sort)))
        (describedPsi.weakenReal (fresh := sort)) := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    change implication negation disjunction
      ((star14_matrixConjunction negation disjunction uniquenessMatrix
        (universalPsi.rename (fun v => .succ v))).weakenReal.instantiate witness)
      (((describedPsi.rename (fun v => .succ v)).weakenReal).instantiate witness) = _
    rw [star14_matrixConjunction_instantiate,
      Formula.closed_weakenReal_instantiate,
      Formula.closed_weakenReal_instantiate]
  have line4 := Derivation.star_9_13 universal
    (implication negation disjunction
      (star14_matrixConjunction negation disjunction uniquenessMatrix
        (universalPsi.rename (fun v => .succ v)))
      (describedPsi.rename (fun v => .succ v)))
    (Derivation.castAssertion matrixEq existentialLift)
  exact line4

/-- ✱14·18, unconditionally at the least admissible assigned order.
`demonstration_provenance: follows-printed`. -/
theorem star_14_18
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix psi :
      Formula signature real [sort] (Nat.succ sort.height)) :
    Derivation (.assertion
      (star_14_18_formula existential universal negation disjunction
        uniquenessMatrix psi)) := by
  have line1 := star14_18_core existential universal negation disjunction
    uniquenessMatrix psi
  exact line1

/-- The primitive AST of ✱14·21 after ✱14·1 expands the contextual
description.  This is the independently constructed right member of
✱10·23, not a definitional rewriting of its universally quantified left
member.  `uniquenessMatrix` is the displayed `φx ≡ₓ x=b`; the description
remains an existentially bound candidate, never a `Term`. -/
def star_14_21_formula
    (existential : ExistentialVocabulary signature sort order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (implicationDisjunction : signature.Disjunction
      (max (bindOrder order sort) (bindOrder order sort)))
    (uniquenessMatrix psi : Formula signature real [sort] order) :
    Formula signature real []
      (bindOrder (max order (bindOrder order sort)) sort) :=
  star_10_23_externalRight existential implicationDisjunction
    (star14_matrixConjunction negation disjunction uniquenessMatrix psi)
    (star_14_02 existential uniquenessMatrix)

/-- Audited scope reading of ✱14·21. -/
def star_14_21_reading
    (existential : ExistentialVocabulary signature sort order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (implicationDisjunction : signature.Disjunction
      (max (bindOrder order sort) (bindOrder order sort)))
    (uniquenessMatrix psi : Formula signature real [sort] order) :
    Star14Reading signature real where
  printed := PM.pmPrinted "⊢ : ψ(℩x)(φx) .⊃ . E!(℩x)(φx)"
  parsed := .assertion
    (star_14_21_formula existential negation disjunction
      implicationDisjunction uniquenessMatrix psi)
  scopeReading := "The description is eliminated contextually by ✱14·1. The parsed AST is the independently built existential-antecedent member of ✱10·23; no definitional scope transport from its universal member is asserted."

/-- The exact rule that the former proof of ✱14·21 was missing.  It maps a
derivation of the universally scoped implication to the independently built
existential-antecedent implication.  This structure merely names the debt; no
inhabitant and no numbered PM proposition is asserted here. -/
structure UniversalImplicationToExistentialAntecedentTransport
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (universal : signature.Universal argument
      (max matrixOrder fixedOrder))
    (matrixDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (implicationDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (matrix : Formula signature real [argument] matrixOrder)
    (fixed : Formula signature real [] fixedOrder) : Prop where
  derive :
    (⊢ᵣ star_10_23_left universal existential.matrixNegation
      matrixDisjunction matrix fixed) →
    (⊢ᵣ star_10_23_externalRight existential implicationDisjunction matrix fixed)

/- There is deliberately no theorem `star_14_21`: its former final step used
`star_10_23_scope_derivation`, which confused the two distinct ASTs above.
The audited reading is retained, and the exact missing rule is recorded by
`UniversalImplicationToExistentialAntecedentTransport`. -/

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

/-- Russell's contextual application of the description to `psi`, at the
least assigned order admitted by the described sort. -/
private def star14_descriptionScope
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix psi :
      Formula signature real [sort] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  star14_stableExistential existential
    (star14_matrixConjunction negation disjunction uniquenessMatrix psi)

/-- The exact object-calculus substitution contract still missing from the
ramified reconstruction of ✱14·242. -/
structure Star14_242Hypothesis
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix :
      Formula signature real [sort] (Nat.succ sort.height)) where
  derive :
    ∀ psi : Formula signature real [sort] (Nat.succ sort.height),
      let witness : Term signature (sort :: real) [] sort :=
        .real (.zero : Var (sort :: real) sort)
      Derivation (.assertion
        (implication negation disjunction
          (uniquenessMatrix.weakenReal.instantiate witness)
          (star_4_01 negation disjunction
            ((star14_descriptionScope existential negation disjunction
              uniquenessMatrix psi).weakenReal)
            (psi.weakenReal.instantiate witness))))

/-- Primitive real-scope normal form of ✱14·31.  Both occurrences of the
description are complete existential scopes; no description-valued term is
formed. -/
def star_14_31_formula
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix chi :
      Formula signature real [sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  let leftMatrix := sameDisjunction disjunction
    (p.rename (fun v => .succ v)) chi
  let leftScope := star14_descriptionScope existential negation disjunction
    uniquenessMatrix leftMatrix
  let rightScope := star14_descriptionScope existential negation disjunction
    uniquenessMatrix chi
  star14_stableUniversal universal
    (implication negation disjunction uniquenessMatrix
      ((star_4_01 negation disjunction leftScope
        (sameDisjunction disjunction p rightScope)).rename (fun v => .succ v)))

/-- Audited scope reading of ✱14·31. -/
def star_14_31_reading
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (uniquenessMatrix chi :
      Formula signature real [sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Star14Reading signature real where
  printed := PM.pmPrinted
    "⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ∨ χ(℩x)(φx) .≡ : p ∨ [(℩x)(φx)] . χ(℩x)(φx)"
  parsed := .assertion
    (star_14_31_formula existential universal negation disjunction
      uniquenessMatrix chi p)
  scopeReading := "After ✱14·242 eliminates each contextual description at a displayed candidate, ✱4·37 lifts the second equivalence through disjunction and ✱10·23 closes the candidate beneath the existence antecedent."

/-- ✱14·31 reduced to the exact missing ramified ✱14·242 substitution
contract.  The remaining proof follows PM's four printed lines in order.
`demonstration_provenance: follows-printed`. -/
theorem star14_31_core
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (existenceNegation : signature.Negation
      (bindOrder (Nat.succ sort.height) sort))
    (existenceDisjunction : signature.Disjunction
      (bindOrder (Nat.succ sort.height) sort))
    (uniquenessMatrix chi :
      Formula signature real [sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (star_14_242_hypothesis : Star14_242Hypothesis existential negation
      disjunction uniquenessMatrix) :
    Derivation (.assertion
      (star_14_31_formula existential universal negation disjunction
        uniquenessMatrix chi p)) := by
  let witness : Term signature (sort :: real) [] sort :=
    .real (.zero : Var (sort :: real) sort)
  let uniquenessAtWitness := uniquenessMatrix.weakenReal.instantiate witness
  let chiAtWitness := chi.weakenReal.instantiate witness
  let pAtWitness := p.weakenReal (fresh := sort)
  let leftMatrix := sameDisjunction disjunction
    (p.rename (fun v => .succ v)) chi
  let leftScope := star14_descriptionScope existential negation disjunction
    uniquenessMatrix leftMatrix
  let rightScope := star14_descriptionScope existential negation disjunction
    uniquenessMatrix chi
  let targetAtWitness := sameDisjunction disjunction pAtWitness chiAtWitness
  let rightAtWitness := sameDisjunction disjunction
    pAtWitness rightScope.weakenReal
  have leftAtWitness :
      leftMatrix.weakenReal.instantiate witness = targetAtWitness := by
    unfold leftMatrix targetAtWitness pAtWitness chiAtWitness
    rw [sameDisjunction_weakenReal, Formula.instantiate,
      sameDisjunction_substitute]
    rw [Formula.closed_weakenReal_instantiateSubstitution]
    rfl
  have rawLine1 := star_14_242_hypothesis.derive leftMatrix
  have line1 : ⊢ᵣ implication negation disjunction uniquenessAtWitness
      (star_4_01 negation disjunction leftScope.weakenReal targetAtWitness) :=
    Derivation.castAssertion
      (congrArg (fun candidate => implication negation disjunction
        uniquenessAtWitness
        (star_4_01 negation disjunction leftScope.weakenReal candidate))
        leftAtWitness.symm) rawLine1
  have substitution := star_14_242_hypothesis.derive chi
  have lifted := star_4_37 negation disjunction rightScope.weakenReal
    chiAtWitness pAtWitness
  have middle := star14_composeSame negation disjunction
    uniquenessAtWitness
    (star_4_01 negation disjunction rightScope.weakenReal chiAtWitness)
    (star_4_01 negation disjunction
      (sameDisjunction disjunction rightScope.weakenReal pAtWitness)
      (sameDisjunction disjunction chiAtWitness pAtWitness))
    substitution lifted
  have leftCommutation := star_4_31 negation disjunction
    pAtWitness rightScope.weakenReal
  have rightCommutation := star_4_31 negation disjunction
    chiAtWitness pAtWitness
  have leftCommutationUnder := star14_under negation disjunction
    uniquenessAtWitness
    (star_4_01 negation disjunction rightAtWitness
      (sameDisjunction disjunction rightScope.weakenReal pAtWitness))
    leftCommutation
  have rightCommutationUnder := star14_under negation disjunction
    uniquenessAtWitness
    (star_4_01 negation disjunction
      (sameDisjunction disjunction chiAtWitness pAtWitness) targetAtWitness)
    rightCommutation
  have firstPair := star14_joinUnder negation disjunction uniquenessAtWitness
    (star_4_01 negation disjunction rightAtWitness
      (sameDisjunction disjunction rightScope.weakenReal pAtWitness))
    (star_4_01 negation disjunction
      (sameDisjunction disjunction rightScope.weakenReal pAtWitness)
      (sameDisjunction disjunction chiAtWitness pAtWitness))
    leftCommutationUnder middle
  have firstChain := star14_composeSame negation disjunction uniquenessAtWitness
    (conjunction negation disjunction
      (star_4_01 negation disjunction rightAtWitness
        (sameDisjunction disjunction rightScope.weakenReal pAtWitness))
      (star_4_01 negation disjunction
        (sameDisjunction disjunction rightScope.weakenReal pAtWitness)
        (sameDisjunction disjunction chiAtWitness pAtWitness)))
    (star_4_01 negation disjunction rightAtWitness
      (sameDisjunction disjunction chiAtWitness pAtWitness))
    firstPair
    (star_4_22 negation disjunction rightAtWitness
      (sameDisjunction disjunction rightScope.weakenReal pAtWitness)
      (sameDisjunction disjunction chiAtWitness pAtWitness))
  have secondPair := star14_joinUnder negation disjunction uniquenessAtWitness
    (star_4_01 negation disjunction rightAtWitness
      (sameDisjunction disjunction chiAtWitness pAtWitness))
    (star_4_01 negation disjunction
      (sameDisjunction disjunction chiAtWitness pAtWitness) targetAtWitness)
    firstChain rightCommutationUnder
  have line2 := star14_composeSame negation disjunction uniquenessAtWitness
    (conjunction negation disjunction
      (star_4_01 negation disjunction rightAtWitness
        (sameDisjunction disjunction chiAtWitness pAtWitness))
      (star_4_01 negation disjunction
        (sameDisjunction disjunction chiAtWitness pAtWitness) targetAtWitness))
    (star_4_01 negation disjunction rightAtWitness targetAtWitness)
    secondPair
    (star_4_22 negation disjunction rightAtWitness
      (sameDisjunction disjunction chiAtWitness pAtWitness) targetAtWitness)
  have symmetryEquivalence := star_4_21 negation disjunction
    rightAtWitness targetAtWitness
  have symmetry := Derivation.star_9_12_same negation disjunction
    symmetryEquivalence
    (star_3_26 negation disjunction
      (implication negation disjunction
        (star_4_01 negation disjunction rightAtWitness targetAtWitness)
        (star_4_01 negation disjunction targetAtWitness rightAtWitness))
      (implication negation disjunction
        (star_4_01 negation disjunction targetAtWitness rightAtWitness)
        (star_4_01 negation disjunction rightAtWitness targetAtWitness)))
  have reversedLine2 := star14_composeSame negation disjunction
    uniquenessAtWitness
    (star_4_01 negation disjunction rightAtWitness targetAtWitness)
    (star_4_01 negation disjunction targetAtWitness rightAtWitness)
    line2 symmetry
  have line3Pair := star14_joinUnder negation disjunction uniquenessAtWitness
    (star_4_01 negation disjunction leftScope.weakenReal targetAtWitness)
    (star_4_01 negation disjunction targetAtWitness rightAtWitness)
    line1 reversedLine2
  have line3 := star14_composeSame negation disjunction uniquenessAtWitness
    (conjunction negation disjunction
      (star_4_01 negation disjunction leftScope.weakenReal targetAtWitness)
      (star_4_01 negation disjunction targetAtWitness rightAtWitness))
    (star_4_01 negation disjunction leftScope.weakenReal rightAtWitness)
    line3Pair
    (star_4_22 negation disjunction leftScope.weakenReal
      targetAtWitness rightAtWitness)
  let target := star_4_01 negation disjunction leftScope
    (sameDisjunction disjunction p rightScope)
  have matrixAtWitness :
      (implication negation disjunction uniquenessMatrix
        (target.rename (fun v => .succ v))).weakenReal.instantiate witness =
      implication negation disjunction uniquenessAtWitness
        (star_4_01 negation disjunction leftScope.weakenReal rightAtWitness) := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    change implication negation disjunction
      uniquenessAtWitness
      (((target.rename (fun v => .succ v)).weakenReal).instantiate witness) = _
    rw [Formula.closed_weakenReal_instantiate]
    unfold target rightAtWitness
    rw [star14_equivalence_weakenReal, sameDisjunction_weakenReal]
  have generalized := Derivation.star_9_13 universal
    (implication negation disjunction uniquenessMatrix
      (target.rename (fun v => .succ v)))
    (Derivation.castAssertion matrixAtWitness line3)
  have line4 := star14_castAssertionOrder (star14_bindOrderHeight sort)
    (.always universal
      (implication negation disjunction uniquenessMatrix
        (target.rename (fun v => .succ v)))) generalized
  have line5 := star_14_11 existential uniquenessMatrix
    existenceNegation existenceDisjunction
  exact line4

/-- ✱14·31, with only the still-missing ✱14·242 substitution step exposed
as a named hypothesis. `demonstration_provenance: follows-printed`. -/
theorem star_14_31
    (existential : ExistentialVocabulary signature sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (existenceNegation : signature.Negation
      (bindOrder (Nat.succ sort.height) sort))
    (existenceDisjunction : signature.Disjunction
      (bindOrder (Nat.succ sort.height) sort))
    (uniquenessMatrix chi :
      Formula signature real [sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (star_14_242_hypothesis : Star14_242Hypothesis existential negation
      disjunction uniquenessMatrix) :
    Derivation (.assertion
      (star_14_31_formula existential universal negation disjunction
        uniquenessMatrix chi p)) := by
  have line1 := star14_31_core existential universal negation disjunction
    existenceNegation existenceDisjunction uniquenessMatrix
    chi p star_14_242_hypothesis
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
#print axioms PM.RamifiedSyntax.star_14_22
#print axioms PM.RamifiedSyntax.star_14_31
