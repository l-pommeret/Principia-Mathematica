import Principia.Deduction.Star13Derived
import Principia.Deduction.Star11Derived
import Principia.FirstEdition.Volume1.Star14Source
import Principia.Syntax.Printed

namespace PM.RamifiedSyntax

/-- Printed-to-AST witness for ramified description propositions. -/
structure Star14Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-- Auxiliary logical meanings used by the unconditional ✱13 substitution
theorems.  These are syntax data, not proposition-valued assumptions. -/
structure Star14ReducibilityVocabulary (signature : Signature) (sort : RSort)
    (order : Nat) where
  reducibilityExistential : ExistentialVocabulary signature
    (.function [sort] order 0) (bindOrder order sort)
  argumentUniversal : signature.Universal sort order
  reducibilityNegation : signature.Negation (bindOrder order sort)
  reducibilityIdentityNegation : signature.Negation
    (max (bindOrder order sort)
      (bindOrder order (.function [sort] order 0)))
  reducibilityBaseNegation : signature.Negation
    (max (bindOrder order sort) order)
  substitutionResultNegation : signature.Negation
    (max (bindOrder order sort)
      (max (bindOrder order (.function [sort] order 0)) order))
  reducibilityDisjunction : signature.Disjunction (bindOrder order sort)
  reducibilityIdentityDisjunction : signature.Disjunction
    (max (bindOrder order sort)
      (bindOrder order (.function [sort] order 0)))
  reducibilityBaseDisjunction : signature.Disjunction
    (max (bindOrder order sort) order)
  substitutionResultDisjunction : signature.Disjunction
    (max (bindOrder order sort)
      (max (bindOrder order (.function [sort] order 0)) order))
  reducibilityScopeUniversal : signature.Universal
    (.function [sort] order 0)
    (max (bindOrder order sort)
      (max (bindOrder order (.function [sort] order 0)) order))
  reducibilityScopeNegation : signature.Negation
    (bindOrder
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order))
      (.function [sort] order 0))
  reducibilityScopeDisjunction : signature.Disjunction
    (bindOrder
      (max (bindOrder order sort)
        (max (bindOrder order (.function [sort] order 0)) order))
      (.function [sort] order 0))
  existentialTargetDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder order sort) (.function [sort] order 0))
      (max (bindOrder order (.function [sort] order 0)) order))
  equivalenceScopeUniversal : signature.Universal
    (.function [sort] order 0)
    (max (bindOrder order (.function [sort] order 0)) order)
  symmetryScopeUniversal : signature.Universal
    (.function [sort] order 0)
    (bindOrder order (.function [sort] order 0))
  scopedNegation : signature.Negation
    (bindOrder (max (bindOrder order (.function [sort] order 0)) order)
      (.function [sort] order 0))
  scopedConsequenceDisjunction : signature.Disjunction
    (max
      (bindOrder (max (bindOrder order (.function [sort] order 0)) order)
        (.function [sort] order 0))
      (bindOrder order (.function [sort] order 0)))
  scopedOuterDisjunction : signature.Disjunction
    (max (bindOrder order (.function [sort] order 0))
      (max
        (bindOrder (max (bindOrder order (.function [sort] order 0)) order)
          (.function [sort] order 0))
        (bindOrder order (.function [sort] order 0))))

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

/-- `Sum` with an independently certified presentation of its premiss.
This is the primitive ✱1·6 instance used when the premiss is an
implication whose negation or disjunction has been moved through a scope. -/
private theorem star14_sumCertifiedRule
    (vocabularyNegation : signature.Negation resultOrder)
    (vocabularyDisjunction : signature.Disjunction resultOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (qNegated : Formula signature real [] qOrder)
    (qrFormula : Formula signature real [] resultOrder)
    (pqFormula : Formula signature real [] pqFormulaOrder)
    (prFormula : Formula signature real [] prFormulaOrder)
    (consequenceFormula : Formula signature real [] resultOrder)
    (consequenceNegated : Formula signature real [] pqFormulaOrder)
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (canonicalOuterNegation : signature.Negation (max qOrder rOrder))
    (canonicalConsequenceNegation : signature.Negation
      (max pOrder qOrder))
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (canonicalConsequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (canonicalOuterDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (consequenceNegation : signature.Negation pqFormulaOrder)
    (qNegationDefinition :
      ImplicationNegation signature real qNegation q qNegated)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real p q pqFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real p r prFormula)
    (consequenceNegationDefinition : ImplicationNegation signature real
      consequenceNegation pqFormula consequenceNegated)
    (consequenceDisjunctionDefinition : ImplicationDisjunction signature real
      consequenceNegated prFormula consequenceFormula) :
    Derivation (.assertion
      (implication vocabularyNegation vocabularyDisjunction
        qrFormula consequenceFormula)) := by
  let formula := implication vocabularyNegation vocabularyDisjunction
    qrFormula consequenceFormula
  let reading : Star1_6Reading qNegation qrDisjunction
      canonicalOuterNegation canonicalConsequenceNegation pqDisjunction
      prDisjunction canonicalConsequenceDisjunction
      canonicalOuterDisjunction p q r formula := {
    qrFormulaOrder := resultOrder
    pqFormulaOrder := pqFormulaOrder
    prFormulaOrder := prFormulaOrder
    consequenceFormulaOrder := resultOrder
    qNegated := qNegated
    qrFormula := qrFormula
    pqFormula := pqFormula
    prFormula := prFormula
    consequenceNegated := consequenceNegated
    consequenceFormula := consequenceFormula
    qrNegated := .neg vocabularyNegation qrFormula
    consequenceNegation := consequenceNegation
    outerNegation := vocabularyNegation
    qNegationDefinition := qNegationDefinition
    qrDisjunctionDefinition := qrDisjunctionDefinition
    pqDisjunctionDefinition := pqDisjunctionDefinition
    prDisjunctionDefinition := prDisjunctionDefinition
    consequenceNegationDefinition := consequenceNegationDefinition
    consequenceDisjunctionDefinition := consequenceDisjunctionDefinition
    outerNegationDefinition := .star_1_01 vocabularyNegation qrFormula
    outerDisjunctionDefinition :=
      .star_1_01_same vocabularyDisjunction
        (.neg vocabularyNegation qrFormula) consequenceFormula
  }
  have line1 := Derivation.star_1_6 qNegation qrDisjunction
    canonicalOuterNegation canonicalConsequenceNegation pqDisjunction
    prDisjunction canonicalConsequenceDisjunction
    canonicalOuterDisjunction p q r (reading := reading)
  exact line1

/-- `Syll` with all three displayed implications certified independently. -/
private theorem star14_syllCertifiedRule
    (vocabularyNegation : signature.Negation resultOrder)
    (vocabularyDisjunction : signature.Disjunction resultOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (pNegated : Formula signature real [] pOrder)
    (qNegated : Formula signature real [] qOrder)
    (pqFormula qrFormula prFormula : Formula signature real [] resultOrder)
    (pNegation : signature.Negation pOrder)
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (canonicalOuterNegation : signature.Negation (max qOrder rOrder))
    (canonicalConsequenceNegation : signature.Negation
      (max pOrder qOrder))
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (canonicalConsequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (canonicalOuterDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (pNegationDefinition :
      ImplicationNegation signature real pNegation p pNegated)
    (qNegationDefinition :
      ImplicationNegation signature real qNegation q qNegated)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula) :
    Derivation (.assertion
      (implication vocabularyNegation vocabularyDisjunction qrFormula
        (implication vocabularyNegation vocabularyDisjunction
          pqFormula prFormula))) := by
  let consequenceFormula := implication vocabularyNegation
    vocabularyDisjunction pqFormula prFormula
  let formula := implication vocabularyNegation vocabularyDisjunction
    qrFormula consequenceFormula
  let reading : Star2_05Reading vocabularyNegation vocabularyDisjunction
      p q r formula := {
    pNegated := pNegated
    pNegation := pNegation
    pNegationDefinition := pNegationDefinition
    primitiveQNegation := qNegation
    primitiveQRDisjunction := qrDisjunction
    primitiveOuterNegation := canonicalOuterNegation
    primitiveConsequenceNegation := canonicalConsequenceNegation
    primitivePQDisjunction := pqDisjunction
    primitivePRDisjunction := prDisjunction
    primitiveConsequenceDisjunction := canonicalConsequenceDisjunction
    primitiveOuterDisjunction := canonicalOuterDisjunction
    sumReading := {
      qrFormulaOrder := resultOrder
      pqFormulaOrder := resultOrder
      prFormulaOrder := resultOrder
      consequenceFormulaOrder := resultOrder
      qNegated := qNegated
      qrFormula := qrFormula
      pqFormula := pqFormula
      prFormula := prFormula
      consequenceNegated := .neg vocabularyNegation pqFormula
      consequenceFormula := consequenceFormula
      qrNegated := .neg vocabularyNegation qrFormula
      consequenceNegation := vocabularyNegation
      outerNegation := vocabularyNegation
      qNegationDefinition := qNegationDefinition
      qrDisjunctionDefinition := qrDisjunctionDefinition
      pqDisjunctionDefinition := pqDisjunctionDefinition
      prDisjunctionDefinition := prDisjunctionDefinition
      consequenceNegationDefinition :=
        .star_1_01 vocabularyNegation pqFormula
      consequenceDisjunctionDefinition :=
        .star_1_01_same vocabularyDisjunction
          (.neg vocabularyNegation pqFormula) prFormula
      outerNegationDefinition := .star_1_01 vocabularyNegation qrFormula
      outerDisjunctionDefinition :=
        .star_1_01_same vocabularyDisjunction
          (.neg vocabularyNegation qrFormula) consequenceFormula
    }
  }
  exact star_2_05 vocabularyNegation vocabularyDisjunction p q r
    (reading := reading)

/-- Transitivity of equivalence with three independently assigned orders. -/
private theorem star14_mixedEquivalenceTransitive
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (line1 : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ))))
    (line2 : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR)))) :
    Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryR))) := by
  let left := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ)
  let right := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR)
  let pair := MixedOrder.ternaryInterpret negation disjunction p q r
    ((MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ) ∧ₚ
      (MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR))
  let target := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryR)
  have line3 := MixedOrder.ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star3.star_3_2
      (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ)
      (MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR))
  have line4 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pqr)
    negation.pq disjunction.pqr left
    (MixedOrder.ternaryInterpret negation disjunction p q r
      ((MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR) ⊃ₚ
        ((MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ) ∧ₚ
          (MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR)))) line1 line3
  have line5 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .pqr)
    negation.qr disjunction.pqr right pair line2 line4
  have line6 := MixedOrder.ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star4.star_4_22
      MixedOrder.ternaryP MixedOrder.ternaryQ MixedOrder.ternaryR)
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pqr .pr)
    negation.pqr disjunction.pqr pair target line5 line6

/-- Syllogistic composition with three independently assigned orders. -/
private theorem star14_mixedImplicationTransitive
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (line1 : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))))
    (line2 : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR)))) :
    Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR))) := by
  let left := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)
  let right := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR)
  let target := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)
  have line3 := MixedOrder.ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star2.star_2_05
      MixedOrder.ternaryP MixedOrder.ternaryQ MixedOrder.ternaryR)
  have line4 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .pqr)
    negation.qr disjunction.pqr right
    (MixedOrder.ternaryInterpret negation disjunction p q r
      ((MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ) ⊃ₚ
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR))) line2 line3
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pr)
    negation.pq disjunction.pqr left target line1 line4

private theorem star14_equivalenceTransitiveSame
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : Derivation (.assertion
      (star_4_01 negation disjunction p q)))
    (line2 : Derivation (.assertion
      (star_4_01 negation disjunction q r))) :
    Derivation (.assertion (star_4_01 negation disjunction p r)) := by
  have line3 := star_10_13 negation disjunction
    (star_4_01 negation disjunction p q)
    (star_4_01 negation disjunction q r) line1 line2
  have line4 := star_4_22 negation disjunction p q r
  exact Derivation.star_9_12_same negation disjunction line3 line4

private theorem star14_equivalenceSubstituteRight
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : Derivation (.assertion
      (star_4_01 negation disjunction p q))) :
    Derivation (.assertion
      (star_4_01 negation disjunction
        (star_4_01 negation disjunction r p)
        (star_4_01 negation disjunction r q))) := by
  have line2 := Derivation.star_9_12_same negation disjunction line1
    (star_4_86 negation disjunction p q r)
  have line3 := star_4_21 negation disjunction r p
  have line4 := star14_equivalenceTransitiveSame negation disjunction
    (star_4_01 negation disjunction r p)
    (star_4_01 negation disjunction p r)
    (star_4_01 negation disjunction q r) line3 line2
  have line5 := star_4_21 negation disjunction q r
  exact star14_equivalenceTransitiveSame negation disjunction
    (star_4_01 negation disjunction r p)
    (star_4_01 negation disjunction q r)
    (star_4_01 negation disjunction r q) line4 line5

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

private theorem star14_scopeNegationImplication
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (negatedScope fixed : Formula signature real [] order) :
    Derivation (.assertion
      (implication negation disjunction
        (implication negation disjunction
          (.neg negation negatedScope) fixed)
        (sameDisjunction disjunction negatedScope fixed))) := by
  have line1 := star_4_13 negation disjunction negatedScope
  have line2 := Derivation.star_9_12_same negation disjunction line1
    (star_4_37 negation disjunction negatedScope
      (.neg negation (.neg negation negatedScope)) fixed)
  have line3 := Derivation.star_9_12_same negation disjunction line2
    (star_3_27 negation disjunction
      (implication negation disjunction
        (sameDisjunction disjunction negatedScope fixed)
        (sameDisjunction disjunction
          (.neg negation (.neg negation negatedScope)) fixed))
      (implication negation disjunction
        (sameDisjunction disjunction
          (.neg negation (.neg negation negatedScope)) fixed)
        (sameDisjunction disjunction negatedScope fixed)))
  exact line3

/-- `Syll` for two independently scoped implication presentations.  The
syntax certificates are exactly the eliminable ✱9·01--·08 readings. -/
private theorem star14_composeCertified
    (vocabularyNegation : signature.Negation vocabularyOrder)
    (vocabularyDisjunction : signature.Disjunction vocabularyOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (pNegated : Formula signature real [] pOrder)
    (qNegated : Formula signature real [] qOrder)
    (pqFormula : Formula signature real [] pqFormulaOrder)
    (qrFormula : Formula signature real [] qrFormulaOrder)
    (prFormula : Formula signature real [] prFormulaOrder)
    (pNegation : signature.Negation pOrder)
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (primitiveOuterNegation : signature.Negation (max qOrder rOrder))
    (primitiveConsequenceNegation : signature.Negation (max pOrder qOrder))
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (primitiveConsequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (primitiveOuterDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (consequenceNegation : signature.Negation pqFormulaOrder)
    (consequenceDisjunction : signature.Disjunction
      (max pqFormulaOrder prFormulaOrder))
    (outerNegation : signature.Negation qrFormulaOrder)
    (outerDisjunction : signature.Disjunction
      (max qrFormulaOrder (max pqFormulaOrder prFormulaOrder)))
    (pNegationDefinition :
      ImplicationNegation signature real pNegation p pNegated)
    (qNegationDefinition :
      ImplicationNegation signature real qNegation q qNegated)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula)
    (line1 : Derivation (.assertion pqFormula))
    (line2 : Derivation (.assertion qrFormula)) :
    Derivation (.assertion prFormula) := by
  let consequenceFormula := mixedImplication consequenceNegation
    consequenceDisjunction pqFormula prFormula
  let formula := mixedImplication outerNegation outerDisjunction
    qrFormula consequenceFormula
  let reading : Star2_05Reading vocabularyNegation vocabularyDisjunction
      p q r formula := {
    pNegated := pNegated
    pNegation := pNegation
    pNegationDefinition := pNegationDefinition
    primitiveQNegation := qNegation
    primitiveQRDisjunction := qrDisjunction
    primitiveOuterNegation := primitiveOuterNegation
    primitiveConsequenceNegation := primitiveConsequenceNegation
    primitivePQDisjunction := pqDisjunction
    primitivePRDisjunction := prDisjunction
    primitiveConsequenceDisjunction := primitiveConsequenceDisjunction
    primitiveOuterDisjunction := primitiveOuterDisjunction
    sumReading := {
      qrFormulaOrder := qrFormulaOrder
      pqFormulaOrder := pqFormulaOrder
      prFormulaOrder := prFormulaOrder
      consequenceFormulaOrder := max pqFormulaOrder prFormulaOrder
      qNegated := qNegated
      qrFormula := qrFormula
      pqFormula := pqFormula
      prFormula := prFormula
      consequenceNegated := .neg consequenceNegation pqFormula
      consequenceFormula := consequenceFormula
      qrNegated := .neg outerNegation qrFormula
      consequenceNegation := consequenceNegation
      outerNegation := outerNegation
      qNegationDefinition := qNegationDefinition
      qrDisjunctionDefinition := qrDisjunctionDefinition
      pqDisjunctionDefinition := pqDisjunctionDefinition
      prDisjunctionDefinition := prDisjunctionDefinition
      consequenceNegationDefinition := .star_1_01 consequenceNegation pqFormula
      consequenceDisjunctionDefinition := .star_1_01 consequenceDisjunction
        (.neg consequenceNegation pqFormula) prFormula
      outerNegationDefinition := .star_1_01 outerNegation qrFormula
      outerDisjunctionDefinition := .star_1_01 outerDisjunction
        (.neg outerNegation qrFormula) consequenceFormula
    }
  }
  have line3 := star_2_05 vocabularyNegation vocabularyDisjunction p q r
    (reading := reading)
  have line4 := Derivation.star_9_12 outerNegation outerDisjunction line2 line3
  exact Derivation.star_9_12 consequenceNegation consequenceDisjunction
    line1 line4

private theorem star14_certifiedSyllogismRight
    (vocabularyNegation : signature.Negation resultOrder)
    (vocabularyDisjunction : signature.Disjunction resultOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (pNegated : Formula signature real [] pOrder)
    (qNegated : Formula signature real [] qOrder)
    (pqFormula qrFormula prFormula : Formula signature real [] resultOrder)
    (pNegation : signature.Negation pOrder)
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (primitiveOuterNegation : signature.Negation (max qOrder rOrder))
    (primitiveConsequenceNegation : signature.Negation (max pOrder qOrder))
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (primitiveConsequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (primitiveOuterDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (pNegationDefinition :
      ImplicationNegation signature real pNegation p pNegated)
    (qNegationDefinition :
      ImplicationNegation signature real qNegation q qNegated)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula)
    (line1 : Derivation (.assertion qrFormula)) :
    Derivation (.assertion
      (implication vocabularyNegation vocabularyDisjunction
        pqFormula prFormula)) := by
  let consequenceFormula := implication vocabularyNegation
    vocabularyDisjunction pqFormula prFormula
  let formula := implication vocabularyNegation vocabularyDisjunction
    qrFormula consequenceFormula
  let reading : Star2_05Reading vocabularyNegation vocabularyDisjunction
      p q r formula := {
    pNegated := pNegated
    pNegation := pNegation
    pNegationDefinition := pNegationDefinition
    primitiveQNegation := qNegation
    primitiveQRDisjunction := qrDisjunction
    primitiveOuterNegation := primitiveOuterNegation
    primitiveConsequenceNegation := primitiveConsequenceNegation
    primitivePQDisjunction := pqDisjunction
    primitivePRDisjunction := prDisjunction
    primitiveConsequenceDisjunction := primitiveConsequenceDisjunction
    primitiveOuterDisjunction := primitiveOuterDisjunction
    sumReading := {
      qrFormulaOrder := resultOrder
      pqFormulaOrder := resultOrder
      prFormulaOrder := resultOrder
      consequenceFormulaOrder := resultOrder
      qNegated := qNegated
      qrFormula := qrFormula
      pqFormula := pqFormula
      prFormula := prFormula
      consequenceNegated := .neg vocabularyNegation pqFormula
      consequenceFormula := consequenceFormula
      qrNegated := .neg vocabularyNegation qrFormula
      consequenceNegation := vocabularyNegation
      outerNegation := vocabularyNegation
      qNegationDefinition := qNegationDefinition
      qrDisjunctionDefinition := qrDisjunctionDefinition
      pqDisjunctionDefinition := pqDisjunctionDefinition
      prDisjunctionDefinition := prDisjunctionDefinition
      consequenceNegationDefinition :=
        .star_1_01 vocabularyNegation pqFormula
      consequenceDisjunctionDefinition :=
        .star_1_01_same vocabularyDisjunction
          (.neg vocabularyNegation pqFormula) prFormula
      outerNegationDefinition := .star_1_01 vocabularyNegation qrFormula
      outerDisjunctionDefinition :=
        .star_1_01_same vocabularyDisjunction
          (.neg vocabularyNegation qrFormula) consequenceFormula
    }
  }
  have line2 := star_2_05 vocabularyNegation vocabularyDisjunction p q r
    (reading := reading)
  exact Derivation.star_9_12_same vocabularyNegation vocabularyDisjunction
    line1 line2

private theorem star14_certifiedSyllogismLeft
    (vocabularyNegation : signature.Negation resultOrder)
    (vocabularyDisjunction : signature.Disjunction resultOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (pNegated : Formula signature real [] pOrder)
    (qNegated : Formula signature real [] qOrder)
    (pqFormula qrFormula prFormula : Formula signature real [] resultOrder)
    (pNegation : signature.Negation pOrder)
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (primitiveOuterNegation : signature.Negation (max qOrder rOrder))
    (primitiveConsequenceNegation : signature.Negation (max pOrder qOrder))
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (primitiveConsequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (primitiveOuterDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (pNegationDefinition :
      ImplicationNegation signature real pNegation p pNegated)
    (qNegationDefinition :
      ImplicationNegation signature real qNegation q qNegated)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula)
    (line1 : Derivation (.assertion pqFormula)) :
    Derivation (.assertion
      (implication vocabularyNegation vocabularyDisjunction
        qrFormula prFormula)) := by
  let consequenceFormula := implication vocabularyNegation
    vocabularyDisjunction pqFormula prFormula
  let formula := implication vocabularyNegation vocabularyDisjunction
    qrFormula consequenceFormula
  let reading : Star2_05Reading vocabularyNegation vocabularyDisjunction
      p q r formula := {
    pNegated := pNegated
    pNegation := pNegation
    pNegationDefinition := pNegationDefinition
    primitiveQNegation := qNegation
    primitiveQRDisjunction := qrDisjunction
    primitiveOuterNegation := primitiveOuterNegation
    primitiveConsequenceNegation := primitiveConsequenceNegation
    primitivePQDisjunction := pqDisjunction
    primitivePRDisjunction := prDisjunction
    primitiveConsequenceDisjunction := primitiveConsequenceDisjunction
    primitiveOuterDisjunction := primitiveOuterDisjunction
    sumReading := {
      qrFormulaOrder := resultOrder
      pqFormulaOrder := resultOrder
      prFormulaOrder := resultOrder
      consequenceFormulaOrder := resultOrder
      qNegated := qNegated
      qrFormula := qrFormula
      pqFormula := pqFormula
      prFormula := prFormula
      consequenceNegated := .neg vocabularyNegation pqFormula
      consequenceFormula := consequenceFormula
      qrNegated := .neg vocabularyNegation qrFormula
      consequenceNegation := vocabularyNegation
      outerNegation := vocabularyNegation
      qNegationDefinition := qNegationDefinition
      qrDisjunctionDefinition := qrDisjunctionDefinition
      pqDisjunctionDefinition := pqDisjunctionDefinition
      prDisjunctionDefinition := prDisjunctionDefinition
      consequenceNegationDefinition :=
        .star_1_01 vocabularyNegation pqFormula
      consequenceDisjunctionDefinition :=
        .star_1_01_same vocabularyDisjunction
          (.neg vocabularyNegation pqFormula) prFormula
      outerNegationDefinition := .star_1_01 vocabularyNegation qrFormula
      outerDisjunctionDefinition :=
        .star_1_01_same vocabularyDisjunction
          (.neg vocabularyNegation qrFormula) consequenceFormula
    }
  }
  have line2 := star_2_05 vocabularyNegation vocabularyDisjunction p q r
    (reading := reading)
  have line3 := Derivation.star_9_12_same vocabularyNegation
    vocabularyDisjunction line2
    (star_2_04 vocabularyNegation vocabularyDisjunction qrFormula pqFormula
      prFormula)
  exact Derivation.star_9_12_same vocabularyNegation vocabularyDisjunction
    line1 line3

private theorem star14_composeCertifiedSame
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r pqFormula : Formula signature real [] order)
    (pqDisjunctionDefinition : ImplicationDisjunction signature real
      (.neg negation p) q pqFormula)
    (line1 : Derivation (.assertion pqFormula))
    (line2 : Derivation (.assertion
      (implication negation disjunction q r))) :
    Derivation (.assertion (implication negation disjunction p r)) := by
  let pairEquality := natMaxSelf order
  let pairNegation := Eq.mp
    (congrArg signature.Negation pairEquality.symm) negation
  let pairDisjunction := Eq.mp
    (congrArg signature.Disjunction pairEquality.symm) disjunction
  let pairPairEquality : max (max order order) (max order order) = order :=
    natMaxCongr pairEquality pairEquality
  let pairPairDisjunction := Eq.mp
    (congrArg signature.Disjunction pairPairEquality.symm) disjunction
  let primitiveOuterEquality :
      max (max order order) (max (max order order) (max order order)) = order :=
    natMaxCongr pairEquality pairPairEquality
  let primitiveOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction primitiveOuterEquality.symm) disjunction
  let outerEquality : max order (max order order) = order := Eq.trans
    (MixedOrder.maxLeftAbsorb order order) pairEquality
  let outerDisjunction := Eq.mp
    (congrArg signature.Disjunction outerEquality.symm) disjunction
  exact star14_composeCertified negation disjunction p q r
    (.neg negation p) (.neg negation q) pqFormula
    (implication negation disjunction q r)
    (implication negation disjunction p r)
    negation negation pairDisjunction pairNegation pairNegation
    pairDisjunction pairDisjunction pairPairDisjunction primitiveOuterDisjunction
    negation pairDisjunction negation outerDisjunction
    (ImplicationNegation.star_1_01 negation p)
    (ImplicationNegation.star_1_01 negation q)
    pqDisjunctionDefinition
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation q) r)
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation p) r)
    line1 line2

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

private theorem star14_commuteRaw
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    Derivation (.assertion
      (MixedOrder.binaryInterpret negation disjunction p q
        (PM.Elementary.imp
          (PM.Elementary.conj MixedOrder.binaryP MixedOrder.binaryQ)
          (PM.Elementary.conj MixedOrder.binaryQ MixedOrder.binaryP)))) := by
  exact MixedOrder.binaryTransport negation disjunction p q
    (PM.FirstEdition.Volume1.Star3.star_3_22
      MixedOrder.binaryP MixedOrder.binaryQ)

private def star14_binaryLeft
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    Formula signature real [] (max negation.leftOrder negation.rightOrder) :=
  MixedOrder.binaryInterpret negation disjunction p q
    (PM.Elementary.conj MixedOrder.binaryP MixedOrder.binaryQ)

private def star14_binaryRight
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    Formula signature real [] (max negation.leftOrder negation.rightOrder) :=
  MixedOrder.binaryInterpret negation disjunction p q
    (PM.Elementary.conj MixedOrder.binaryQ MixedOrder.binaryP)

private theorem star14_commuteNormalized
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    Derivation (.assertion
      (implication negation.both disjunction.both
        (star14_binaryLeft negation disjunction p q)
        (star14_binaryRight negation disjunction p q))) := by
  have line1 := star14_commuteRaw negation disjunction p q
  change Derivation (.assertion
    (implication negation.both disjunction.both
      (star14_binaryLeft negation disjunction p q)
      (star14_binaryRight negation disjunction p q))) at line1
  exact line1

private theorem star14_commuteEquivalenceNormalized
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    Derivation (.assertion
      (star_4_01 negation.both disjunction.both
        (star14_binaryLeft negation disjunction p q)
        (star14_binaryRight negation disjunction p q))) := by
  have line1 := MixedOrder.binaryTransport negation disjunction p q
    (PM.FirstEdition.Volume1.Star4.star_4_3
      MixedOrder.binaryP MixedOrder.binaryQ)
  change Derivation (.assertion
    (star_4_01 negation.both disjunction.both
      (star14_binaryLeft negation disjunction p q)
      (star14_binaryRight negation disjunction p q))) at line1
  exact line1

private theorem star14_binaryLeft_eq
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    star14_binaryLeft negation disjunction p q =
      mixedConjunction negation.left negation.right negation.both
        disjunction.both p q := by
  rfl

private def star14_swappedConjunction
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real apparent negation.leftOrder)
    (q : Formula signature real apparent negation.rightOrder) :
    Formula signature real apparent
      (max negation.leftOrder negation.rightOrder) :=
  let equality := MixedOrder.binaryOrderCombine negation .right .left
  Eq.mp (congrArg (Formula signature real apparent) equality)
    (mixedConjunction negation.right negation.left
      (Eq.mp (congrArg signature.Negation equality.symm) negation.both)
      (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction.both)
      q p)

private theorem star14_castNegation
    (equality : sourceOrder = targetOrder)
    (negation : signature.Negation targetOrder)
    (body : Formula signature real apparent sourceOrder) :
    Eq.mp (congrArg (Formula signature real apparent) equality)
        (.neg (Eq.mp (congrArg signature.Negation equality.symm) negation)
          body) =
      .neg negation
        (Eq.mp (congrArg (Formula signature real apparent) equality) body) := by
  cases equality
  rfl

private theorem star14_swappedConjunction_weakenReal
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real apparent negation.leftOrder)
    (q : Formula signature real apparent negation.rightOrder) :
    (star14_swappedConjunction negation disjunction p q).weakenReal
      (fresh := fresh) =
      star14_swappedConjunction negation disjunction p.weakenReal q.weakenReal := by
  let equality := MixedOrder.binaryOrderCombine negation .right .left
  let body := mixedConjunction negation.right negation.left
    (Eq.mp (congrArg signature.Negation equality.symm) negation.both)
    (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction.both)
    q p
  have line1 := Formula.weakenReal_cast (fresh := fresh) equality body
  change (Eq.mp (congrArg (Formula signature real apparent) equality)
      body).weakenReal =
    Eq.mp (congrArg (Formula signature (fresh :: real) apparent) equality)
      (mixedConjunction negation.right negation.left
        (Eq.mp (congrArg signature.Negation equality.symm) negation.both)
        (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction.both)
        q.weakenReal p.weakenReal)
  change (Eq.mp (congrArg (Formula signature real apparent) equality)
      body).weakenReal =
    Eq.mp (congrArg (Formula signature (fresh :: real) apparent) equality)
      body.weakenReal at line1
  exact line1

private theorem star14_swappedConjunction_substitute
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real source negation.leftOrder)
    (q : Formula signature real source negation.rightOrder)
    (substitution : Substitution signature real source target) :
    (star14_swappedConjunction negation disjunction p q).substitute substitution =
      star14_swappedConjunction negation disjunction
        (p.substitute substitution) (q.substitute substitution) := by
  let equality := MixedOrder.binaryOrderCombine negation .right .left
  let body := mixedConjunction negation.right negation.left
    (Eq.mp (congrArg signature.Negation equality.symm) negation.both)
    (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction.both)
    q p
  have line1 := Formula.substitute_cast equality body substitution
  change (Eq.mp (congrArg (Formula signature real source) equality)
      body).substitute substitution =
    Eq.mp (congrArg (Formula signature real target) equality)
      (mixedConjunction negation.right negation.left
        (Eq.mp (congrArg signature.Negation equality.symm) negation.both)
        (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction.both)
        (q.substitute substitution) (p.substitute substitution))
  change (Eq.mp (congrArg (Formula signature real source) equality)
      body).substitute substitution =
    Eq.mp (congrArg (Formula signature real target) equality)
      (body.substitute substitution) at line1
  exact line1

private theorem star14_binaryRight_eq
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    star14_binaryRight negation disjunction p q =
      star14_swappedConjunction negation disjunction p q := by
  let equality := MixedOrder.binaryOrderCombine negation .right .left
  change Formula.neg negation.both
      (MixedOrder.normalizedDisjunction equality disjunction.both
        (.neg negation.right q) (.neg negation.left p)) =
    Eq.mp (congrArg (Formula signature real []) equality)
      (.neg (Eq.mp (congrArg signature.Negation equality.symm) negation.both)
        (.disj
          (Eq.mp (congrArg signature.Disjunction equality.symm)
            disjunction.both)
          (.neg negation.right q) (.neg negation.left p)))
  rw [star14_castNegation equality negation.both]
  rfl

private def star14_commutePointwise
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [argument] negation.leftOrder)
    (q : Formula signature real [argument] negation.rightOrder) :
    Formula signature real [argument]
      (max negation.leftOrder negation.rightOrder) :=
  implication negation.both disjunction.both
    (mixedConjunction negation.left negation.right negation.both
      disjunction.both p q)
    (star14_swappedConjunction negation disjunction p q)

private theorem star14_commutePointwise_at
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (p : Formula signature real [argument] negation.leftOrder)
    (q : Formula signature real [argument] negation.rightOrder)
    (value : Term signature (argument :: real) [] argument) :
    (star14_commutePointwise negation disjunction p q).weakenReal.instantiate value =
      implication negation.both disjunction.both
        (mixedConjunction negation.left negation.right negation.both
          disjunction.both
          (p.weakenReal.instantiate value) (q.weakenReal.instantiate value))
        (star14_swappedConjunction negation disjunction
          (p.weakenReal.instantiate value)
          (q.weakenReal.instantiate value)) := by
  unfold star14_commutePointwise
  rw [implication_weakenReal, star14_swappedConjunction_weakenReal,
    Formula.instantiate, implication_substitute,
    star14_swappedConjunction_substitute]
  rfl

private theorem star14_existentialCommute
    (negation : MixedOrder.BinaryNegations signature)
    (disjunction : MixedOrder.BinaryDisjunctions signature negation)
    (existential0 : ExistentialVocabulary signature argument
      (max negation.leftOrder negation.rightOrder))
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder (max negation.leftOrder negation.rightOrder) argument))
    (universal2 : signature.Universal argument
      (bindOrder
        (bindOrder (max negation.leftOrder negation.rightOrder) argument)
        argument))
    (disjunction01 : signature.Disjunction
      (max (max negation.leftOrder negation.rightOrder)
        (bindOrder (max negation.leftOrder negation.rightOrder) argument)))
    (negation1 : signature.Negation
      (bindOrder (max negation.leftOrder negation.rightOrder) argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder (max negation.leftOrder negation.rightOrder) argument)
        (bindOrder
          (bindOrder (max negation.leftOrder negation.rightOrder) argument)
          argument)))
    (p : Formula signature real [argument] negation.leftOrder)
    (q : Formula signature real [argument] negation.rightOrder) :
    Derivation (.assertion
      (star_9_22_consequent existential0 existential1 negation.both
        disjunction.both
        (mixedConjunction negation.left negation.right negation.both
          disjunction.both p q)
        (star14_swappedConjunction negation disjunction p q))) := by
  let pointwise := star14_commutePointwise negation disjunction p q
  let value : Term signature (argument :: real) [] argument := .real .zero
  have line1 := star14_commuteNormalized negation disjunction
    (p.weakenReal.instantiate value) (q.weakenReal.instantiate value)
  rw [star14_binaryLeft_eq, star14_binaryRight_eq] at line1
  have line2 := star_10_11 existential0.universal pointwise
    (Derivation.castAssertion
      (star14_commutePointwise_at negation disjunction p q value) line1)
  have line3 := star_10_28 existential0 existential1 universal2
    negation.both disjunction.both disjunction01 negation1 disjunction12
    (mixedConjunction negation.left negation.right negation.both
      disjunction.both p q)
    (star14_swappedConjunction negation disjunction p q)
  letI : ImplicationReading negation1 disjunction12
      (.always existential0.universal pointwise)
      (.always universal2
        (star_9_22_body existential0 existential1 negation.both
          disjunction.both
          (mixedConjunction negation.left negation.right negation.both
            disjunction.both p q)
          (star14_swappedConjunction negation disjunction p q)))
      (star_9_22_consequent existential0 existential1 negation.both
        disjunction.both
        (mixedConjunction negation.left negation.right negation.both
          disjunction.both p q)
        (star14_swappedConjunction negation disjunction p q)) :=
    star_9_22_implicationReading existential0 existential1 universal2
      negation.both disjunction.both negation1 disjunction12
      (mixedConjunction negation.left negation.right negation.both
        disjunction.both p q)
      (star14_swappedConjunction negation disjunction p q)
  exact Derivation.star_9_12 negation1 disjunction12 line2 line3

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

private theorem star14_mixedConjunction_weakenReal
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    (mixedConjunction leftNegation rightNegation outerNegation disjunction
      left right).weakenReal (fresh := fresh) =
    mixedConjunction leftNegation rightNegation outerNegation disjunction
      left.weakenReal right.weakenReal := by
  rfl

private theorem star14_always_weakenReal
    (universal : signature.Universal argument order)
    (body : Formula signature real (argument :: apparent) order) :
    (Formula.always universal body).weakenReal (fresh := fresh) =
      Formula.always universal body.weakenReal := by
  rfl

private theorem star14_sometimes_weakenReal
    (existential : ExistentialVocabulary signature argument order)
    (body : Formula signature real (argument :: apparent) order) :
    (Formula.sometimes existential body).weakenReal (fresh := fresh) =
      Formula.sometimes existential body.weakenReal := by
  rfl

private theorem star14_conjunction_weakenReal
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (conjunction negation disjunction left right).weakenReal
        (fresh := fresh) =
      conjunction negation disjunction left.weakenReal right.weakenReal := by
  unfold conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  rfl

private theorem star14_mixedConjunction_substitute
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature real source leftOrder)
    (right : Formula signature real source rightOrder)
    (substitution : Substitution signature real source target) :
    (mixedConjunction leftNegation rightNegation outerNegation disjunction
      left right).substitute substitution =
    mixedConjunction leftNegation rightNegation outerNegation disjunction
      (left.substitute substitution) (right.substitute substitution) := by
  rfl

private theorem star14_identity_weakenReal
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real apparent sort) :
    (star_13_01 vocabulary x y).weakenReal (fresh := fresh) =
      star_13_01 vocabulary x.weakenReal y.weakenReal := by
  unfold star_13_01
  dsimp
  change Formula.always vocabulary.universal
    ((implication vocabulary.negation vocabulary.disjunction
      (applyUnary (.apparent .zero) x.weaken)
      (applyUnary (.apparent .zero) y.weaken)).weakenReal) = _
  rw [implication_weakenReal]
  cases x <;> cases y <;> rfl

private theorem star14_identity_substitute
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real source sort)
    (substitution : Substitution signature real source target) :
    (star_13_01 vocabulary x y).substitute substitution =
      star_13_01 vocabulary (x.substitute substitution)
        (y.substitute substitution) := by
  unfold star_13_01
  change Formula.always vocabulary.universal
    ((implication vocabulary.negation vocabulary.disjunction
      (applyUnary (.apparent .zero) x.weaken)
      (applyUnary (.apparent .zero) y.weaken)).substitute
        (liftSubstitution substitution)) = _
  rw [implication_substitute]
  cases x <;> cases y <;> rfl

private theorem star14_conditionUnderCandidate_instantiate
    (condition : Formula signature real [sort] order) :
    ((condition.rename (liftRenaming (fun v => .succ v))).weakenReal
      (fresh := sort)).substitute
        (liftSubstitution (instantiateSubstitution
          (.real (.zero : Var (sort :: real) sort)))) =
      condition.weakenReal := by
  rw [Formula.weakenReal_rename]
  let identitySubstitution :
      Substitution signature (sort :: real) [sort] [sort] :=
    fun v => .apparent v
  have pointwise : ∀ {variableSort} (v : Var [sort] variableSort),
      liftSubstitution (instantiateSubstitution
        (.real (.zero : Var (sort :: real) sort)))
        (liftRenaming (fun v => .succ v) v) = identitySubstitution v := by
    intro variableSort v
    cases v <;> rfl
  have line1 := Formula.rename_substitute_of_pointwise
    (liftRenaming (fun v => .succ v))
    (liftSubstitution (instantiateSubstitution
      (.real (.zero : Var (sort :: real) sort))))
    identitySubstitution pointwise condition.weakenReal
  rw [line1]
  exact Formula.substitute_eq_self condition.weakenReal (by
    intro variableSort v
    rfl)

private theorem star14_conditionUnderCandidate_instantiateClosed
    (condition : Formula signature real [sort] order)
    (value : Term signature real [] sort) :
    (condition.rename (liftRenaming (fun v => .succ v))).substitute
        (liftSubstitution (instantiateSubstitution value)) = condition := by
  let identitySubstitution :
      Substitution signature real [sort] [sort] :=
    fun v => .apparent v
  have pointwise : ∀ {variableSort} (v : Var [sort] variableSort),
      liftSubstitution (instantiateSubstitution value)
        (liftRenaming (fun v => .succ v) v) = identitySubstitution v := by
    intro variableSort v
    cases v <;> rfl
  have line1 := Formula.rename_substitute_of_pointwise
    (liftRenaming (fun v => .succ v))
    (liftSubstitution (instantiateSubstitution value))
    identitySubstitution pointwise condition
  rw [line1]
  exact Formula.substitute_eq_self condition (by
    intro variableSort v
    rfl)

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

private theorem star14_equivalence_castOrder
    (equality : sourceOrder = targetOrder)
    (negation : signature.Negation targetOrder)
    (disjunction : signature.Disjunction targetOrder)
    (left right : Formula signature real apparent sourceOrder) :
    Eq.mp (congrArg (Formula signature real apparent) equality)
        (equivalence
          (Eq.mp (congrArg signature.Negation equality.symm) negation)
          (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
          left right) =
      equivalence negation disjunction
        (Eq.mp (congrArg (Formula signature real apparent) equality) left)
        (Eq.mp (congrArg (Formula signature real apparent) equality) right) := by
  cases equality
  rfl

private theorem star14_implication_castOrder
    (equality : sourceOrder = targetOrder)
    (negation : signature.Negation targetOrder)
    (disjunction : signature.Disjunction targetOrder)
    (left right : Formula signature real apparent sourceOrder) :
    Eq.mp (congrArg (Formula signature real apparent) equality)
        (implication
          (Eq.mp (congrArg signature.Negation equality.symm) negation)
          (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
          left right) =
      implication negation disjunction
        (Eq.mp (congrArg (Formula signature real apparent) equality) left)
        (Eq.mp (congrArg (Formula signature real apparent) equality) right) := by
  cases equality
  rfl

private theorem star14_conjunction_castOrder
    (equality : sourceOrder = targetOrder)
    (negation : signature.Negation targetOrder)
    (disjunction : signature.Disjunction targetOrder)
    (left right : Formula signature real apparent sourceOrder) :
    Eq.mp (congrArg (Formula signature real apparent) equality)
        (conjunction
          (Eq.mp (congrArg signature.Negation equality.symm) negation)
          (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
          left right) =
      conjunction negation disjunction
        (Eq.mp (congrArg (Formula signature real apparent) equality) left)
        (Eq.mp (congrArg (Formula signature real apparent) equality) right) := by
  cases equality
  rfl

private theorem star14_sometimes_castOrder
    (equality : sourceOrder = targetOrder)
    (existential : ExistentialVocabulary signature sort targetOrder)
    (body : Formula signature real [sort] sourceOrder) :
    Eq.mp (congrArg (Formula signature real [])
        (congrArg (fun matrixOrder => bindOrder matrixOrder sort) equality))
        (Formula.sometimes {
          printed := Eq.mp
            (congrArg (signature.Existential sort) equality.symm)
            existential.printed
          matrixNegation := Eq.mp
            (congrArg signature.Negation equality.symm)
            existential.matrixNegation
          universal := Eq.mp
            (congrArg (signature.Universal sort) equality.symm)
            existential.universal
          outerNegation := Eq.mp
            (congrArg signature.Negation
              (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
                equality).symm)
            existential.outerNegation
        } body) =
      Formula.sometimes existential
        (Eq.mp (congrArg (Formula signature real [sort]) equality) body) := by
  cases equality
  rfl

private theorem star14_star10_23_right_castMatrix
    (equality : sourceMatrixOrder = targetMatrixOrder)
    (sourceCollapse : max sourceMatrixOrder fixedOrder = sourceMatrixOrder)
    (targetCollapse : max targetMatrixOrder fixedOrder = targetMatrixOrder)
    (existential : ExistentialVocabulary signature sort targetMatrixOrder)
    (scopeUniversal : signature.Universal sort
      (max targetMatrixOrder fixedOrder))
    (matrixNegation : signature.Negation targetMatrixOrder)
    (matrixDisjunction : signature.Disjunction
      (max targetMatrixOrder fixedOrder))
    (body : Formula signature real [sort] sourceMatrixOrder)
    (fixed : Formula signature real [] fixedOrder) :
    Eq.mp (congrArg (Formula signature real [])
        (congrArg (fun matrixOrder => bindOrder matrixOrder sort) equality))
        (Eq.mp (congrArg (Formula signature real [])
            (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
              sourceCollapse))
          (star_10_23_right {
              printed := Eq.mp
                (congrArg (signature.Existential sort) equality.symm)
                existential.printed
              matrixNegation := Eq.mp
                (congrArg signature.Negation equality.symm)
                existential.matrixNegation
              universal := Eq.mp
                (congrArg (signature.Universal sort) equality.symm)
                existential.universal
              outerNegation := Eq.mp
                (congrArg signature.Negation
                  (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
                    equality).symm)
                existential.outerNegation
            }
            (Eq.mp (congrArg (signature.Universal sort) equality.symm)
              existential.universal)
            (Eq.mp (congrArg (signature.Universal sort)
              (congrArg (fun matrixOrder => max matrixOrder fixedOrder)
                equality).symm) scopeUniversal)
            (Eq.mp (congrArg signature.Negation equality.symm)
              matrixNegation)
            (Eq.mp (congrArg signature.Disjunction
              (congrArg (fun matrixOrder => max matrixOrder fixedOrder)
                equality).symm) matrixDisjunction)
            body fixed)) =
      Eq.mp (congrArg (Formula signature real [])
          (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
            targetCollapse))
        (star_10_23_right existential existential.universal scopeUniversal
          matrixNegation matrixDisjunction
          (Eq.mp (congrArg (Formula signature real [sort]) equality) body)
          fixed) := by
  cases equality
  rfl

private theorem star14_normalizedMixedImplication_cast
    (leftEquality : sourceLeftOrder = targetLeftOrder)
    (rightEquality : sourceRightOrder = targetRightOrder)
    (resultEquality : sourceResultOrder =
      max targetLeftOrder targetRightOrder)
    (sourceEquality : max sourceLeftOrder sourceRightOrder =
      sourceResultOrder)
    (negation : signature.Negation targetLeftOrder)
    (disjunction : signature.Disjunction
      (max targetLeftOrder targetRightOrder))
    (left : Formula signature real [] sourceLeftOrder)
    (right : Formula signature real [] sourceRightOrder) :
    Eq.mp (congrArg (Formula signature real []) resultEquality)
        (MixedOrder.normalizedDisjunction sourceEquality
          (Eq.mp (congrArg signature.Disjunction resultEquality.symm)
            disjunction)
          (.neg
            (Eq.mp (congrArg signature.Negation leftEquality.symm) negation)
            left)
          right) =
      mixedImplication negation disjunction
        (Eq.mp (congrArg (Formula signature real []) leftEquality) left)
        (Eq.mp (congrArg (Formula signature real []) rightEquality) right) := by
  cases leftEquality
  cases rightEquality
  cases resultEquality
  rfl

private theorem star14_normalizedImplication_castOrder
    (leftEquality : sourceLeftOrder = targetOrder)
    (rightEquality : sourceRightOrder = targetOrder)
    (resultEquality : sourceResultOrder = targetOrder)
    (sourceEquality : max sourceLeftOrder sourceRightOrder =
      sourceResultOrder)
    (negation : signature.Negation targetOrder)
    (disjunction : signature.Disjunction targetOrder)
    (left : Formula signature real [] sourceLeftOrder)
    (right : Formula signature real [] sourceRightOrder) :
    Eq.mp (congrArg (Formula signature real []) resultEquality)
        (MixedOrder.normalizedDisjunction sourceEquality
          (Eq.mp (congrArg signature.Disjunction resultEquality.symm)
            disjunction)
          (.neg
            (Eq.mp (congrArg signature.Negation leftEquality.symm) negation)
            left)
          right) =
      implication negation disjunction
        (Eq.mp (congrArg (Formula signature real []) leftEquality) left)
        (Eq.mp (congrArg (Formula signature real []) rightEquality) right) := by
  cases leftEquality
  cases rightEquality
  cases resultEquality
  rfl

private theorem star14_matrixEquivalence_weakenReal
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (equivalence negation disjunction left right).weakenReal
      (fresh := fresh) =
      equivalence negation disjunction left.weakenReal right.weakenReal := by
  unfold equivalence conjunction
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

private theorem star14_matrixEquivalence_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (substitution : Substitution signature real source target) :
    (equivalence negation disjunction left right).substitute substitution =
      equivalence negation disjunction
        (left.substitute substitution) (right.substitute substitution) := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).substitute
        substitution) = _
  rw [sameDisjunction_substitute]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).substitute substitution))
      (.neg negation
        ((implication negation disjunction right left).substitute substitution))) = _
  rw [implication_substitute, implication_substitute]

private theorem star14_castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

private theorem star14_cast_trans
    (first : firstOrder = middleOrder)
    (second : middleOrder = finalOrder)
    (item : family firstOrder) :
    Eq.mp (congrArg family (Eq.trans first second)) item =
      Eq.mp (congrArg family second)
        (Eq.mp (congrArg family first) item) := by
  cases first
  cases second
  rfl

private theorem star14_max_eq_left_of_le
    {left right : Nat} (ordering : right ≤ left) : max left right = left := by
  exact Eq.trans (MixedOrder.maxComm left right)
    (Nat.max_eq_right ordering)

private theorem star14_le_max_left (left right : Nat) :
    left ≤ max left right := by
  unfold Max.max Nat.instMax maxOfLe
  change left ≤ (if left ≤ right then right else left)
  by_cases ordering : left ≤ right
  · rw [if_pos ordering]
    exact ordering
  · rw [if_neg ordering]
    exact Nat.le_refl left

private theorem star14_le_max_right (left right : Nat) :
    right ≤ max left right := by
  exact Eq.mp
    (congrArg (fun order => right ≤ order)
      (MixedOrder.maxComm right left))
    (star14_le_max_left right left)

/-- At the least order admitted by `sort`, binding one variable has the same
assigned order.  This is the pure kernel calculation used for ✱14·18. -/
private theorem star14_bindOrderHeight (sort : RSort) :
    bindOrder (Nat.succ sort.height) sort = Nat.succ sort.height := by
  unfold bindOrder
  exact natMaxSelf _

private theorem star14_identityOrderStable (order : Nat) (sort : RSort) :
    bindOrder (bindOrder order (.function [sort] order 0)) sort =
      bindOrder order (.function [sort] order 0) := by
  let argumentHeight : sort.height ≤ RSort.maxHeight [sort] :=
    star14_le_max_left sort.height (RSort.maxHeight [])
  let argumentSucc : Nat.succ sort.height ≤
      Nat.succ (RSort.maxHeight [sort]) :=
    Nat.succ_le_succ argumentHeight
  let functionHeight : Nat.succ (RSort.maxHeight [sort]) ≤
      RSort.height (.function [sort] order 0) :=
    star14_le_max_left (Nat.succ (RSort.maxHeight [sort])) (Nat.succ order)
  let boundHeight : Nat.succ sort.height ≤
      Nat.succ (RSort.height (.function [sort] order 0)) :=
    Nat.le.step (Nat.le_trans argumentSucc functionHeight)
  let identityHeight : Nat.succ sort.height ≤
      bindOrder order (.function [sort] order 0) :=
    Nat.le_trans boundHeight
      (star14_le_max_right order
        (Nat.succ (RSort.height (.function [sort] order 0))))
  unfold bindOrder
  exact star14_max_eq_left_of_le identityHeight

private theorem star14_bindOrderStable (baseOrder : Nat) (sort : RSort) :
    bindOrder (bindOrder baseOrder sort) sort = bindOrder baseOrder sort := by
  unfold bindOrder
  exact MixedOrder.maxRightAbsorb baseOrder (Nat.succ sort.height)

private def star14_saturatedUniversal
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real (sort :: apparent)
      (bindOrder baseOrder sort)) :
    Formula signature real apparent (bindOrder baseOrder sort) :=
  Eq.mp (congrArg (Formula signature real apparent)
    (star14_bindOrderStable baseOrder sort)) (.always universal body)

private theorem star14_saturatedEquivalenceScope_cast
    (collapse : targetOrder = sourceOrder)
    (sourceBind : bindOrder sourceOrder sort = targetOrder)
    (targetBind : bindOrder targetOrder sort = targetOrder)
    (universal : signature.Universal sort sourceOrder)
    (negation : signature.Negation sourceOrder)
    (disjunction : signature.Disjunction sourceOrder)
    (left right : Formula signature real (sort :: apparent) sourceOrder) :
    Eq.mp (congrArg (Formula signature real apparent) targetBind)
        (.always
          (Eq.mp (congrArg (signature.Universal sort) collapse.symm)
            universal)
          (equivalence
            (Eq.mp (congrArg signature.Negation collapse.symm) negation)
            (Eq.mp (congrArg signature.Disjunction collapse.symm) disjunction)
            (Eq.mp (congrArg (Formula signature real (sort :: apparent))
              collapse.symm) left)
            (Eq.mp (congrArg (Formula signature real (sort :: apparent))
              collapse.symm) right))) =
      Eq.mp (congrArg (Formula signature real apparent) sourceBind)
        (.always universal (equivalence negation disjunction left right)) := by
  cases collapse
  rfl

private def star14_saturatedExistential
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  .neg negation
    (star14_saturatedUniversal universal (.neg negation body))

private theorem star14_cast_self
    (equality : order = order)
    (value : family order) :
    Eq.mp (congrArg family equality) value = value := by
  have line1 : equality = rfl := rfl
  cases line1
  rfl

private theorem star14_saturatedExistential_cast
    (collapse : sourceOrder = bindOrder baseOrder sort)
    (sourceBind : bindOrder sourceOrder sort = bindOrder baseOrder sort)
    (targetBind : bindOrder (bindOrder baseOrder sort) sort =
      bindOrder baseOrder sort)
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort] sourceOrder) :
    Eq.mp (congrArg (Formula signature real []) sourceBind)
        (.neg (Eq.mp (congrArg signature.Negation sourceBind.symm) negation)
          (.always
            (Eq.mp (congrArg (signature.Universal sort) collapse.symm)
              universal)
            (.neg (Eq.mp (congrArg signature.Negation collapse.symm)
              negation) body))) =
      star14_saturatedExistential universal negation
        (Eq.mp (congrArg (Formula signature real [sort]) collapse) body) := by
  subst sourceOrder
  rw [show sourceBind = targetBind from rfl]
  unfold star14_saturatedExistential star14_saturatedUniversal
  rw [star14_castNegation, star14_cast_self, star14_cast_self,
    star14_cast_self]
  rfl
  rfl
  rfl
  exact targetBind

private def star14_castImplicationDisjunctionOrder
    (equality : sourceOrder = targetOrder)
    (left : Formula signature real [] leftOrder)
    (right result : Formula signature real [] sourceOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real left
      (Eq.mp (congrArg (Formula signature real []) equality) right)
      (Eq.mp (congrArg (Formula signature real []) equality) result) := by
  cases equality
  exact reading

private def star14_castImplicationDisjunctionLeftOrder
    (equality : sourceOrder = targetOrder)
    (left result : Formula signature real [] sourceOrder)
    (right : Formula signature real [] rightOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real
      (Eq.mp (congrArg (Formula signature real []) equality) left) right
      (Eq.mp (congrArg (Formula signature real []) equality) result) := by
  cases equality
  exact reading

private def star14_castImplicationDisjunctionMixed
    (leftEquality : sourceLeftOrder = targetLeftOrder)
    (resultEquality : sourceResultOrder = targetResultOrder)
    (left : Formula signature real [] sourceLeftOrder)
    (right : Formula signature real [] rightOrder)
    (result : Formula signature real [] sourceResultOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real
      (Eq.mp (congrArg (Formula signature real []) leftEquality) left) right
      (Eq.mp (congrArg (Formula signature real []) resultEquality)
        result) := by
  cases leftEquality
  cases resultEquality
  exact reading

private def star14_castImplicationNegationOrder
    (equality : sourceOrder = targetOrder)
    (negation : signature.Negation targetOrder)
    (formula negated : Formula signature real [] sourceOrder)
    (reading : ImplicationNegation signature real
      (Eq.mp (congrArg signature.Negation equality.symm) negation)
      formula negated) :
    ImplicationNegation signature real negation
      (Eq.mp (congrArg (Formula signature real []) equality) formula)
      (Eq.mp (congrArg (Formula signature real []) equality) negated) := by
  cases equality
  exact reading

private def star14_castImplicationDisjunctionResult
    (equality : sourceOrder = targetOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder)
    (result : Formula signature real apparent sourceOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real left right
      (Eq.mp (congrArg (Formula signature real apparent) equality) result) := by
  cases equality
  exact reading

private def star14_stableScopeImplicationDisjunction
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (matrix : Formula signature real [sort] (bindOrder baseOrder sort)) :
    ImplicationDisjunction signature real (.neg negation p)
      (star14_saturatedUniversal universal matrix)
      (star_10_21_stable_right (baseOrder := baseOrder) universal negation
        disjunction p matrix) := by
  let body := sameDisjunction disjunction
    ((Formula.neg negation p).rename (fun v => .succ v)) matrix
  have raw := ImplicationDisjunction.star_9_04 universal universal
    (.neg negation p) matrix body
    (ImplicationDisjunction.star_1_01_same disjunction
      ((Formula.neg negation p).rename (fun v => .succ v)) matrix)
  have cast := star14_castImplicationDisjunctionOrder
    (star14_bindOrderStable baseOrder sort) (.neg negation p)
    (.always universal matrix) (.always universal body) raw
  change ImplicationDisjunction signature real (.neg negation p)
    (star14_saturatedUniversal universal matrix)
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction p matrix) at cast
  exact cast

private theorem star14_composeStableScope
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (matrix : Formula signature real [sort] (bindOrder baseOrder sort))
    (r : Formula signature real [] (bindOrder baseOrder sort))
    (line1 : Derivation (.assertion
      (star_10_21_stable_right (baseOrder := baseOrder) universal negation
        disjunction p matrix)))
    (line2 : Derivation (.assertion
      (implication negation disjunction
        (star14_saturatedUniversal universal matrix) r))) :
    Derivation (.assertion (implication negation disjunction p r)) := by
  exact star14_composeCertifiedSame negation disjunction p
    (star14_saturatedUniversal universal matrix) r
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction p matrix)
    (star14_stableScopeImplicationDisjunction universal negation disjunction
      p matrix) line1 line2

private theorem star14_liftSaturatedUniversalEquivalence
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (left right : Formula signature real [sort] (bindOrder baseOrder sort))
    (line1 : Derivation (.assertion
      (star_4_01 negation disjunction
        (left.weakenReal.instantiate (.real .zero))
        (right.weakenReal.instantiate (.real .zero))))) :
    Derivation (.assertion
      (star_4_01 negation disjunction
        (star14_saturatedUniversal universal left)
        (star14_saturatedUniversal universal right))) := by
  let pointwise := equivalence negation disjunction left right
  let value : Term signature (sort :: real) [] sort := .real .zero
  have pointwiseAt : pointwise.weakenReal.instantiate value =
      star_4_01 negation disjunction
        (left.weakenReal.instantiate value)
        (right.weakenReal.instantiate value) := by
    unfold pointwise
    rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
      star14_matrixEquivalence_substitute]
    rfl
  have line2 := star_10_11 universal pointwise
    (Derivation.castAssertion pointwiseAt line1)
  have line2Cast := star14_castAssertionOrder
    (star14_bindOrderStable baseOrder sort)
    (.always universal pointwise) line2
  have line3 := star_10_271 (baseOrder := baseOrder) universal negation
    disjunction left right
  unfold star_10_271_reading star_10_271_left star_10_271_right at line3
  exact Derivation.star_9_12_same negation disjunction line2Cast line3

private theorem star14_liftSaturatedExistentialEquivalence
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (left right : Formula signature real [sort] (bindOrder baseOrder sort))
    (line1 : Derivation (.assertion
      (star_4_01 negation disjunction
        (left.weakenReal.instantiate (.real .zero))
        (right.weakenReal.instantiate (.real .zero))))) :
    Derivation (.assertion
      (star_4_01 negation disjunction
        (star14_saturatedExistential universal negation left)
        (star14_saturatedExistential universal negation right))) := by
  let value : Term signature (sort :: real) [] sort := .real .zero
  let leftAt := left.weakenReal.instantiate value
  let rightAt := right.weakenReal.instantiate value
  let pointwise := star_4_01 negation disjunction leftAt rightAt
  let negatedPointwise := star_4_01 negation disjunction
    (.neg negation leftAt) (.neg negation rightAt)
  have line2a := star_4_11 (negation := negation) (disjunction := disjunction)
    leftAt rightAt
  have line2b := Derivation.star_9_12_same negation disjunction line2a
    (star_3_26 negation disjunction
      (implication negation disjunction pointwise negatedPointwise)
      (implication negation disjunction negatedPointwise pointwise))
  have line2 := Derivation.star_9_12_same negation disjunction line1 line2b
  have line3 := star14_liftSaturatedUniversalEquivalence universal negation
    disjunction (.neg negation left) (.neg negation right) line2
  let universalLeft := star14_saturatedUniversal universal
    (.neg negation left)
  let universalRight := star14_saturatedUniversal universal
    (.neg negation right)
  let lifted := star_4_01 negation disjunction universalLeft universalRight
  let negatedLifted := star_4_01 negation disjunction
    (.neg negation universalLeft) (.neg negation universalRight)
  have line4a := star_4_11 (negation := negation) (disjunction := disjunction)
    universalLeft universalRight
  have line4b := Derivation.star_9_12_same negation disjunction line4a
    (star_3_26 negation disjunction
      (implication negation disjunction lifted negatedLifted)
      (implication negation disjunction negatedLifted lifted))
  have line4 := Derivation.star_9_12_same negation disjunction line3 line4b
  unfold star14_saturatedExistential
  exact line4

private theorem star14_saturatedExistentialEquivalenceImplication
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (left right : Formula signature real [sort] (bindOrder baseOrder sort)) :
    Derivation (.assertion
      (implication negation disjunction
        (star14_saturatedUniversal universal
          (equivalence negation disjunction left right))
        (star_4_01 negation disjunction
          (star14_saturatedExistential universal negation left)
          (star14_saturatedExistential universal negation right)))) := by
  let equivalenceMatrix := equivalence negation disjunction left right
  let negatedEquivalenceMatrix := equivalence negation disjunction
    (.neg negation left) (.neg negation right)
  let value : Term signature (sort :: real) [] sort := .real .zero
  let leftAt := left.weakenReal.instantiate value
  let rightAt := right.weakenReal.instantiate value
  let equivalenceAt := star_4_01 negation disjunction leftAt rightAt
  let negatedEquivalenceAt := star_4_01 negation disjunction
    (.neg negation leftAt) (.neg negation rightAt)
  have line1a := star_4_11 (negation := negation) (disjunction := disjunction)
    leftAt rightAt
  have line1Raw := Derivation.star_9_12_same negation disjunction line1a
    (star_3_26 negation disjunction
      (implication negation disjunction equivalenceAt negatedEquivalenceAt)
      (implication negation disjunction negatedEquivalenceAt equivalenceAt))
  have matrixAt :
      (implication negation disjunction equivalenceMatrix
        negatedEquivalenceMatrix).weakenReal.instantiate value =
      implication negation disjunction equivalenceAt negatedEquivalenceAt := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    change implication negation disjunction
      (equivalenceMatrix.weakenReal.instantiate value)
      (negatedEquivalenceMatrix.weakenReal.instantiate value) = _
    have equivalenceAtEquality :
        equivalenceMatrix.weakenReal.instantiate value = equivalenceAt := by
      unfold equivalenceMatrix equivalenceAt
      rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
        star14_matrixEquivalence_substitute]
      rfl
    have negatedEquivalenceAtEquality :
        negatedEquivalenceMatrix.weakenReal.instantiate value =
          negatedEquivalenceAt := by
      unfold negatedEquivalenceMatrix negatedEquivalenceAt
      rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
        star14_matrixEquivalence_substitute]
      rfl
    rw [equivalenceAtEquality, negatedEquivalenceAtEquality]
  have line1 := Derivation.castAssertion matrixAt line1Raw
  have line2Raw := star_10_11 universal
    (implication negation disjunction equivalenceMatrix
      negatedEquivalenceMatrix) line1
  have line2 := star14_castAssertionOrder
    (star14_bindOrderStable baseOrder sort)
    (.always universal
      (implication negation disjunction equivalenceMatrix
        negatedEquivalenceMatrix)) line2Raw
  have distribution := star_10_27_saturated (baseOrder := baseOrder)
    universal negation disjunction equivalenceMatrix negatedEquivalenceMatrix
  unfold star_10_27_saturated_reading star_10_27_saturated_left
    star_10_27_saturated_right at distribution
  have line3 := Derivation.star_9_12_same negation disjunction line2 distribution
  have equivalenceLift := star_10_271 (baseOrder := baseOrder)
    universal negation disjunction (.neg negation left) (.neg negation right)
  unfold star_10_271_reading star_10_271_left star_10_271_right at equivalenceLift
  have line4 := star14_composeSame negation disjunction
    (star14_saturatedUniversal universal equivalenceMatrix)
    (star14_saturatedUniversal universal negatedEquivalenceMatrix)
    (star_4_01 negation disjunction
      (star14_saturatedUniversal universal (.neg negation left))
      (star14_saturatedUniversal universal (.neg negation right)))
    line3 equivalenceLift
  let universalLeft := star14_saturatedUniversal universal
    (.neg negation left)
  let universalRight := star14_saturatedUniversal universal
    (.neg negation right)
  let lifted := star_4_01 negation disjunction universalLeft universalRight
  let negatedLifted := star_4_01 negation disjunction
    (.neg negation universalLeft) (.neg negation universalRight)
  have line5a := star_4_11 (negation := negation) (disjunction := disjunction)
    universalLeft universalRight
  have line5 := Derivation.star_9_12_same negation disjunction line5a
    (star_3_26 negation disjunction
      (implication negation disjunction lifted negatedLifted)
      (implication negation disjunction negatedLifted lifted))
  unfold star14_saturatedExistential
  exact star14_composeSame negation disjunction _ _ _ line4 line5

private theorem star14_liftConditionalSaturatedExistentialEquivalence
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (hypothesis : Formula signature real [] (bindOrder baseOrder sort))
    (left right : Formula signature real [sort] (bindOrder baseOrder sort))
    (line1 : Derivation (.assertion
      (implication negation disjunction hypothesis.weakenReal
        (star_4_01 negation disjunction
          (left.weakenReal.instantiate (.real .zero))
          (right.weakenReal.instantiate (.real .zero)))))) :
    Derivation (.assertion
      (implication negation disjunction hypothesis
        (star_4_01 negation disjunction
          (star14_saturatedExistential universal negation left)
          (star14_saturatedExistential universal negation right)))) := by
  let equivalenceMatrix := equivalence negation disjunction left right
  let conditionalMatrix := implication negation disjunction
    (hypothesis.rename (fun v => .succ v)) equivalenceMatrix
  let value : Term signature (sort :: real) [] sort := .real .zero
  have conditionalAt : conditionalMatrix.weakenReal.instantiate value =
      implication negation disjunction hypothesis.weakenReal
        (star_4_01 negation disjunction
          (left.weakenReal.instantiate value)
          (right.weakenReal.instantiate value)) := by
    unfold conditionalMatrix
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    change implication negation disjunction
      (((hypothesis.rename (fun v => .succ v)).weakenReal).instantiate value)
      (equivalenceMatrix.weakenReal.instantiate value) = _
    rw [Formula.closed_weakenReal_instantiate]
    unfold equivalenceMatrix
    rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
      star14_matrixEquivalence_substitute]
    rfl
  have line2Raw := star_10_11 universal conditionalMatrix
    (Derivation.castAssertion conditionalAt line1)
  have line2 := star14_castAssertionOrder
    (star14_bindOrderStable baseOrder sort)
    (.always universal conditionalMatrix) line2Raw
  change Derivation (.assertion
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction hypothesis equivalenceMatrix)) at line2
  have line3 := star14_saturatedExistentialEquivalenceImplication
    universal negation disjunction left right
  exact star14_composeStableScope universal negation disjunction hypothesis
    equivalenceMatrix
    (star_4_01 negation disjunction
      (star14_saturatedExistential universal negation left)
      (star14_saturatedExistential universal negation right)) line2 line3

private theorem star14_innerUniquenessTransport
    (vocabulary : IdentityVocabulary signature sort order 0)
    (identityUniversal : signature.Universal sort
      (bindOrder order (.function [sort] order 0)))
    (identityNegation : signature.Negation
      (bindOrder order (.function [sort] order 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder order (.function [sort] order 0)))
    (condition : Formula signature real [sort]
      (bindOrder order (.function [sort] order 0)))
    (b c : Term signature real [] sort) :
    let identityOrder := bindOrder order (.function [sort] order 0)
    let stability := star14_identityOrderStable order sort
    let stableUniversal := Eq.mp
      (congrArg (signature.Universal sort) stability.symm) identityUniversal
    let stableNegation := Eq.mp
      (congrArg signature.Negation stability.symm) identityNegation
    let stableDisjunction := Eq.mp
      (congrArg signature.Disjunction stability.symm) identityDisjunction
    let x : Term signature real [sort] sort := .apparent .zero
    let identityB := star_13_01 vocabulary x b.weaken
    let identityC := star_13_01 vocabulary x c.weaken
    let stableCondition := Eq.mp (congrArg
      (Formula signature real [sort]) stability.symm) condition
    let stableIdentityB := Eq.mp (congrArg
      (Formula signature real [sort]) stability.symm) identityB
    let stableIdentityC := Eq.mp (congrArg
      (Formula signature real [sort]) stability.symm) identityC
    let hypothesisMatrix := equivalence stableNegation stableDisjunction
      stableCondition stableIdentityB
    let leftMatrix := equivalence stableNegation stableDisjunction
      stableCondition stableIdentityC
    let rightMatrix := equivalence stableNegation stableDisjunction
      stableIdentityB stableIdentityC
    let hypothesis := star14_saturatedUniversal stableUniversal hypothesisMatrix
    let left := star14_saturatedUniversal stableUniversal leftMatrix
    let right := star14_saturatedUniversal stableUniversal rightMatrix
    Derivation (.assertion
      (implication stableNegation stableDisjunction hypothesis
        (star_4_01 stableNegation stableDisjunction left right))) := by
  let identityOrder := bindOrder order (.function [sort] order 0)
  let stability := star14_identityOrderStable order sort
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) stability.symm) identityUniversal
  let stableNegation := Eq.mp
    (congrArg signature.Negation stability.symm) identityNegation
  let stableDisjunction := Eq.mp
    (congrArg signature.Disjunction stability.symm) identityDisjunction
  let x : Term signature real [sort] sort := .apparent .zero
  let identityB := star_13_01 vocabulary x b.weaken
  let identityC := star_13_01 vocabulary x c.weaken
  let stableCondition := Eq.mp (congrArg
    (Formula signature real [sort]) stability.symm) condition
  let stableIdentityB := Eq.mp (congrArg
    (Formula signature real [sort]) stability.symm) identityB
  let stableIdentityC := Eq.mp (congrArg
    (Formula signature real [sort]) stability.symm) identityC
  let hypothesisMatrix := equivalence stableNegation stableDisjunction
    stableCondition stableIdentityB
  let leftMatrix := equivalence stableNegation stableDisjunction
    stableCondition stableIdentityC
  let rightMatrix := equivalence stableNegation stableDisjunction
    stableIdentityB stableIdentityC
  let transportedMatrix := equivalence stableNegation stableDisjunction
    leftMatrix rightMatrix
  let value : Term signature (sort :: real) [] sort := .real .zero
  have line1Raw := star_4_86 stableNegation stableDisjunction
    (stableCondition.weakenReal.instantiate value)
    (stableIdentityB.weakenReal.instantiate value)
    (stableIdentityC.weakenReal.instantiate value)
  have hypothesisAt : hypothesisMatrix.weakenReal.instantiate value =
      star_4_01 stableNegation stableDisjunction
        (stableCondition.weakenReal.instantiate value)
        (stableIdentityB.weakenReal.instantiate value) := by
    unfold hypothesisMatrix
    rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
      star14_matrixEquivalence_substitute]
    rfl
  have leftAt : leftMatrix.weakenReal.instantiate value =
      star_4_01 stableNegation stableDisjunction
        (stableCondition.weakenReal.instantiate value)
        (stableIdentityC.weakenReal.instantiate value) := by
    unfold leftMatrix
    rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
      star14_matrixEquivalence_substitute]
    rfl
  have rightAt : rightMatrix.weakenReal.instantiate value =
      star_4_01 stableNegation stableDisjunction
        (stableIdentityB.weakenReal.instantiate value)
        (stableIdentityC.weakenReal.instantiate value) := by
    unfold rightMatrix
    rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
      star14_matrixEquivalence_substitute]
    rfl
  have transportedAt : transportedMatrix.weakenReal.instantiate value =
      star_4_01 stableNegation stableDisjunction
        (leftMatrix.weakenReal.instantiate value)
        (rightMatrix.weakenReal.instantiate value) := by
    unfold transportedMatrix
    rw [star14_matrixEquivalence_weakenReal, Formula.instantiate,
      star14_matrixEquivalence_substitute]
    rfl
  have line1Normalization :
      implication stableNegation stableDisjunction
        (hypothesisMatrix.weakenReal.instantiate value)
        (star_4_01 stableNegation stableDisjunction
          (leftMatrix.weakenReal.instantiate value)
          (rightMatrix.weakenReal.instantiate value)) =
      implication stableNegation stableDisjunction
        (star_4_01 stableNegation stableDisjunction
          (stableCondition.weakenReal.instantiate value)
          (stableIdentityB.weakenReal.instantiate value))
        (star_4_01 stableNegation stableDisjunction
          (star_4_01 stableNegation stableDisjunction
            (stableCondition.weakenReal.instantiate value)
            (stableIdentityC.weakenReal.instantiate value))
          (star_4_01 stableNegation stableDisjunction
            (stableIdentityB.weakenReal.instantiate value)
            (stableIdentityC.weakenReal.instantiate value))) := by
    rw [hypothesisAt, leftAt, rightAt]
  have line1Normalized := Derivation.castAssertion line1Normalization line1Raw
  have pointwiseEquality :
      (implication stableNegation stableDisjunction hypothesisMatrix
        transportedMatrix).weakenReal.instantiate value =
      implication stableNegation stableDisjunction
        (hypothesisMatrix.weakenReal.instantiate value)
        (star_4_01 stableNegation stableDisjunction
          (leftMatrix.weakenReal.instantiate value)
          (rightMatrix.weakenReal.instantiate value)) := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    change implication stableNegation stableDisjunction
      (hypothesisMatrix.weakenReal.instantiate value)
      (transportedMatrix.weakenReal.instantiate value) = _
    rw [transportedAt]
  have line1 := Derivation.castAssertion pointwiseEquality line1Normalized
  have line2 := star_10_11 stableUniversal
    (implication stableNegation stableDisjunction hypothesisMatrix
      transportedMatrix) line1
  unfold star_10_11_reading at line2
  have line2Cast := star14_castAssertionOrder
    (star14_bindOrderStable identityOrder sort)
    (.always stableUniversal
      (implication stableNegation stableDisjunction hypothesisMatrix
        transportedMatrix)) line2
  have line3 := star_10_27_saturated (baseOrder := identityOrder)
    stableUniversal stableNegation stableDisjunction
    hypothesisMatrix transportedMatrix
  unfold star_10_27_saturated_reading star_10_27_saturated_left
    star_10_27_saturated_right at line3
  have line4 := Derivation.star_9_12_same stableNegation
    stableDisjunction line2Cast line3
  have equivalenceLift := star_10_271 (baseOrder := identityOrder)
    stableUniversal stableNegation stableDisjunction leftMatrix rightMatrix
  unfold star_10_271_reading star_10_271_left star_10_271_right at equivalenceLift
  have line5 := star14_composeSame stableNegation stableDisjunction
    (star14_saturatedUniversal stableUniversal hypothesisMatrix)
    (star14_saturatedUniversal stableUniversal transportedMatrix)
    (star_4_01 stableNegation stableDisjunction
      (star14_saturatedUniversal stableUniversal leftMatrix)
      (star14_saturatedUniversal stableUniversal rightMatrix))
    line4 equivalenceLift
  exact line5

/-- ✱4·36 at the two assigned orders occurring in a description body. -/
private theorem star14_mixedConjunctionEquivalentRight
    (leftNegation : signature.Negation leftOrder)
    (leftDisjunction : signature.Disjunction leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (rightDisjunction : signature.Disjunction rightOrder)
    (bothNegation : signature.Negation (max leftOrder rightOrder))
    (bothDisjunction : signature.Disjunction (max leftOrder rightOrder))
    (p q : Formula signature real [] leftOrder)
    (r : Formula signature real [] rightOrder) :
    let pqEquality := natMaxSelf leftOrder
    let pqrEquality := MixedOrder.maxLeftAbsorb leftOrder rightOrder
    let negation : MixedOrder.TernaryNegations signature := {
      pOrder := leftOrder
      qOrder := leftOrder
      rOrder := rightOrder
      p := leftNegation
      q := leftNegation
      r := rightNegation
      pq := Eq.mp (congrArg signature.Negation pqEquality.symm) leftNegation
      pr := bothNegation
      qr := bothNegation
      pqr := Eq.mp (congrArg signature.Negation pqrEquality.symm) bothNegation
    }
    let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
      p := leftDisjunction
      q := leftDisjunction
      r := rightDisjunction
      pq := Eq.mp (congrArg signature.Disjunction pqEquality.symm)
        leftDisjunction
      pr := bothDisjunction
      qr := bothDisjunction
      pqr := Eq.mp (congrArg signature.Disjunction pqrEquality.symm)
        bothDisjunction
    }
    Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        ((MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ) ⊃ₚ
          ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR) ≡ₚ
            (MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR))))) := by
  let pqEquality := natMaxSelf leftOrder
  let pqrEquality := MixedOrder.maxLeftAbsorb leftOrder rightOrder
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := leftOrder
    qOrder := leftOrder
    rOrder := rightOrder
    p := leftNegation
    q := leftNegation
    r := rightNegation
    pq := Eq.mp (congrArg signature.Negation pqEquality.symm) leftNegation
    pr := bothNegation
    qr := bothNegation
    pqr := Eq.mp (congrArg signature.Negation pqrEquality.symm) bothNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := leftDisjunction
    q := leftDisjunction
    r := rightDisjunction
    pq := Eq.mp (congrArg signature.Disjunction pqEquality.symm)
      leftDisjunction
    pr := bothDisjunction
    qr := bothDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction pqrEquality.symm)
      bothDisjunction
  }
  have line1 := MixedOrder.ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star4.star_4_36
      MixedOrder.ternaryP MixedOrder.ternaryQ MixedOrder.ternaryR)
  exact line1

private theorem star14_mixedConjunctionEquivalentRightDirect
    (leftNegation : signature.Negation leftOrder)
    (leftDisjunction : signature.Disjunction leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (rightDisjunction : signature.Disjunction rightOrder)
    (bothNegation : signature.Negation (max leftOrder rightOrder))
    (bothDisjunction : signature.Disjunction (max leftOrder rightOrder))
    (p q : Formula signature real [] leftOrder)
    (r : Formula signature real [] rightOrder) :
    let outerEquality := MixedOrder.maxLeftAbsorb leftOrder rightOrder
    let outerDisjunction := Eq.mp (congrArg signature.Disjunction
      outerEquality.symm) bothDisjunction
    Derivation (.assertion
      (mixedImplication leftNegation outerDisjunction
        (star_4_01 leftNegation leftDisjunction p q)
        (star_4_01 bothNegation bothDisjunction
          (mixedConjunction leftNegation rightNegation bothNegation
            bothDisjunction p r)
          (mixedConjunction leftNegation rightNegation bothNegation
            bothDisjunction q r)))) := by
  let outerEquality := MixedOrder.maxLeftAbsorb leftOrder rightOrder
  let outerDisjunction := Eq.mp (congrArg signature.Disjunction
    outerEquality.symm) bothDisjunction
  have line1 := star14_mixedConjunctionEquivalentRight leftNegation
    leftDisjunction rightNegation rightDisjunction bothNegation
    bothDisjunction p q r
  let pqEquality := natMaxSelf leftOrder
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := leftOrder
    qOrder := leftOrder
    rOrder := rightOrder
    p := leftNegation
    q := leftNegation
    r := rightNegation
    pq := Eq.mp (congrArg signature.Negation pqEquality.symm) leftNegation
    pr := bothNegation
    qr := bothNegation
    pqr := Eq.mp (congrArg signature.Negation outerEquality.symm) bothNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := leftDisjunction
    q := leftDisjunction
    r := rightDisjunction
    pq := Eq.mp (congrArg signature.Disjunction pqEquality.symm)
      leftDisjunction
    pr := bothDisjunction
    qr := bothDisjunction
    pqr := outerDisjunction
  }
  let source := MixedOrder.ternaryInterpret negation disjunction p q r
    ((MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ) ⊃ₚ
      ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR) ≡ₚ
        (MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR)))
  change Derivation (.assertion source) at line1
  let antecedent := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ)
  let leftPair := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR)
  let rightPair := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR)
  let consequent := MixedOrder.ternaryInterpret negation disjunction p q r
    ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR) ≡ₚ
      (MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR))
  let antecedentForward := MixedOrder.ternaryInterpret negation disjunction
    p q r (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)
  let antecedentReverse := MixedOrder.ternaryInterpret negation disjunction
    p q r (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP)
  have antecedentShape : antecedent =
      conjunction negation.pq disjunction.pq
        antecedentForward antecedentReverse := by
    rfl
  have antecedentNormalization :
      Eq.mp (congrArg (Formula signature real []) pqEquality) antecedent =
        star_4_01 leftNegation leftDisjunction p q := by
    rw [antecedentShape]
    have line2 := star14_conjunction_castOrder pqEquality
      leftNegation leftDisjunction antecedentForward antecedentReverse
    rw [line2]
    have line3 :
        Eq.mp (congrArg (Formula signature real []) pqEquality)
            antecedentForward =
          implication leftNegation leftDisjunction p q := by
      exact mixedImplication_normalizeSameOrder rfl rfl
        leftNegation leftDisjunction p q
    have line4 :
        Eq.mp (congrArg (Formula signature real []) pqEquality)
            antecedentReverse =
          implication leftNegation leftDisjunction q p := by
      exact mixedImplication_normalizeSameOrder rfl rfl
        leftNegation leftDisjunction q p
    unfold star_4_01
    rw [line3, line4]
  have leftPairShape : leftPair =
      mixedConjunction leftNegation rightNegation bothNegation
        bothDisjunction p r := by
    rfl
  have rightPairShape : rightPair =
      mixedConjunction leftNegation rightNegation bothNegation
        bothDisjunction q r := by
    rfl
  let consequentForward := MixedOrder.ternaryInterpret negation disjunction
    p q r
    ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR) ⊃ₚ
      (MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR))
  let consequentReverse := MixedOrder.ternaryInterpret negation disjunction
    p q r
    ((MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR) ⊃ₚ
      (MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR))
  have consequentShape : consequent =
      conjunction negation.pqr disjunction.pqr
        consequentForward consequentReverse := by
    rfl
  have consequentForwardNormalization :
      Eq.mp (congrArg (Formula signature real []) outerEquality)
          consequentForward =
        implication bothNegation bothDisjunction leftPair rightPair := by
    change Eq.mp (congrArg (Formula signature real []) outerEquality)
        (MixedOrder.normalizedDisjunction
          (MixedOrder.ternaryOrderCombine negation .pr .qr)
          disjunction.pqr (.neg negation.pr leftPair) rightPair) = _
    exact star14_normalizedImplication_castOrder rfl rfl outerEquality
      (MixedOrder.ternaryOrderCombine negation .pr .qr)
      bothNegation bothDisjunction leftPair rightPair
  have consequentReverseNormalization :
      Eq.mp (congrArg (Formula signature real []) outerEquality)
          consequentReverse =
        implication bothNegation bothDisjunction rightPair leftPair := by
    change Eq.mp (congrArg (Formula signature real []) outerEquality)
        (MixedOrder.normalizedDisjunction
          (MixedOrder.ternaryOrderCombine negation .qr .pr)
          disjunction.pqr (.neg negation.qr rightPair) leftPair) = _
    exact star14_normalizedImplication_castOrder rfl rfl outerEquality
      (MixedOrder.ternaryOrderCombine negation .qr .pr)
      bothNegation bothDisjunction rightPair leftPair
  have consequentNormalization :
      Eq.mp (congrArg (Formula signature real []) outerEquality) consequent =
        star_4_01 bothNegation bothDisjunction leftPair rightPair := by
    rw [consequentShape]
    have line5 := star14_conjunction_castOrder outerEquality
      bothNegation bothDisjunction consequentForward consequentReverse
    rw [line5]
    unfold star_4_01
    rw [consequentForwardNormalization, consequentReverseNormalization]
  have sourceShape : source = MixedOrder.normalizedDisjunction
      (MixedOrder.ternaryOrderCombine negation .pq .pqr)
      disjunction.pqr (.neg negation.pq antecedent) consequent := by
    rfl
  have sourceNormalization : source =
      mixedImplication leftNegation outerDisjunction
        (star_4_01 leftNegation leftDisjunction p q)
        (star_4_01 bothNegation bothDisjunction
          (mixedConjunction leftNegation rightNegation bothNegation
            bothDisjunction p r)
          (mixedConjunction leftNegation rightNegation bothNegation
            bothDisjunction q r)) := by
    rw [sourceShape]
    have line6 := star14_normalizedMixedImplication_cast pqEquality
      outerEquality rfl
      (MixedOrder.ternaryOrderCombine negation .pq .pqr)
      leftNegation outerDisjunction antecedent consequent
    change Eq.mp (congrArg (Formula signature real []) rfl)
        (MixedOrder.normalizedDisjunction
          (MixedOrder.ternaryOrderCombine negation .pq .pqr)
          (Eq.mp (congrArg signature.Disjunction rfl.symm)
            outerDisjunction)
          (.neg
            (Eq.mp (congrArg signature.Negation pqEquality.symm)
              leftNegation)
            antecedent)
          consequent) = _
    have line7 : mixedImplication leftNegation outerDisjunction
        (Eq.mp (congrArg (Formula signature real []) pqEquality) antecedent)
        (Eq.mp (congrArg (Formula signature real []) outerEquality)
          consequent) =
        mixedImplication leftNegation outerDisjunction
          (star_4_01 leftNegation leftDisjunction p q)
          (star_4_01 bothNegation bothDisjunction
            (mixedConjunction leftNegation rightNegation bothNegation
              bothDisjunction p r)
            (mixedConjunction leftNegation rightNegation bothNegation
              bothDisjunction q r)) := by
      rw [antecedentNormalization, consequentNormalization,
        leftPairShape, rightPairShape]
    exact Eq.trans line6 line7
  rw [sourceNormalization] at line1
  exact line1

private theorem star14_applyMixedConjunctionEquivalentRight
    (leftNegation : signature.Negation leftOrder)
    (leftDisjunction : signature.Disjunction leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (rightDisjunction : signature.Disjunction rightOrder)
    (bothNegation : signature.Negation (max leftOrder rightOrder))
    (bothDisjunction : signature.Disjunction (max leftOrder rightOrder))
    (p q : Formula signature real [] leftOrder)
    (r : Formula signature real [] rightOrder)
    (line1 : Derivation (.assertion
      (star_4_01 leftNegation leftDisjunction p q))) :
    let pqEquality := natMaxSelf leftOrder
    let pqrEquality := MixedOrder.maxLeftAbsorb leftOrder rightOrder
    let negation : MixedOrder.TernaryNegations signature := {
      pOrder := leftOrder
      qOrder := leftOrder
      rOrder := rightOrder
      p := leftNegation
      q := leftNegation
      r := rightNegation
      pq := Eq.mp (congrArg signature.Negation pqEquality.symm) leftNegation
      pr := bothNegation
      qr := bothNegation
      pqr := Eq.mp (congrArg signature.Negation pqrEquality.symm) bothNegation
    }
    let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
      p := leftDisjunction
      q := leftDisjunction
      r := rightDisjunction
      pq := Eq.mp (congrArg signature.Disjunction pqEquality.symm)
        leftDisjunction
      pr := bothDisjunction
      qr := bothDisjunction
      pqr := Eq.mp (congrArg signature.Disjunction pqrEquality.symm)
        bothDisjunction
    }
    Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR) ≡ₚ
          (MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR)))) := by
  let pqEquality := natMaxSelf leftOrder
  let pqrEquality := MixedOrder.maxLeftAbsorb leftOrder rightOrder
  let negation : MixedOrder.TernaryNegations signature := {
    pOrder := leftOrder
    qOrder := leftOrder
    rOrder := rightOrder
    p := leftNegation
    q := leftNegation
    r := rightNegation
    pq := Eq.mp (congrArg signature.Negation pqEquality.symm) leftNegation
    pr := bothNegation
    qr := bothNegation
    pqr := Eq.mp (congrArg signature.Negation pqrEquality.symm) bothNegation
  }
  let disjunction : MixedOrder.TernaryDisjunctions signature negation := {
    p := leftDisjunction
    q := leftDisjunction
    r := rightDisjunction
    pq := Eq.mp (congrArg signature.Disjunction pqEquality.symm)
      leftDisjunction
    pr := bothDisjunction
    qr := bothDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction pqrEquality.symm)
      bothDisjunction
  }
  let antecedent := MixedOrder.ternaryInterpret negation disjunction p q r
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ)
  let consequent := MixedOrder.ternaryInterpret negation disjunction p q r
    ((MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR) ≡ₚ
      (MixedOrder.ternaryQ ∧ₚ MixedOrder.ternaryR))
  let forward := implication leftNegation leftDisjunction p q
  let reverse := implication leftNegation leftDisjunction q p
  have line2a := Derivation.star_9_12_same leftNegation leftDisjunction line1
    (star_3_26 leftNegation leftDisjunction forward reverse)
  have line2b := Derivation.star_9_12_same leftNegation leftDisjunction line1
    (star_3_27 leftNegation leftDisjunction forward reverse)
  let rawForward := mixedImplication leftNegation disjunction.pq p q
  let rawReverse := mixedImplication leftNegation disjunction.pq q p
  have antecedentShape : antecedent =
      conjunction negation.pq disjunction.pq rawForward rawReverse := by
    change conjunction negation.pq disjunction.pq
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP)) = _
    have forwardShape :
        MixedOrder.ternaryInterpret negation disjunction p q r
          (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ) = rawForward := by
      rfl
    have reverseShape :
        MixedOrder.ternaryInterpret negation disjunction p q r
          (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP) = rawReverse := by
      rfl
    rw [forwardShape, reverseShape]
  have antecedentNormalization :
      Eq.mp (congrArg (Formula signature real []) pqEquality) antecedent =
        star_4_01 leftNegation leftDisjunction p q := by
    rw [antecedentShape]
    have castEquivalence := star14_conjunction_castOrder pqEquality
      leftNegation leftDisjunction rawForward rawReverse
    rw [castEquivalence]
    have forwardEquality :
        Eq.mp (congrArg (Formula signature real []) pqEquality) rawForward =
          implication leftNegation leftDisjunction p q := by
      exact mixedImplication_normalizeSameOrder rfl rfl
        leftNegation leftDisjunction p q
    have reverseEquality :
        Eq.mp (congrArg (Formula signature real []) pqEquality) rawReverse =
          implication leftNegation leftDisjunction q p := by
      exact mixedImplication_normalizeSameOrder rfl rfl
        leftNegation leftDisjunction q p
    unfold star_4_01
    rw [forwardEquality, reverseEquality]
  have forwardNormalization :
      Eq.mp (congrArg (Formula signature real []) pqEquality) rawForward =
        forward := by
    exact mixedImplication_normalizeSameOrder rfl rfl
      leftNegation leftDisjunction p q
  have line2aCast := Derivation.castAssertion forwardNormalization line2a
  have line2aRaw := star14_uncastAssertionOrder pqEquality rawForward line2aCast
  have line2a' : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))) := by
    have interpretationEquality :
        MixedOrder.ternaryInterpret negation disjunction p q r
          (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ) = rawForward := by
      rfl
    exact Derivation.castAssertion interpretationEquality.symm line2aRaw
  have reverseNormalization :
      Eq.mp (congrArg (Formula signature real []) pqEquality) rawReverse =
        reverse := by
    exact mixedImplication_normalizeSameOrder rfl rfl
      leftNegation leftDisjunction q p
  have line2bCast := Derivation.castAssertion reverseNormalization line2b
  have line2bRaw := star14_uncastAssertionOrder pqEquality rawReverse line2bCast
  have line2b' : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP))) := by
    have interpretationEquality :
        MixedOrder.ternaryInterpret negation disjunction p q r
          (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP) = rawReverse := by
      rfl
    exact Derivation.castAssertion interpretationEquality.symm line2bRaw
  have line2c := MixedOrder.ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star3.star_3_2
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)
      (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP))
  have line2d := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pq)
    negation.pq disjunction.pq
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))
    (MixedOrder.ternaryInterpret negation disjunction p q r
      ((MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP) ⊃ₚ
        (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ))) line2a' line2c
  have line2 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pq)
    negation.pq disjunction.pq
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP)) antecedent
    line2b' line2d
  have line3 := star14_mixedConjunctionEquivalentRight leftNegation
    leftDisjunction rightNegation rightDisjunction bothNegation
    bothDisjunction p q r
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pqr)
    negation.pq disjunction.pqr antecedent consequent line2 line3

private theorem star14_ternaryPairP_normalize
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder) :
    MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ∧ₚ MixedOrder.ternaryR) =
    MixedOrder.binaryInterpret {
      leftOrder := negation.pOrder
      rightOrder := negation.rOrder
      left := negation.p
      right := negation.r
      both := negation.pr
    } {
      left := disjunction.p
      right := disjunction.r
      both := disjunction.pr
    } p r (MixedOrder.binaryP ∧ₚ MixedOrder.binaryQ) := by
  rfl

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

private def star14_normalizedDisjunction
    (equality : max leftOrder rightOrder = targetOrder)
    (disjunction : signature.Disjunction targetOrder)
    (left : Formula signature real [] leftOrder)
    (right : Formula signature real [] rightOrder) :
    Formula signature real [] targetOrder :=
  Eq.mp (congrArg (Formula signature real []) equality)
    (.disj (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
      left right)

private theorem star14_normalizedDisjunction_weakenReal
    (equality : max leftOrder rightOrder = targetOrder)
    (disjunction : signature.Disjunction targetOrder)
    (left : Formula signature real [] leftOrder)
    (right : Formula signature real [] rightOrder) :
    (star14_normalizedDisjunction equality disjunction left right).weakenReal
        (fresh := fresh) =
      star14_normalizedDisjunction
        (signature := signature) (real := fresh :: real)
        (leftOrder := leftOrder) (rightOrder := rightOrder)
        (targetOrder := targetOrder) equality disjunction
        left.weakenReal right.weakenReal := by
  unfold star14_normalizedDisjunction
  exact Formula.weakenReal_cast (fresh := fresh) equality
    (.disj (Eq.mp (congrArg signature.Disjunction equality.symm)
      disjunction) left right)

private theorem star14_10_23_right_weakenReal
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    (star_10_23_right existential matrixUniversal scopeUniversal negation
      disjunction phi p).weakenReal (fresh := fresh) =
    star_10_23_right existential matrixUniversal scopeUniversal negation
      disjunction phi.weakenReal p.weakenReal := by
  change (Formula.always scopeUniversal
    (.disj disjunction (.neg negation phi)
      (p.rename (fun v => .succ v)))).weakenReal =
    Formula.always scopeUniversal
      (.disj disjunction (.neg negation phi.weakenReal)
        (p.weakenReal.rename (fun v => .succ v)))
  change Formula.always scopeUniversal
    (.disj disjunction (.neg negation phi.weakenReal)
      ((p.rename (fun v => .succ v)).weakenReal)) = _
  rw [Formula.weakenReal_rename]

private theorem star14_applicationOrderStable
    (conditionOrder : Nat) (sort : RSort) :
    max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort) conditionOrder =
      bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort := by
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  have conditionLeIdentity : conditionOrder ≤ identityOrder := by
    unfold identityOrder bindOrder
    exact star14_le_max_left _ _
  have identityLeUniqueness : identityOrder ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_left _ _
  exact star14_max_eq_left_of_le
    (Nat.le_trans conditionLeIdentity identityLeUniqueness)

private theorem star14_bindOrder_eq_of_le
    (height : Nat.succ sort.height ≤ order) : bindOrder order sort = order := by
  unfold bindOrder
  exact star14_max_eq_left_of_le height

private theorem star14_descriptionBindOrderStable
    (conditionOrder : Nat) (sort : RSort) :
    bindOrder
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))) sort =
      max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0)) := by
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let continuationOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionBodyOrder := max uniquenessOrder continuationOrder
  have uniquenessHeight : Nat.succ sort.height ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_right _ _
  have descriptionHeight : Nat.succ sort.height ≤ descriptionBodyOrder :=
    Nat.le_trans uniquenessHeight (star14_le_max_left _ _)
  exact star14_bindOrder_eq_of_le descriptionHeight

structure Star14_15LogicalVocabulary (signature : Signature) (sort : RSort)
    (conditionOrder : Nat) where
  descriptionExistential : ExistentialVocabulary signature sort
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
  descriptionBodyNegation : signature.Negation
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
  descriptionBodyDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
  applicationExistential : ExistentialVocabulary signature sort
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort) conditionOrder)
  applicationBodyDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort) conditionOrder)
  applicationResultDisjunction : signature.Disjunction
    (bindOrder (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort) conditionOrder) sort)
  finalDisjunction : signature.Disjunction
    (max
      (bindOrder
        (max (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))) sort)
      (bindOrder (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder) sort))

def star_14_15_logicalVocabulary
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityDisjunction : signature.Disjunction
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (descriptionPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (applicationPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)) :
    Star14_15LogicalVocabulary signature sort conditionOrder := by
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let continuationOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionOrder := max uniquenessOrder continuationOrder
  let applicationOrder := max uniquenessOrder conditionOrder
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let uniquenessDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) identityDisjunction
  let applicationStability := star14_applicationOrderStable conditionOrder sort
  let applicationResultStability := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      applicationStability)
    (star14_bindOrderStable identityOrder sort)
  let applicationNegation := Eq.mp (congrArg signature.Negation
    applicationStability.symm) uniquenessNegation
  let applicationDisjunction := Eq.mp (congrArg signature.Disjunction
    applicationStability.symm) uniquenessDisjunction
  let applicationScopeUniversal := Eq.mp
    (congrArg (signature.Universal sort) applicationStability.symm)
    (Eq.mp (congrArg (signature.Universal sort) identityStability.symm)
      identityUniversal)
  let applicationOuterNegation := Eq.mp (congrArg signature.Negation
    applicationResultStability.symm) uniquenessNegation
  let applicationResultDisjunction := Eq.mp
    (congrArg signature.Disjunction applicationResultStability.symm)
    uniquenessDisjunction
  let applicationExistential : ExistentialVocabulary signature sort
      applicationOrder := {
    printed := applicationPrinted
    matrixNegation := applicationNegation
    universal := applicationScopeUniversal
    outerNegation := applicationOuterNegation
  }
  let uniquenessLeContinuation : uniquenessOrder ≤ continuationOrder := by
    unfold continuationOrder bindOrder
    exact star14_le_max_left _ _
  let descriptionStability : descriptionOrder = continuationOrder :=
    Nat.max_eq_right uniquenessLeContinuation
  let descriptionNegation := Eq.mp (congrArg signature.Negation
    descriptionStability.symm) continuationIdentityNegation
  let descriptionDisjunction := Eq.mp (congrArg signature.Disjunction
    descriptionStability.symm) continuationIdentityDisjunction
  let uniquenessHeight : Nat.succ sort.height ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_right _ _
  let descriptionHeight : Nat.succ sort.height ≤ descriptionOrder :=
    Nat.le_trans uniquenessHeight (star14_le_max_left _ _)
  let descriptionResultStability :=
    star14_bindOrder_eq_of_le descriptionHeight
  let descriptionOuterNegation := Eq.mp (congrArg signature.Negation
    descriptionResultStability.symm) descriptionNegation
  let descriptionExistential : ExistentialVocabulary signature sort
      descriptionOrder := {
    printed := descriptionPrinted
    matrixNegation := descriptionNegation
    universal := descriptionUniversal
    outerNegation := descriptionOuterNegation
  }
  let uniquenessLeDescription : uniquenessOrder ≤ descriptionOrder :=
    star14_le_max_left _ _
  let finalStability :
      max (bindOrder descriptionOrder sort)
          (bindOrder applicationOrder sort) = descriptionOrder :=
    Eq.trans
      (congrArg (fun leftOrder =>
        max leftOrder (bindOrder applicationOrder sort))
        descriptionResultStability)
      (Eq.trans
        (congrArg (max descriptionOrder) applicationResultStability)
        (star14_max_eq_left_of_le uniquenessLeDescription))
  exact {
    descriptionExistential := descriptionExistential
    descriptionBodyNegation := descriptionNegation
    descriptionBodyDisjunction := descriptionDisjunction
    applicationExistential := applicationExistential
    applicationBodyDisjunction := applicationDisjunction
    applicationResultDisjunction := applicationResultDisjunction
    finalDisjunction := Eq.mp (congrArg signature.Disjunction
      finalStability.symm) descriptionDisjunction
  }

/-- Primitive contextual AST of ✱14·15.  Both description occurrences are
the ✱14·01 existential expansion; neither is a description-valued term. -/
def star_14_15_formula
    (descriptionExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentity : IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (descriptionBodyNegation : signature.Negation
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (applicationExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (applicationResultDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder) sort))
    (finalDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (bindOrder (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort)
              (.function [sort]
                (bindOrder (bindOrder conditionOrder
                  (.function [sort] conditionOrder 0)) sort) 0))) sort)
        (bindOrder (max (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) conditionOrder) sort)))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort) :=
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let continuationIdentityOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionBodyOrder := max uniquenessOrder continuationIdentityOrder
  let descriptionIdentity := star_14_descriptionIdentity
    descriptionExistential identityUniversal conditionIdentity identityNegation
    identityDisjunction uniquenessNegation continuationIdentity
    continuationIdentityNegation descriptionBodyNegation
    descriptionBodyDisjunction condition b
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let candidate : Term signature real [sort, sort] sort :=
    .apparent (.succ .zero)
  let conditionUnderCandidate : Formula signature real [sort, sort]
      identityOrder := condition.rename
    (liftRenaming (fun v => .succ v))
  let uniquenessMatrix := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction conditionUnderCandidate
      (star_13_01 conditionIdentity x candidate))
  let applicationOrder := max uniquenessOrder conditionOrder
  let applicationStability := star14_applicationOrderStable conditionOrder sort
  let applicationBodyNegation := Eq.mp (congrArg signature.Negation
    applicationStability.symm) uniquenessNegation
  let applicationBody := mixedConjunction uniquenessNegation
    conditionIdentity.negation applicationBodyNegation
    applicationBodyDisjunction uniquenessMatrix psi
  let psiDescription := Formula.sometimes applicationExistential applicationBody
  let psiB := psi.instantiate b
  let applicationPsiEquality := MixedOrder.maxRightAbsorb
    uniquenessOrder conditionOrder
  let applicationPsiDisjunction := Eq.mp (congrArg signature.Disjunction
    applicationPsiEquality.symm) applicationBodyDisjunction
  let forwardEquality := congrArg (fun matrixOrder => bindOrder matrixOrder sort)
    applicationPsiEquality
  let forward := Eq.mp (congrArg (Formula signature real []) forwardEquality)
    (star_10_23_right applicationExistential applicationExistential.universal
      applicationImplicationUniversal applicationBodyNegation
      applicationPsiDisjunction applicationBody psiB)
  let reverseEquality := Eq.trans
    (bindOrderMaxLeft conditionOrder applicationOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder))
  let reverse := star14_normalizedDisjunction reverseEquality
    applicationResultDisjunction (.neg conditionIdentity.negation psiB)
    psiDescription
  let conclusion := conjunction applicationExistential.outerNegation
    applicationResultDisjunction forward reverse
  mixedImplication descriptionExistential.outerNegation finalDisjunction
    descriptionIdentity conclusion

/-- Audited scope reading of ✱14·15. -/
def star_14_15_reading
    (descriptionExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentity : IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (descriptionBodyNegation : signature.Negation
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (applicationExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (applicationResultDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder) sort))
    (finalDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (bindOrder (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort)
              (.function [sort]
                (bindOrder (bindOrder conditionOrder
                  (.function [sort] conditionOrder 0)) sort) 0))) sort)
        (bindOrder (max (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) conditionOrder) sort)))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : (℩x)(φx) = b .⊃ : ψ{(℩x)(φx)} .≡ . ψb"
  parsed := .assertion (star_14_15_formula descriptionExistential
    identityUniversal conditionIdentity identityNegation identityDisjunction
    continuationIdentity continuationIdentityNegation
    descriptionBodyNegation descriptionBodyDisjunction applicationExistential
    applicationBodyDisjunction applicationImplicationUniversal
    applicationResultDisjunction finalDisjunction condition psi b)

/-- Contextual AST of ✱14·242.  The right member is the complete
description scope from ✱14·01, and the displayed equivalence is oriented
exactly as `ψb ≡ ψ(ℙx)(φx)`. -/
def star_14_242_formula
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (applicationExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (applicationResultDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder) sort))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort) :=
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let uniquenessDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) identityDisjunction
  let applicationOrder := max uniquenessOrder conditionOrder
  let applicationStability := star14_applicationOrderStable conditionOrder sort
  let applicationResultStability := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      applicationStability)
    (star14_bindOrderStable identityOrder sort)
  let applicationBodyNegation := Eq.mp (congrArg signature.Negation
    applicationStability.symm) uniquenessNegation
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let candidate : Term signature real [sort, sort] sort :=
    .apparent (.succ .zero)
  let conditionUnderCandidate : Formula signature real [sort, sort]
      identityOrder := condition.rename
    (liftRenaming (fun v => .succ v))
  let uniquenessMatrix := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction conditionUnderCandidate
      (star_13_01 conditionIdentity x candidate))
  let applicationBody := mixedConjunction uniquenessNegation
    conditionIdentity.negation applicationBodyNegation
    applicationBodyDisjunction uniquenessMatrix psi
  let psiDescription := Formula.sometimes applicationExistential applicationBody
  let psiB := psi.instantiate b
  let applicationPsiEquality := MixedOrder.maxRightAbsorb
    uniquenessOrder conditionOrder
  let applicationPsiDisjunction := Eq.mp (congrArg signature.Disjunction
    applicationPsiEquality.symm) applicationBodyDisjunction
  let forwardEquality := congrArg (fun matrixOrder => bindOrder matrixOrder sort)
    applicationPsiEquality
  let forward := Eq.mp (congrArg (Formula signature real []) forwardEquality)
    (star_10_23_right applicationExistential applicationExistential.universal
      applicationImplicationUniversal applicationBodyNegation
      applicationPsiDisjunction applicationBody psiB)
  let reverseEquality := Eq.trans
    (bindOrderMaxLeft conditionOrder applicationOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder))
  let reverse := star14_normalizedDisjunction reverseEquality
    applicationResultDisjunction (.neg conditionIdentity.negation psiB)
    psiDescription
  let stableForward := Eq.mp (congrArg (Formula signature real [])
    applicationResultStability) forward
  let stableReverse := Eq.mp (congrArg (Formula signature real [])
    applicationResultStability) reverse
  let hypothesisVariable : Term signature real [sort] sort := .apparent .zero
  let hypothesis := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction condition
      (star_13_01 conditionIdentity hypothesisVariable b.weaken))
  implication uniquenessNegation uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction
      stableReverse stableForward)

/-- Audited scope reading of ✱14·242. -/
def star_14_242_reading
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (applicationExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (applicationResultDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder) sort))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : φx .≡ₓ. x = b : ⊃ : ψb .≡ . ψ(ℙx)(φx)  [✱14·202·15]"
  parsed := .assertion (star_14_242_formula identityUniversal
    conditionIdentity identityNegation identityDisjunction
    applicationExistential applicationBodyDisjunction
    applicationImplicationUniversal applicationResultDisjunction
    condition psi b)

/-- First adjacent equivalence of ✱14·202, with the two ramified orders
retained in the implication factors and normalized at the description order. -/
def star_14_202_first_formula
    (descriptionExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentity : IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (descriptionBodyNegation : signature.Negation
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (b : Term signature real [] sort) :=
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let continuationOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionBodyOrder := max uniquenessOrder continuationOrder
  let descriptionResultOrder := bindOrder descriptionBodyOrder sort
  let uniquenessLeContinuation : uniquenessOrder ≤ continuationOrder := by
    unfold continuationOrder bindOrder
    exact star14_le_max_left _ _
  let descriptionBodyStability : descriptionBodyOrder = continuationOrder :=
    Nat.max_eq_right uniquenessLeContinuation
  let uniquenessHeight : Nat.succ sort.height ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_right _ _
  let descriptionHeight : Nat.succ sort.height ≤ descriptionBodyOrder :=
    Nat.le_trans uniquenessHeight (star14_le_max_left _ _)
  let descriptionBindStability : descriptionResultOrder =
      descriptionBodyOrder := star14_bindOrder_eq_of_le descriptionHeight
  let resultNegation := Eq.mp (congrArg signature.Negation
    descriptionBindStability.symm) descriptionBodyNegation
  let resultDisjunction := Eq.mp (congrArg signature.Disjunction
    descriptionBindStability.symm) descriptionBodyDisjunction
  let hypothesisVariable : Term signature real [sort] sort := .apparent .zero
  let hypothesisIdentity := star_13_01 conditionIdentity hypothesisVariable
    b.weaken
  let hypothesis := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction condition
      hypothesisIdentity)
  let descriptionIdentity := star_14_descriptionIdentity
    descriptionExistential identityUniversal conditionIdentity
    identityNegation identityDisjunction uniquenessNegation
    continuationIdentity continuationIdentityNegation
    descriptionBodyNegation descriptionBodyDisjunction condition b
  let descriptionUniqueness : uniquenessOrder ≤ descriptionBodyOrder :=
    star14_le_max_left _ _
  let resultUniqueness : uniquenessOrder ≤ descriptionResultOrder := by
    rw [descriptionBindStability]
    exact descriptionUniqueness
  let forwardEquality : max descriptionResultOrder uniquenessOrder =
      descriptionResultOrder := star14_max_eq_left_of_le resultUniqueness
  let reverseEquality : max uniquenessOrder descriptionResultOrder =
      descriptionResultOrder := Nat.max_eq_right resultUniqueness
  let forward := star14_normalizedDisjunction forwardEquality
    resultDisjunction (.neg resultNegation descriptionIdentity) hypothesis
  let reverse := star14_normalizedDisjunction reverseEquality
    resultDisjunction (.neg uniquenessNegation hypothesis) descriptionIdentity
  conjunction resultNegation resultDisjunction reverse forward

/-- Four-member reading of ✱14·202.  The members alternate between the
uniqueness order and the contextual-description order. -/
private def star14_202_chain
    (uniquenessNegation : signature.Negation uniquenessOrder)
    (resultNegation : signature.Negation resultOrder)
    (resultDisjunction : signature.Disjunction resultOrder)
    (resultUniqueness : uniquenessOrder ≤ resultOrder)
    (conditionEquals conditionReverseEquals :
      Formula signature real [] uniquenessOrder)
    (identityDescription reverseIdentityDescription :
      Formula signature real [] resultOrder) :
    Formula signature real [] resultOrder :=
  let highLow : max resultOrder uniquenessOrder = resultOrder :=
    star14_max_eq_left_of_le resultUniqueness
  let lowHigh : max uniquenessOrder resultOrder = resultOrder :=
    Nat.max_eq_right resultUniqueness
  let highToLow (high : Formula signature real [] resultOrder)
      (low : Formula signature real [] uniquenessOrder) :=
    star14_normalizedDisjunction highLow resultDisjunction
      (.neg resultNegation high) low
  let lowToHigh (low : Formula signature real [] uniquenessOrder)
      (high : Formula signature real [] resultOrder) :=
    star14_normalizedDisjunction lowHigh resultDisjunction
      (.neg uniquenessNegation low) high
  let mixedEquivalence
      (low : Formula signature real [] uniquenessOrder)
      (high : Formula signature real [] resultOrder) :=
    conjunction resultNegation resultDisjunction
      (lowToHigh low high) (highToLow high low)
  let first := mixedEquivalence conditionEquals identityDescription
  let second := conjunction resultNegation resultDisjunction
    (highToLow identityDescription conditionReverseEquals)
    (lowToHigh conditionReverseEquals identityDescription)
  let third := mixedEquivalence conditionReverseEquals
    reverseIdentityDescription
  conjunction resultNegation resultDisjunction
    (conjunction resultNegation resultDisjunction first second) third

/-- Literal contextual AST of ✱14·202. -/
def star_14_202_formula
    (descriptionExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentity : IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (descriptionBodyNegation : signature.Negation
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (b : Term signature real [] sort) :=
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let continuationOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionBodyOrder := max uniquenessOrder continuationOrder
  let descriptionResultOrder := bindOrder descriptionBodyOrder sort
  let uniquenessLeContinuation : uniquenessOrder ≤ continuationOrder := by
    unfold continuationOrder bindOrder
    exact star14_le_max_left _ _
  let uniquenessHeight : Nat.succ sort.height ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_right _ _
  let descriptionHeight : Nat.succ sort.height ≤ descriptionBodyOrder :=
    Nat.le_trans uniquenessHeight (star14_le_max_left _ _)
  let descriptionBindStability : descriptionResultOrder =
      descriptionBodyOrder := star14_bindOrder_eq_of_le descriptionHeight
  let resultNegation := Eq.mp (congrArg signature.Negation
    descriptionBindStability.symm) descriptionBodyNegation
  let resultDisjunction := Eq.mp (congrArg signature.Disjunction
    descriptionBindStability.symm) descriptionBodyDisjunction
  let x : Term signature real [sort] sort := .apparent .zero
  let identityToB := star_13_01 conditionIdentity x b.weaken
  let identityFromB := star_13_01 conditionIdentity b.weaken x
  let conditionEquals := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction condition identityToB)
  let conditionReverseEquals := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction condition identityFromB)
  let identityDescription := star_14_descriptionIdentity
    descriptionExistential identityUniversal conditionIdentity
    identityNegation identityDisjunction uniquenessNegation
    continuationIdentity continuationIdentityNegation
    descriptionBodyNegation descriptionBodyDisjunction condition b
  let reverseContinuation := star_13_01 continuationIdentity b.weaken x
  let reverseIdentityDescription := star_14_01 descriptionExistential
    identityUniversal conditionIdentity identityNegation identityDisjunction
    uniquenessNegation continuationIdentityNegation descriptionBodyNegation
    descriptionBodyDisjunction condition reverseContinuation
  let descriptionUniqueness : uniquenessOrder ≤ descriptionBodyOrder :=
    star14_le_max_left _ _
  let resultUniqueness : uniquenessOrder ≤ descriptionResultOrder := by
    rw [descriptionBindStability]
    exact descriptionUniqueness
  star14_202_chain uniquenessNegation resultNegation resultDisjunction
    resultUniqueness conditionEquals conditionReverseEquals
    identityDescription reverseIdentityDescription

/-- Audited scope reading of ✱14·202. -/
def star_14_202_reading
    (descriptionExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentity : IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (descriptionBodyNegation : signature.Negation
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (b : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : φx ≡ₓ x=b : ≡ : (℩x)(φx)=b : ≡ : φx ≡ₓ b=x : ≡ : b=(℩x)(φx)"
  parsed := .assertion (star_14_202_formula descriptionExistential
    identityUniversal conditionIdentity identityNegation identityDisjunction
    continuationIdentity continuationIdentityNegation descriptionBodyNegation
    descriptionBodyDisjunction condition b)

set_option maxHeartbeats 1000000
/-- ✱14·15, following the two printed description expansions and the
substitution theorems ✱13·195 and ✱13·192.
`demonstration_provenance: follows-printed`. -/
private theorem star14_15_core
    (descriptionExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentity : IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityDisjunction : signature.Disjunction
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityBaseNegationCoherence :
      continuationIdentity.negation = Eq.mp
        (congrArg signature.Negation
          (star14_identityOrderStable conditionOrder sort).symm)
        identityNegation)
    (descriptionBodyNegation : signature.Negation
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (continuationImplicationUniversal : signature.Universal sort
      (max
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort))
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)))
    (continuationResultNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (continuationResultDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (applicationExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (applicationResultDisjunction : signature.Disjunction
      (bindOrder (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder) sort))
    (finalDisjunction : signature.Disjunction
      (max
        (bindOrder
          (max (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (bindOrder (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort)
              (.function [sort]
                (bindOrder (bindOrder conditionOrder
                  (.function [sort] conditionOrder 0)) sort) 0))) sort)
        (bindOrder (max (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) conditionOrder) sort)))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort)
    (descriptionPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (applicationPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (descriptionExistentialCoherence : descriptionExistential =
      (star_14_15_logicalVocabulary identityUniversal identityNegation identityDisjunction
        continuationIdentityNegation continuationIdentityDisjunction
        descriptionPrinted descriptionUniversal applicationPrinted
        applicationUniversal).descriptionExistential)
    (descriptionBodyNegationCoherence : descriptionBodyNegation =
      (star_14_15_logicalVocabulary identityUniversal identityNegation identityDisjunction
        continuationIdentityNegation continuationIdentityDisjunction
        descriptionPrinted descriptionUniversal applicationPrinted
        applicationUniversal).descriptionBodyNegation)
    (descriptionBodyDisjunctionCoherence : descriptionBodyDisjunction =
      (star_14_15_logicalVocabulary identityUniversal identityNegation identityDisjunction
        continuationIdentityNegation continuationIdentityDisjunction
        descriptionPrinted descriptionUniversal applicationPrinted
        applicationUniversal).descriptionBodyDisjunction)
    (applicationExistentialCoherence : applicationExistential =
      (star_14_15_logicalVocabulary identityUniversal identityNegation identityDisjunction
        continuationIdentityNegation continuationIdentityDisjunction
        descriptionPrinted descriptionUniversal applicationPrinted
        applicationUniversal).applicationExistential)
    (applicationBodyDisjunctionCoherence : applicationBodyDisjunction =
      (star_14_15_logicalVocabulary identityUniversal identityNegation identityDisjunction
        continuationIdentityNegation continuationIdentityDisjunction
        descriptionPrinted descriptionUniversal applicationPrinted
        applicationUniversal).applicationBodyDisjunction)
    (applicationResultDisjunctionCoherence : applicationResultDisjunction =
      (star_14_15_logicalVocabulary identityUniversal identityNegation identityDisjunction
        continuationIdentityNegation continuationIdentityDisjunction
        descriptionPrinted descriptionUniversal applicationPrinted
        applicationUniversal).applicationResultDisjunction)
    (finalDisjunctionCoherence : finalDisjunction =
      (star_14_15_logicalVocabulary identityUniversal identityNegation identityDisjunction
        continuationIdentityNegation continuationIdentityDisjunction
        descriptionPrinted descriptionUniversal applicationPrinted
        applicationUniversal).finalDisjunction)
    (conditionReducibility : Star14ReducibilityVocabulary signature sort
      conditionOrder)
    (continuationReducibility : Star14ReducibilityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)) :
    Derivation (star_14_15_reading descriptionExistential identityUniversal
        conditionIdentity identityNegation identityDisjunction
        continuationIdentity continuationIdentityNegation
        descriptionBodyNegation descriptionBodyDisjunction
        applicationExistential applicationBodyDisjunction
        applicationImplicationUniversal applicationResultDisjunction
        finalDisjunction condition psi b).parsed ∧
      Derivation (.assertion (star_14_202_first_formula
        descriptionExistential identityUniversal conditionIdentity
        identityNegation identityDisjunction continuationIdentity
        continuationIdentityNegation descriptionBodyNegation
        descriptionBodyDisjunction condition b)) ∧
      Derivation (star_14_242_reading identityUniversal conditionIdentity
        identityNegation identityDisjunction applicationExistential
        applicationBodyDisjunction applicationImplicationUniversal
        applicationResultDisjunction condition psi b).parsed := by
  cases descriptionExistentialCoherence
  cases descriptionBodyNegationCoherence
  cases descriptionBodyDisjunctionCoherence
  cases applicationExistentialCoherence
  cases applicationBodyDisjunctionCoherence
  cases applicationResultDisjunctionCoherence
  cases finalDisjunctionCoherence
  let logicalVocabulary := star_14_15_logicalVocabulary identityUniversal
    identityNegation identityDisjunction continuationIdentityNegation
    continuationIdentityDisjunction descriptionPrinted descriptionUniversal
    applicationPrinted applicationUniversal
  let descriptionExistential := logicalVocabulary.descriptionExistential
  let descriptionBodyNegation := logicalVocabulary.descriptionBodyNegation
  let descriptionBodyDisjunction := logicalVocabulary.descriptionBodyDisjunction
  let applicationExistential := logicalVocabulary.applicationExistential
  let applicationBodyDisjunction :=
    logicalVocabulary.applicationBodyDisjunction
  let applicationResultDisjunction :=
    logicalVocabulary.applicationResultDisjunction
  let finalDisjunction := logicalVocabulary.finalDisjunction
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let uniquenessDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) identityDisjunction
  let applicationStability := star14_applicationOrderStable conditionOrder sort
  let applicationBodyNegation := Eq.mp (congrArg signature.Negation
    applicationStability.symm) uniquenessNegation
  let identityBaseEquality :
      max uniquenessOrder conditionOrder = max identityOrder conditionOrder :=
    congrArg (fun leftOrder => max leftOrder conditionOrder)
      identityStability
  let conditionIdentityBaseNegation := Eq.mp
    (congrArg signature.Negation identityBaseEquality)
    applicationBodyNegation
  let conditionIdentityBaseDisjunction := Eq.mp
    (congrArg signature.Disjunction identityBaseEquality)
    applicationBodyDisjunction
  have line1 := star_13_192 conditionIdentity identityUniversal
    identityNegation identityDisjunction uniquenessNegation
    uniquenessDisjunction applicationBodyNegation applicationBodyDisjunction
    applicationExistential applicationResultDisjunction
    applicationImplicationUniversal applicationExistential.outerNegation
    applicationResultDisjunction psi b
    conditionReducibility.reducibilityExistential
    conditionReducibility.argumentUniversal conditionIdentityBaseDisjunction
    conditionReducibility.reducibilityNegation
    conditionReducibility.reducibilityIdentityNegation
    conditionReducibility.reducibilityBaseNegation conditionIdentityBaseNegation
    conditionReducibility.substitutionResultNegation
    conditionReducibility.reducibilityDisjunction
    conditionReducibility.reducibilityIdentityDisjunction
    conditionReducibility.reducibilityBaseDisjunction
    conditionReducibility.substitutionResultDisjunction
    conditionReducibility.reducibilityScopeUniversal
    conditionReducibility.reducibilityScopeNegation
    conditionReducibility.reducibilityScopeDisjunction
    conditionReducibility.existentialTargetDisjunction
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) identityStability.symm)
    identityUniversal
  let stableNegation := uniquenessNegation
  let stableDisjunction := uniquenessDisjunction
  let stableBind := star14_bindOrderStable identityOrder sort
  let candidate : Term signature (sort :: real) [] sort := .real .zero
  let apparent : Term signature (sort :: real) [sort] sort := .apparent .zero
  let bValue := b.weakenReal (fresh := sort)
  let rawCondition := condition.weakenReal (fresh := sort)
  let rawIdentityB := star_13_01 conditionIdentity apparent bValue.weaken
  let rawIdentityC := star_13_01 conditionIdentity apparent candidate.weaken
  let rawHypothesisMatrix := equivalence identityNegation identityDisjunction
    rawCondition rawIdentityB
  let rawLeftMatrix := equivalence identityNegation identityDisjunction
    rawCondition rawIdentityC
  let rawRightMatrix := equivalence identityNegation identityDisjunction
    rawIdentityB rawIdentityC
  let rawHypothesis := Formula.always identityUniversal rawHypothesisMatrix
  let rawLeft := Formula.always identityUniversal rawLeftMatrix
  let rawRight := Formula.always identityUniversal rawRightMatrix
  have line2 := star14_innerUniquenessTransport conditionIdentity
    identityUniversal identityNegation identityDisjunction
    (condition.weakenReal (fresh := sort)) bValue candidate
  have hypothesisNormalization :
      star14_saturatedUniversal stableUniversal
        (equivalence stableNegation stableDisjunction
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawCondition)
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawIdentityB)) = rawHypothesis := by
    exact star14_saturatedEquivalenceScope_cast identityStability rfl
      stableBind identityUniversal identityNegation identityDisjunction
      rawCondition rawIdentityB
  have leftNormalization :
      star14_saturatedUniversal stableUniversal
        (equivalence stableNegation stableDisjunction
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawCondition)
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawIdentityC)) = rawLeft := by
    exact star14_saturatedEquivalenceScope_cast identityStability rfl
      stableBind identityUniversal identityNegation identityDisjunction
      rawCondition rawIdentityC
  have rightNormalization :
      star14_saturatedUniversal stableUniversal
        (equivalence stableNegation stableDisjunction
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawIdentityB)
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawIdentityC)) = rawRight := by
    exact star14_saturatedEquivalenceScope_cast identityStability rfl
      stableBind identityUniversal identityNegation identityDisjunction
      rawIdentityB rawIdentityC
  change Derivation (.assertion
    (implication stableNegation stableDisjunction
      (star14_saturatedUniversal stableUniversal
        (equivalence stableNegation stableDisjunction
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawCondition)
          (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
            identityStability.symm) rawIdentityB)))
      (star_4_01 stableNegation stableDisjunction
        (star14_saturatedUniversal stableUniversal
          (equivalence stableNegation stableDisjunction
            (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
              identityStability.symm) rawCondition)
            (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
              identityStability.symm) rawIdentityC)))
        (star14_saturatedUniversal stableUniversal
          (equivalence stableNegation stableDisjunction
            (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
              identityStability.symm) rawIdentityB)
            (Eq.mp (congrArg (Formula signature (sort :: real) [sort])
              identityStability.symm) rawIdentityC)))))) at line2
  rw [hypothesisNormalization, leftNormalization, rightNormalization] at line2
  let psiCandidate := psi.weakenReal.instantiate candidate
  have line3 := star14_mixedConjunctionEquivalentRightDirect stableNegation
    stableDisjunction conditionIdentity.negation conditionIdentity.disjunction
    applicationBodyNegation applicationBodyDisjunction
    rawLeft rawRight psiCandidate
  let applicationOrder := max uniquenessOrder conditionOrder
  let outerEquality := MixedOrder.maxLeftAbsorb uniquenessOrder conditionOrder
  let rightDisjunction := Eq.mp (congrArg signature.Disjunction
    outerEquality.symm) applicationBodyDisjunction
  let rightNegation := Eq.mp (congrArg signature.Negation
    outerEquality.symm) applicationBodyNegation
  let rightStability : max uniquenessOrder applicationOrder =
      uniquenessOrder := Eq.trans outerEquality applicationStability
  let sameStability := natMaxSelf uniquenessOrder
  let innerStability :
      max (max uniquenessOrder uniquenessOrder)
        (max uniquenessOrder applicationOrder) = uniquenessOrder :=
    natMaxCongr sameStability rightStability
  let outerStability :
      max (max uniquenessOrder applicationOrder)
        (max (max uniquenessOrder uniquenessOrder)
          (max uniquenessOrder applicationOrder)) = uniquenessOrder :=
    natMaxCongr rightStability innerStability
  let innerDisjunction := Eq.mp (congrArg signature.Disjunction
    innerStability.symm) stableDisjunction
  let outerDisjunction := Eq.mp (congrArg signature.Disjunction
    outerStability.symm) stableDisjunction
  have line4 := star14_mixedSyllSameLeft stableNegation stableDisjunction
    rightDisjunction rightNegation innerDisjunction outerDisjunction
    rawHypothesis
    (star_4_01 stableNegation stableDisjunction rawLeft rawRight)
    (star_4_01 applicationBodyNegation applicationBodyDisjunction
      (mixedConjunction stableNegation conditionIdentity.negation
        applicationBodyNegation applicationBodyDisjunction
        rawLeft psiCandidate)
      (mixedConjunction stableNegation conditionIdentity.negation
        applicationBodyNegation applicationBodyDisjunction
        rawRight psiCandidate)) line2 line3
  let leftBody := mixedConjunction stableNegation conditionIdentity.negation
    applicationBodyNegation applicationBodyDisjunction rawLeft psiCandidate
  let rightBody := mixedConjunction stableNegation conditionIdentity.negation
    applicationBodyNegation applicationBodyDisjunction rawRight psiCandidate
  let rawConsequence := star_4_01 applicationBodyNegation
    applicationBodyDisjunction leftBody rightBody
  let line4Formula := mixedImplication stableNegation rightDisjunction
    rawHypothesis rawConsequence
  have applicationDisjunctionNormalization : applicationBodyDisjunction =
      Eq.mp (congrArg signature.Disjunction applicationStability.symm)
        stableDisjunction := by
    unfold applicationBodyDisjunction logicalVocabulary
      star_14_15_logicalVocabulary stableDisjunction uniquenessDisjunction
    rfl
  have rightDisjunctionNormalization : rightDisjunction =
      Eq.mp (congrArg signature.Disjunction rightStability.symm)
        stableDisjunction := by
    unfold rightDisjunction
    rw [applicationDisjunctionNormalization]
    exact (star14_cast_trans applicationStability.symm outerEquality.symm
      stableDisjunction).symm
  have line4Cast := star14_castAssertionOrder rightStability line4Formula line4
  let stableLeftBody := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationStability) leftBody
  let stableRightBody := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationStability) rightBody
  have consequenceNormalization :
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        applicationStability) rawConsequence =
        star_4_01 stableNegation stableDisjunction
          stableLeftBody stableRightBody := by
    unfold rawConsequence stableLeftBody stableRightBody star_4_01
    exact star14_equivalence_castOrder applicationStability
      stableNegation stableDisjunction leftBody rightBody
  have line4Normalization :
      Eq.mp (congrArg (Formula signature (sort :: real) []) rightStability)
          line4Formula =
        implication stableNegation stableDisjunction rawHypothesis
          (star_4_01 stableNegation stableDisjunction
            stableLeftBody stableRightBody) := by
    unfold line4Formula
    rw [rightDisjunctionNormalization]
    have line5 := mixedImplication_normalizeSameOrder rfl
      applicationStability stableNegation stableDisjunction
      rawHypothesis rawConsequence
    exact Eq.trans line5
      (congrArg (implication stableNegation stableDisjunction rawHypothesis)
        consequenceNormalization)
  rw [line4Normalization] at line4Cast
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let descriptionCandidate : Term signature real [sort, sort] sort :=
    .apparent (.succ .zero)
  let conditionUnderCandidate : Formula signature real [sort, sort]
      identityOrder := condition.rename
    (liftRenaming (fun v => .succ v))
  let uniquenessMatrix := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction conditionUnderCandidate
      (star_13_01 conditionIdentity x descriptionCandidate))
  let equalityMatrix := star_13_192_body conditionIdentity identityUniversal
    identityNegation identityDisjunction stableNegation
    applicationBodyNegation applicationBodyDisjunction psi b
  let applicationMatrix := mixedConjunction stableNegation
    conditionIdentity.negation applicationBodyNegation
    applicationBodyDisjunction uniquenessMatrix psi
  let stableApplicationMatrix := Eq.mp (congrArg
    (Formula signature real [sort]) applicationStability) applicationMatrix
  let stableEqualityMatrix := Eq.mp (congrArg
    (Formula signature real [sort]) applicationStability) equalityMatrix
  let hypothesisVariable : Term signature real [sort] sort := .apparent .zero
  let hypothesisIdentity := star_13_01 conditionIdentity hypothesisVariable
    b.weaken
  let hypothesisMatrix := equivalence identityNegation identityDisjunction
    condition hypothesisIdentity
  let hypothesis := Formula.always identityUniversal hypothesisMatrix
  have hypothesisWeaken : hypothesis.weakenReal (fresh := sort) =
      rawHypothesis := by
    unfold hypothesis hypothesisMatrix rawHypothesis rawHypothesisMatrix
      hypothesisIdentity hypothesisVariable rawCondition rawIdentityB apparent
      bValue
    change Formula.always identityUniversal
      ((equivalence identityNegation identityDisjunction condition
        (star_13_01 conditionIdentity (.apparent .zero) b.weaken)).weakenReal) = _
    rw [star14_matrixEquivalence_weakenReal, star14_identity_weakenReal]
    cases b <;> rfl
  have uniquenessAtCandidate :
      uniquenessMatrix.weakenReal.instantiate candidate = rawLeft := by
    unfold uniquenessMatrix rawLeft rawLeftMatrix conditionUnderCandidate
      rawCondition rawIdentityC x descriptionCandidate apparent
    change (Formula.always identityUniversal
      ((equivalence identityNegation identityDisjunction
        (condition.rename (liftRenaming (fun v => .succ v)))
        (star_13_01 conditionIdentity (.apparent .zero)
          (.apparent (.succ .zero)))).weakenReal)).instantiate candidate = _
    rw [Formula.instantiate, substitute_always,
      star14_matrixEquivalence_weakenReal,
      star14_matrixEquivalence_substitute]
    rw [star14_conditionUnderCandidate_instantiate]
    rw [star14_identity_weakenReal, star14_identity_substitute]
    rfl
  have equalityAtCandidate :
      equalityMatrix.weakenReal.instantiate candidate = rightBody := by
    unfold equalityMatrix star_13_192_body rightBody rawRight
      rawRightMatrix psiCandidate
    change mixedConjunction stableNegation conditionIdentity.negation
      applicationBodyNegation applicationBodyDisjunction
      ((Formula.always identityUniversal
        ((star_13_192_identityMatrix conditionIdentity identityNegation
          identityDisjunction b).weakenReal)).instantiate candidate)
      (psi.weakenReal.instantiate candidate) = _
    unfold star_13_192_identityMatrix
    rw [Formula.instantiate, substitute_always,
      star14_matrixEquivalence_weakenReal,
      star14_matrixEquivalence_substitute]
    unfold rawIdentityB rawIdentityC apparent candidate bValue
    rw [star14_identity_weakenReal, star14_identity_substitute,
      star14_identity_weakenReal, star14_identity_substitute]
    cases b <;> rfl
  have applicationAtCandidate :
      applicationMatrix.weakenReal.instantiate candidate = leftBody := by
    unfold applicationMatrix leftBody psiCandidate
    change mixedConjunction stableNegation conditionIdentity.negation
      applicationBodyNegation applicationBodyDisjunction
      (uniquenessMatrix.weakenReal.instantiate candidate)
      (psi.weakenReal.instantiate candidate) = _
    rw [uniquenessAtCandidate]
  have stableApplicationAtCandidate :
      stableApplicationMatrix.weakenReal.instantiate candidate =
        stableLeftBody := by
    unfold stableApplicationMatrix stableLeftBody
    rw [Formula.weakenReal_cast]
    unfold Formula.instantiate
    rw [Formula.substitute_cast]
    change Eq.mp (congrArg (Formula signature (sort :: real) [])
      applicationStability)
      (applicationMatrix.weakenReal.instantiate candidate) = _
    exact congrArg (fun formula : Formula signature (sort :: real) []
        applicationOrder => Eq.mp
      (congrArg (Formula signature (sort :: real) []) applicationStability)
      formula) applicationAtCandidate
    exact applicationStability
    exact applicationStability
  have stableEqualityAtCandidate :
      stableEqualityMatrix.weakenReal.instantiate candidate =
        stableRightBody := by
    unfold stableEqualityMatrix stableRightBody
    rw [Formula.weakenReal_cast]
    unfold Formula.instantiate
    rw [Formula.substitute_cast]
    change Eq.mp (congrArg (Formula signature (sort :: real) [])
      applicationStability)
      (equalityMatrix.weakenReal.instantiate candidate) = _
    exact congrArg (fun formula : Formula signature (sort :: real) []
        applicationOrder => Eq.mp
      (congrArg (Formula signature (sort :: real) []) applicationStability)
      formula) equalityAtCandidate
    exact applicationStability
    exact applicationStability
  rw [← hypothesisWeaken, ← stableApplicationAtCandidate,
    ← stableEqualityAtCandidate] at line4Cast
  have line5 := star14_liftConditionalSaturatedExistentialEquivalence
    stableUniversal stableNegation stableDisjunction hypothesis
    stableApplicationMatrix stableEqualityMatrix line4Cast
  let applicationResultStability := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      applicationStability)
    (star14_bindOrderStable identityOrder sort)
  let psiDescription := Formula.sometimes applicationExistential
    applicationMatrix
  let equalityDescription := Formula.sometimes applicationExistential
    equalityMatrix
  have applicationScopeNormalization :
      Eq.mp (congrArg (Formula signature real [])
        applicationResultStability) psiDescription =
        star14_saturatedExistential stableUniversal stableNegation
          stableApplicationMatrix := by
    unfold psiDescription applicationExistential logicalVocabulary
      star_14_15_logicalVocabulary stableApplicationMatrix
    exact star14_saturatedExistential_cast applicationStability
      applicationResultStability stableBind stableUniversal stableNegation
      applicationMatrix
  have equalityScopeNormalization :
      Eq.mp (congrArg (Formula signature real [])
        applicationResultStability) equalityDescription =
        star14_saturatedExistential stableUniversal stableNegation
          stableEqualityMatrix := by
    unfold equalityDescription applicationExistential logicalVocabulary
      star_14_15_logicalVocabulary stableEqualityMatrix
    exact star14_saturatedExistential_cast applicationStability
      applicationResultStability stableBind stableUniversal stableNegation
      equalityMatrix
  rw [← applicationScopeNormalization,
    ← equalityScopeNormalization] at line5
  have applicationOuterNegationNormalization :
      Eq.mp (congrArg signature.Negation applicationResultStability)
        applicationExistential.outerNegation = stableNegation := by
    unfold applicationExistential logicalVocabulary
      star_14_15_logicalVocabulary applicationResultStability stableNegation
    exact Eq.trans (star14_cast_trans applicationResultStability.symm
      applicationResultStability stableNegation).symm
      (star14_cast_self
        (Eq.trans applicationResultStability.symm applicationResultStability)
        stableNegation)
  have applicationResultDisjunctionNormalization :
      Eq.mp (congrArg signature.Disjunction applicationResultStability)
        applicationResultDisjunction = stableDisjunction := by
    unfold applicationResultDisjunction logicalVocabulary
      star_14_15_logicalVocabulary applicationResultStability stableDisjunction
    exact Eq.trans (star14_cast_trans applicationResultStability.symm
      applicationResultStability stableDisjunction).symm
      (star14_cast_self
        (Eq.trans applicationResultStability.symm applicationResultStability)
        stableDisjunction)
  rw [← applicationOuterNegationNormalization,
    ← applicationResultDisjunctionNormalization] at line5
  let rawHypothesis := Eq.mp (congrArg (Formula signature real [])
    applicationResultStability.symm) hypothesis
  let rawApplicationEquivalence := star_4_01
    applicationExistential.outerNegation applicationResultDisjunction
    psiDescription equalityDescription
  have applicationScopeRoundtrip :
      Eq.mp (congrArg (Formula signature real [])
        applicationResultStability.symm)
        (Eq.mp (congrArg (Formula signature real [])
          applicationResultStability) psiDescription) = psiDescription := by
    exact Eq.trans (star14_cast_trans applicationResultStability
      applicationResultStability.symm psiDescription).symm
      (star14_cast_self
        (Eq.trans applicationResultStability applicationResultStability.symm)
        psiDescription)
  have equalityScopeRoundtrip :
      Eq.mp (congrArg (Formula signature real [])
        applicationResultStability.symm)
        (Eq.mp (congrArg (Formula signature real [])
          applicationResultStability) equalityDescription) =
        equalityDescription := by
    exact Eq.trans (star14_cast_trans applicationResultStability
      applicationResultStability.symm equalityDescription).symm
      (star14_cast_self
        (Eq.trans applicationResultStability applicationResultStability.symm)
        equalityDescription)
  have line5Cast := star14_castAssertionOrder
    applicationResultStability.symm
    (implication
      (Eq.mp (congrArg signature.Negation applicationResultStability)
        applicationExistential.outerNegation)
      (Eq.mp (congrArg signature.Disjunction applicationResultStability)
        applicationResultDisjunction)
      hypothesis
      (star_4_01
        (Eq.mp (congrArg signature.Negation applicationResultStability)
          applicationExistential.outerNegation)
        (Eq.mp (congrArg signature.Disjunction applicationResultStability)
          applicationResultDisjunction)
        (Eq.mp (congrArg (Formula signature real [])
          applicationResultStability) psiDescription)
        (Eq.mp (congrArg (Formula signature real [])
          applicationResultStability) equalityDescription))) line5
  have line5Normalization :
      Eq.mp (congrArg (Formula signature real [])
        applicationResultStability.symm)
        (implication
          (Eq.mp (congrArg signature.Negation applicationResultStability)
            applicationExistential.outerNegation)
          (Eq.mp (congrArg signature.Disjunction applicationResultStability)
            applicationResultDisjunction)
          hypothesis
          (star_4_01
            (Eq.mp (congrArg signature.Negation applicationResultStability)
              applicationExistential.outerNegation)
            (Eq.mp (congrArg signature.Disjunction applicationResultStability)
              applicationResultDisjunction)
            (Eq.mp (congrArg (Formula signature real [])
              applicationResultStability) psiDescription)
            (Eq.mp (congrArg (Formula signature real [])
              applicationResultStability) equalityDescription))) =
        implication applicationExistential.outerNegation
          applicationResultDisjunction rawHypothesis
          rawApplicationEquivalence := by
    rw [star14_implication_castOrder]
    unfold rawHypothesis rawApplicationEquivalence star_4_01
    rw [star14_conjunction_castOrder, star14_implication_castOrder,
      star14_implication_castOrder]
    rw [applicationScopeRoundtrip, equalityScopeRoundtrip]
    exact applicationResultStability.symm
    exact applicationResultStability.symm
    exact applicationResultStability.symm
    exact applicationResultStability.symm
  rw [line5Normalization] at line5Cast
  let applicationForward := Eq.mp (congrArg (Formula signature real [])
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder)))
    (star_10_23_right applicationExistential
      applicationExistential.universal applicationImplicationUniversal
      applicationBodyNegation
      (Eq.mp (congrArg signature.Disjunction
        (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder).symm)
        applicationBodyDisjunction)
      applicationMatrix (psi.instantiate b))
  let equalityForward := Eq.mp (congrArg (Formula signature real [])
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder)))
    (star_10_23_right applicationExistential
      applicationExistential.universal applicationImplicationUniversal
      applicationBodyNegation
      (Eq.mp (congrArg signature.Disjunction
        (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder).symm)
        applicationBodyDisjunction)
      equalityMatrix (psi.instantiate b))
  let applicationReverse := star14_normalizedDisjunction
    (Eq.trans
      (bindOrderMaxLeft conditionOrder
        (max uniquenessOrder conditionOrder) sort)
      (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
        (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder)))
    applicationResultDisjunction
    (.neg conditionIdentity.negation (psi.instantiate b)) psiDescription
  let equalityReverse := star14_normalizedDisjunction
    (Eq.trans
      (bindOrderMaxLeft conditionOrder
        (max uniquenessOrder conditionOrder) sort)
      (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
        (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder)))
    applicationResultDisjunction
    (.neg conditionIdentity.negation (psi.instantiate b)) equalityDescription
  let applicationConclusion := conjunction
    applicationExistential.outerNegation applicationResultDisjunction
    applicationForward applicationReverse
  let equalityConclusion := conjunction
    applicationExistential.outerNegation applicationResultDisjunction
    equalityForward equalityReverse
  let applicationEquivalenceForward := implication
    applicationExistential.outerNegation applicationResultDisjunction
    psiDescription equalityDescription
  let applicationEquivalenceReverse := implication
    applicationExistential.outerNegation applicationResultDisjunction
    equalityDescription psiDescription
  have line6 := star14_composeSame applicationExistential.outerNegation
    applicationResultDisjunction rawHypothesis rawApplicationEquivalence
    applicationEquivalenceForward line5Cast
    (star_3_26 applicationExistential.outerNegation
      applicationResultDisjunction applicationEquivalenceForward
      applicationEquivalenceReverse)
  have line7 := star14_composeSame applicationExistential.outerNegation
    applicationResultDisjunction rawHypothesis rawApplicationEquivalence
    applicationEquivalenceReverse line5Cast
    (star_3_27 applicationExistential.outerNegation
      applicationResultDisjunction applicationEquivalenceForward
      applicationEquivalenceReverse)
  change Derivation (.assertion equalityConclusion) at line1
  have line8 := Derivation.star_9_12_same
    applicationExistential.outerNegation applicationResultDisjunction line1
    (star_3_26 applicationExistential.outerNegation
      applicationResultDisjunction equalityForward equalityReverse)
  have line9 := Derivation.star_9_12_same
    applicationExistential.outerNegation applicationResultDisjunction line1
    (star_3_27 applicationExistential.outerNegation
      applicationResultDisjunction equalityForward equalityReverse)
  let applicationResultOrder := bindOrder
    (max uniquenessOrder conditionOrder) sort
  have conditionLeApplicationResult :
      conditionOrder ≤ applicationResultOrder := by
    exact Nat.le_trans (star14_le_max_right uniquenessOrder conditionOrder)
      (star14_le_max_left _ _)
  let scopePsiEquality : max applicationResultOrder conditionOrder =
      applicationResultOrder :=
    star14_max_eq_left_of_le conditionLeApplicationResult
  let pairEquality := natMaxSelf applicationResultOrder
  let consequenceEquality :
      max (max applicationResultOrder applicationResultOrder)
          (max applicationResultOrder conditionOrder) =
        applicationResultOrder :=
    natMaxCongr pairEquality scopePsiEquality
  let primitiveOuterEquality :
      max (max applicationResultOrder conditionOrder)
          (max (max applicationResultOrder applicationResultOrder)
            (max applicationResultOrder conditionOrder)) =
        applicationResultOrder :=
    natMaxCongr scopePsiEquality consequenceEquality
  let scopePsiNegation := Eq.mp (congrArg signature.Negation
    scopePsiEquality.symm) applicationExistential.outerNegation
  let scopePsiDisjunction := Eq.mp (congrArg signature.Disjunction
    scopePsiEquality.symm) applicationResultDisjunction
  let pairNegation := Eq.mp (congrArg signature.Negation
    pairEquality.symm) applicationExistential.outerNegation
  let pairDisjunction := Eq.mp (congrArg signature.Disjunction
    pairEquality.symm) applicationResultDisjunction
  let consequenceDisjunction := Eq.mp (congrArg signature.Disjunction
    consequenceEquality.symm) applicationResultDisjunction
  let primitiveOuterDisjunction := Eq.mp (congrArg signature.Disjunction
    primitiveOuterEquality.symm) applicationResultDisjunction
  let equalityNegated := star_9_02 applicationExistential.universal
    applicationBodyNegation equalityMatrix
  let applicationNegated := star_9_02 applicationExistential.universal
    applicationBodyNegation applicationMatrix
  let applicationScopedForward := sameDisjunction
    applicationResultDisjunction applicationNegated equalityDescription
  have equalityNegationDefinition : ImplicationNegation signature real
      applicationExistential.outerNegation equalityDescription
      equalityNegated := by
    unfold equalityDescription equalityNegated
    exact ImplicationNegation.star_9_02
      applicationExistential.outerNegation applicationExistential
      applicationExistential.universal applicationBodyNegation equalityMatrix
  have applicationNegationDefinition : ImplicationNegation signature real
      applicationExistential.outerNegation psiDescription
      applicationNegated := by
    unfold psiDescription applicationNegated
    exact ImplicationNegation.star_9_02
      applicationExistential.outerNegation applicationExistential
      applicationExistential.universal applicationBodyNegation
      applicationMatrix
  have equalityForwardDefinition : ImplicationDisjunction signature real
      equalityNegated (psi.instantiate b) equalityForward := by
    unfold equalityForward equalityNegated
    apply star14_castImplicationDisjunctionResult
      (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
        (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder))
    unfold star_10_23_right
    exact ImplicationDisjunction.star_9_03
      applicationExistential.universal applicationImplicationUniversal
      (.neg applicationBodyNegation equalityMatrix) (psi.instantiate b)
      (.disj
        (Eq.mp (congrArg signature.Disjunction
          (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder).symm)
          applicationBodyDisjunction)
        (.neg applicationBodyNegation equalityMatrix)
        ((psi.instantiate b).rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01
        (Eq.mp (congrArg signature.Disjunction
          (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder).symm)
          applicationBodyDisjunction)
        (.neg applicationBodyNegation equalityMatrix)
        ((psi.instantiate b).rename (fun v => .succ v)))
  have applicationForwardDefinition : ImplicationDisjunction signature real
      applicationNegated (psi.instantiate b) applicationForward := by
    unfold applicationForward applicationNegated
    apply star14_castImplicationDisjunctionResult
      (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
        (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder))
    unfold star_10_23_right
    exact ImplicationDisjunction.star_9_03
      applicationExistential.universal applicationImplicationUniversal
      (.neg applicationBodyNegation applicationMatrix) (psi.instantiate b)
      (.disj
        (Eq.mp (congrArg signature.Disjunction
          (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder).symm)
          applicationBodyDisjunction)
        (.neg applicationBodyNegation applicationMatrix)
        ((psi.instantiate b).rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01
        (Eq.mp (congrArg signature.Disjunction
          (MixedOrder.maxRightAbsorb uniquenessOrder conditionOrder).symm)
          applicationBodyDisjunction)
        (.neg applicationBodyNegation applicationMatrix)
        ((psi.instantiate b).rename (fun v => .succ v)))
  have line10 := star14_scopeNegationImplication
    applicationExistential.outerNegation applicationResultDisjunction
    applicationNegated equalityDescription
  change Derivation (.assertion
    (implication applicationExistential.outerNegation
      applicationResultDisjunction applicationEquivalenceForward
      applicationScopedForward)) at line10
  have line11 := star14_composeSame applicationExistential.outerNegation
    applicationResultDisjunction rawHypothesis applicationEquivalenceForward
    applicationScopedForward line6 line10
  have line12 := star14_certifiedSyllogismRight
    applicationExistential.outerNegation applicationResultDisjunction
    psiDescription equalityDescription (psi.instantiate b)
    applicationNegated equalityNegated applicationScopedForward equalityForward
    applicationForward applicationExistential.outerNegation
    applicationExistential.outerNegation scopePsiDisjunction
    scopePsiNegation pairNegation pairDisjunction scopePsiDisjunction
    consequenceDisjunction primitiveOuterDisjunction
    applicationNegationDefinition
    equalityNegationDefinition
    (ImplicationDisjunction.star_1_01_same applicationResultDisjunction
      applicationNegated equalityDescription)
    equalityForwardDefinition applicationForwardDefinition line8
  have line13 := star14_composeSame applicationExistential.outerNegation
    applicationResultDisjunction rawHypothesis applicationScopedForward
    applicationForward line11 line12
  let equalityScopedReverse := sameDisjunction
    applicationResultDisjunction equalityNegated psiDescription
  have line14 := star14_scopeNegationImplication
    applicationExistential.outerNegation applicationResultDisjunction
    equalityNegated psiDescription
  change Derivation (.assertion
    (implication applicationExistential.outerNegation
      applicationResultDisjunction applicationEquivalenceReverse
      equalityScopedReverse)) at line14
  have line15 := star14_composeSame applicationExistential.outerNegation
    applicationResultDisjunction rawHypothesis applicationEquivalenceReverse
    equalityScopedReverse line7 line14
  let reversePairEquality : max conditionOrder applicationResultOrder =
      applicationResultOrder := Nat.max_eq_right conditionLeApplicationResult
  let reverseConsequenceEquality :
      max (max conditionOrder applicationResultOrder)
          (max conditionOrder applicationResultOrder) =
        applicationResultOrder :=
    natMaxCongr reversePairEquality reversePairEquality
  let reverseOuterEquality :
      max (max applicationResultOrder applicationResultOrder)
          (max (max conditionOrder applicationResultOrder)
            (max conditionOrder applicationResultOrder)) =
        applicationResultOrder :=
    natMaxCongr pairEquality reverseConsequenceEquality
  let reversePairNegation := Eq.mp (congrArg signature.Negation
    reversePairEquality.symm) applicationExistential.outerNegation
  let reversePairDisjunction := Eq.mp (congrArg signature.Disjunction
    reversePairEquality.symm) applicationResultDisjunction
  let reverseConsequenceDisjunction := Eq.mp
    (congrArg signature.Disjunction reverseConsequenceEquality.symm)
    applicationResultDisjunction
  let reverseOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction reverseOuterEquality.symm)
    applicationResultDisjunction
  have equalityReverseDefinition : ImplicationDisjunction signature real
      (.neg conditionIdentity.negation (psi.instantiate b))
      equalityDescription equalityReverse := by
    unfold equalityReverse star14_normalizedDisjunction
    apply star14_castImplicationDisjunctionResult
      (Eq.trans
        (bindOrderMaxLeft conditionOrder
          (max uniquenessOrder conditionOrder) sort)
        (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
          (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder)))
    exact ImplicationDisjunction.star_1_01
      (Eq.mp (congrArg signature.Disjunction
        (Eq.trans
          (bindOrderMaxLeft conditionOrder
            (max uniquenessOrder conditionOrder) sort)
          (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
            (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder))).symm)
        applicationResultDisjunction)
      (.neg conditionIdentity.negation (psi.instantiate b))
      equalityDescription
  have applicationReverseDefinition : ImplicationDisjunction signature real
      (.neg conditionIdentity.negation (psi.instantiate b))
      psiDescription applicationReverse := by
    unfold applicationReverse star14_normalizedDisjunction
    apply star14_castImplicationDisjunctionResult
      (Eq.trans
        (bindOrderMaxLeft conditionOrder
          (max uniquenessOrder conditionOrder) sort)
        (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
          (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder)))
    exact ImplicationDisjunction.star_1_01
      (Eq.mp (congrArg signature.Disjunction
        (Eq.trans
          (bindOrderMaxLeft conditionOrder
            (max uniquenessOrder conditionOrder) sort)
          (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
            (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder))).symm)
        applicationResultDisjunction)
      (.neg conditionIdentity.negation (psi.instantiate b)) psiDescription
  have line16 := star14_certifiedSyllogismLeft
    applicationExistential.outerNegation applicationResultDisjunction
    (psi.instantiate b) equalityDescription psiDescription
    (.neg conditionIdentity.negation (psi.instantiate b)) equalityNegated
    equalityReverse equalityScopedReverse applicationReverse
    conditionIdentity.negation applicationExistential.outerNegation
    pairDisjunction pairNegation reversePairNegation reversePairDisjunction
    reversePairDisjunction reverseConsequenceDisjunction
    reverseOuterDisjunction
    (ImplicationNegation.star_1_01 conditionIdentity.negation
      (psi.instantiate b))
    equalityNegationDefinition equalityReverseDefinition
    (ImplicationDisjunction.star_1_01_same applicationResultDisjunction
      equalityNegated psiDescription)
    applicationReverseDefinition line9
  have line17 := star14_composeSame applicationExistential.outerNegation
    applicationResultDisjunction rawHypothesis equalityScopedReverse
    applicationReverse line15 line16
  have line18 := star14_joinUnder applicationExistential.outerNegation
    applicationResultDisjunction rawHypothesis applicationForward
    applicationReverse line13 line17
  have applicationOuterNegationSource :
      applicationExistential.outerNegation =
        Eq.mp (congrArg signature.Negation applicationResultStability.symm)
          stableNegation := by
    unfold applicationExistential logicalVocabulary
      star_14_15_logicalVocabulary applicationResultStability stableNegation
    rfl
  have applicationResultDisjunctionSource :
      applicationResultDisjunction =
        Eq.mp (congrArg signature.Disjunction
          applicationResultStability.symm) stableDisjunction := by
    unfold applicationResultDisjunction logicalVocabulary
      star_14_15_logicalVocabulary applicationResultStability stableDisjunction
    rfl
  rw [applicationOuterNegationSource,
    applicationResultDisjunctionSource] at line18
  let stableApplicationConclusion := Eq.mp
    (congrArg (Formula signature real []) applicationResultStability)
    applicationConclusion
  have hypothesisRoundtrip :
      Eq.mp (congrArg (Formula signature real []) applicationResultStability)
        rawHypothesis = hypothesis := by
    unfold rawHypothesis
    exact Eq.trans (star14_cast_trans applicationResultStability.symm
      applicationResultStability hypothesis).symm
      (star14_cast_self
        (Eq.trans applicationResultStability.symm applicationResultStability)
        hypothesis)
  have line18Cast := star14_castAssertionOrder applicationResultStability
    (implication
      (Eq.mp (congrArg signature.Negation applicationResultStability.symm)
        stableNegation)
      (Eq.mp (congrArg signature.Disjunction
        applicationResultStability.symm) stableDisjunction)
      rawHypothesis applicationConclusion) line18
  have line18Normalization :
      Eq.mp (congrArg (Formula signature real []) applicationResultStability)
        (implication
          (Eq.mp (congrArg signature.Negation
            applicationResultStability.symm) stableNegation)
          (Eq.mp (congrArg signature.Disjunction
            applicationResultStability.symm) stableDisjunction)
          rawHypothesis applicationConclusion) =
        implication stableNegation stableDisjunction hypothesis
          stableApplicationConclusion := by
    rw [star14_implication_castOrder]
    unfold stableApplicationConclusion
    rw [hypothesisRoundtrip]
    exact applicationResultStability
  rw [line18Normalization] at line18Cast
  let stableApplicationForward := Eq.mp
    (congrArg (Formula signature real []) applicationResultStability)
    applicationForward
  let stableApplicationReverse := Eq.mp
    (congrArg (Formula signature real []) applicationResultStability)
    applicationReverse
  have stableApplicationConclusionShape : stableApplicationConclusion =
      conjunction stableNegation stableDisjunction
        stableApplicationForward stableApplicationReverse := by
    unfold stableApplicationConclusion applicationConclusion
      stableApplicationForward stableApplicationReverse
    rw [applicationOuterNegationSource,
      applicationResultDisjunctionSource]
    exact star14_conjunction_castOrder applicationResultStability
      stableNegation stableDisjunction applicationForward applicationReverse
  have line242Base := line18Cast
  rw [stableApplicationConclusionShape] at line242Base
  have line242 := star14_composeSame stableNegation stableDisjunction
    hypothesis
    (conjunction stableNegation stableDisjunction
      stableApplicationForward stableApplicationReverse)
    (conjunction stableNegation stableDisjunction
      stableApplicationReverse stableApplicationForward)
    line242Base
    (star_3_22 stableNegation stableDisjunction
      stableApplicationForward stableApplicationReverse)
  change Derivation (star_14_242_reading identityUniversal
    conditionIdentity identityNegation identityDisjunction
    applicationExistential applicationBodyDisjunction
    applicationImplicationUniversal applicationResultDisjunction
    condition psi b).parsed at line242
  let continuationOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionBodyOrder := max uniquenessOrder continuationOrder
  let descriptionResultOrder := bindOrder descriptionBodyOrder sort
  let continuationMatrix := star_13_01 continuationIdentity
    (.apparent (.zero : Var [sort] sort)) b.weaken
  let descriptionNegation : MixedOrder.BinaryNegations signature := {
    leftOrder := uniquenessOrder
    rightOrder := continuationOrder
    left := uniquenessNegation
    right := continuationIdentityNegation
    both := descriptionBodyNegation
  }
  let descriptionDisjunction :
      MixedOrder.BinaryDisjunctions signature descriptionNegation := {
    left := uniquenessDisjunction
    right := continuationIdentityDisjunction
    both := descriptionBodyDisjunction
  }
  let originalDescriptionBody := mixedConjunction uniquenessNegation
    continuationIdentityNegation descriptionBodyNegation
    descriptionBodyDisjunction uniquenessMatrix continuationMatrix
  let swappedDescriptionBody := star14_swappedConjunction
    descriptionNegation descriptionDisjunction uniquenessMatrix
    continuationMatrix
  let descriptionCandidateValue : Term signature (sort :: real) [] sort :=
    .real .zero
  let uniquenessAtDescriptionCandidate :=
    uniquenessMatrix.weakenReal.instantiate descriptionCandidateValue
  let continuationAtDescriptionCandidate :=
    continuationMatrix.weakenReal.instantiate descriptionCandidateValue
  have line19 := star14_commuteEquivalenceNormalized descriptionNegation
    descriptionDisjunction uniquenessAtDescriptionCandidate
    continuationAtDescriptionCandidate
  rw [star14_binaryLeft_eq, star14_binaryRight_eq] at line19
  have originalDescriptionAtCandidate :
      originalDescriptionBody.weakenReal.instantiate
        descriptionCandidateValue =
      mixedConjunction uniquenessNegation continuationIdentityNegation
        descriptionBodyNegation descriptionBodyDisjunction
        uniquenessAtDescriptionCandidate continuationAtDescriptionCandidate := by
    unfold originalDescriptionBody uniquenessAtDescriptionCandidate
      continuationAtDescriptionCandidate Formula.instantiate
    rw [star14_mixedConjunction_weakenReal,
      star14_mixedConjunction_substitute]
  have swappedDescriptionAtCandidate :
      swappedDescriptionBody.weakenReal.instantiate
        descriptionCandidateValue =
      star14_swappedConjunction descriptionNegation descriptionDisjunction
        uniquenessAtDescriptionCandidate
        continuationAtDescriptionCandidate := by
    unfold swappedDescriptionBody uniquenessAtDescriptionCandidate
      continuationAtDescriptionCandidate Formula.instantiate
    rw [star14_swappedConjunction_weakenReal,
      star14_swappedConjunction_substitute]
  rw [← originalDescriptionAtCandidate,
    ← swappedDescriptionAtCandidate] at line19
  have uniquenessLeContinuation : uniquenessOrder ≤ continuationOrder := by
    unfold continuationOrder bindOrder
    exact star14_le_max_left _ _
  let descriptionBodyStability : descriptionBodyOrder = continuationOrder :=
    Nat.max_eq_right uniquenessLeContinuation
  have uniquenessHeight : Nat.succ sort.height ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_right _ _
  have descriptionHeight : Nat.succ sort.height ≤ descriptionBodyOrder :=
    Nat.le_trans uniquenessHeight (star14_le_max_left _ _)
  let descriptionBindStability : descriptionResultOrder =
      descriptionBodyOrder := star14_bindOrder_eq_of_le descriptionHeight
  let descriptionSecondBindStability :
      bindOrder descriptionResultOrder sort = descriptionResultOrder :=
    Eq.trans
      (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
        descriptionBindStability)
      (Eq.trans descriptionBindStability descriptionBindStability.symm)
  let stableDescriptionUniversal := Eq.mp
    (congrArg (signature.Universal sort) descriptionBindStability.symm)
    descriptionExistential.universal
  let stableDescriptionNegation := Eq.mp
    (congrArg signature.Negation descriptionBindStability.symm)
    descriptionBodyNegation
  let stableDescriptionDisjunction := Eq.mp
    (congrArg signature.Disjunction descriptionBindStability.symm)
    descriptionBodyDisjunction
  let stableOriginalDescriptionBody := Eq.mp
    (congrArg (Formula signature real [sort])
      descriptionBindStability.symm) originalDescriptionBody
  let stableSwappedDescriptionBody := Eq.mp
    (congrArg (Formula signature real [sort])
      descriptionBindStability.symm) swappedDescriptionBody
  have descriptionNegationSource : descriptionBodyNegation =
      Eq.mp (congrArg signature.Negation descriptionBindStability)
        stableDescriptionNegation := by
    unfold stableDescriptionNegation
    exact Eq.trans
      (star14_cast_self
        (Eq.trans descriptionBindStability.symm descriptionBindStability)
        descriptionBodyNegation).symm
      (star14_cast_trans descriptionBindStability.symm
        descriptionBindStability descriptionBodyNegation)
  have descriptionDisjunctionSource : descriptionBodyDisjunction =
      Eq.mp (congrArg signature.Disjunction descriptionBindStability)
        stableDescriptionDisjunction := by
    unfold stableDescriptionDisjunction
    exact Eq.trans
      (star14_cast_self
        (Eq.trans descriptionBindStability.symm descriptionBindStability)
        descriptionBodyDisjunction).symm
      (star14_cast_trans descriptionBindStability.symm
        descriptionBindStability descriptionBodyDisjunction)
  have line19Cast := star14_castAssertionOrder descriptionBindStability.symm
    (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
      (originalDescriptionBody.weakenReal.instantiate
        descriptionCandidateValue)
      (swappedDescriptionBody.weakenReal.instantiate
        descriptionCandidateValue)) line19
  have line19Normalization :
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        descriptionBindStability.symm)
        (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
          (originalDescriptionBody.weakenReal.instantiate
            descriptionCandidateValue)
          (swappedDescriptionBody.weakenReal.instantiate
            descriptionCandidateValue)) =
      star_4_01 stableDescriptionNegation stableDescriptionDisjunction
        (stableOriginalDescriptionBody.weakenReal.instantiate
          descriptionCandidateValue)
        (stableSwappedDescriptionBody.weakenReal.instantiate
          descriptionCandidateValue) := by
    rw [descriptionNegationSource, descriptionDisjunctionSource]
    unfold stableOriginalDescriptionBody stableSwappedDescriptionBody
    unfold star_4_01
    rw [star14_conjunction_castOrder, star14_implication_castOrder,
      star14_implication_castOrder, Formula.weakenReal_cast,
      Formula.weakenReal_cast]
    unfold Formula.instantiate
    rw [Formula.substitute_cast, Formula.substitute_cast]
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
  rw [line19Normalization] at line19Cast
  have line20 := star14_liftSaturatedExistentialEquivalence
    stableDescriptionUniversal stableDescriptionNegation
    stableDescriptionDisjunction stableOriginalDescriptionBody
    stableSwappedDescriptionBody line19Cast
  let originalDescription := Formula.sometimes descriptionExistential
    originalDescriptionBody
  let swappedDescription := Formula.sometimes descriptionExistential
    swappedDescriptionBody
  have descriptionMatrixNegationSource :
      descriptionExistential.matrixNegation =
        Eq.mp (congrArg signature.Negation descriptionBindStability)
          stableDescriptionNegation := by
    unfold stableDescriptionNegation
    have line21 := Eq.trans
      (star14_cast_self
        (Eq.trans descriptionBindStability.symm descriptionBindStability)
        descriptionBodyNegation).symm
      (star14_cast_trans descriptionBindStability.symm
        descriptionBindStability descriptionBodyNegation)
    unfold descriptionExistential logicalVocabulary
      star_14_15_logicalVocabulary descriptionBodyNegation
    exact line21
  have descriptionUniversalSource : descriptionExistential.universal =
      Eq.mp (congrArg (signature.Universal sort) descriptionBindStability)
        stableDescriptionUniversal := by
    unfold stableDescriptionUniversal
    have line21 := Eq.trans
      (star14_cast_self
        (Eq.trans descriptionBindStability.symm descriptionBindStability)
        descriptionExistential.universal).symm
      (star14_cast_trans descriptionBindStability.symm
        descriptionBindStability descriptionExistential.universal)
    exact line21
  have descriptionOuterNegationSource :
      descriptionExistential.outerNegation = stableDescriptionNegation := by
    unfold descriptionExistential stableDescriptionNegation logicalVocabulary
      star_14_15_logicalVocabulary descriptionBindStability
    rfl
  have originalDescriptionNormalization : originalDescription =
      star14_saturatedExistential stableDescriptionUniversal
        stableDescriptionNegation stableOriginalDescriptionBody := by
    unfold originalDescription Formula.sometimes
    rw [descriptionMatrixNegationSource, descriptionUniversalSource,
      descriptionOuterNegationSource]
    unfold stableOriginalDescriptionBody
    exact star14_saturatedExistential_cast descriptionBindStability.symm rfl
      descriptionSecondBindStability stableDescriptionUniversal
      stableDescriptionNegation originalDescriptionBody
  have swappedDescriptionNormalization : swappedDescription =
      star14_saturatedExistential stableDescriptionUniversal
        stableDescriptionNegation stableSwappedDescriptionBody := by
    unfold swappedDescription Formula.sometimes
    rw [descriptionMatrixNegationSource, descriptionUniversalSource,
      descriptionOuterNegationSource]
    unfold stableSwappedDescriptionBody
    exact star14_saturatedExistential_cast descriptionBindStability.symm rfl
      descriptionSecondBindStability stableDescriptionUniversal
      stableDescriptionNegation swappedDescriptionBody
  rw [← originalDescriptionNormalization,
    ← swappedDescriptionNormalization] at line20
  have line21 := star_14_1 originalDescription stableDescriptionNegation
    stableDescriptionDisjunction
  change Derivation (.assertion
    (conjunction stableDescriptionNegation stableDescriptionDisjunction
      (implication stableDescriptionNegation stableDescriptionDisjunction
        originalDescription originalDescription)
      (implication stableDescriptionNegation stableDescriptionDisjunction
        originalDescription originalDescription))) at line21
  have line22 := Derivation.star_9_12_same stableDescriptionNegation
    stableDescriptionDisjunction line21
    (star_3_26 stableDescriptionNegation stableDescriptionDisjunction
      (implication stableDescriptionNegation stableDescriptionDisjunction
        originalDescription originalDescription)
      (implication stableDescriptionNegation stableDescriptionDisjunction
        originalDescription originalDescription))
  change Derivation (.assertion
    (conjunction stableDescriptionNegation stableDescriptionDisjunction
      (implication stableDescriptionNegation stableDescriptionDisjunction
        originalDescription swappedDescription)
      (implication stableDescriptionNegation stableDescriptionDisjunction
        swappedDescription originalDescription))) at line20
  have line23 := Derivation.star_9_12_same stableDescriptionNegation
    stableDescriptionDisjunction line20
    (star_3_26 stableDescriptionNegation stableDescriptionDisjunction
      (implication stableDescriptionNegation stableDescriptionDisjunction
        originalDescription swappedDescription)
      (implication stableDescriptionNegation stableDescriptionDisjunction
        swappedDescription originalDescription))
  have line24 := star14_composeSame stableDescriptionNegation
    stableDescriptionDisjunction originalDescription originalDescription
    swappedDescription line22 line23
  have continuationMemberStability :
      max continuationOrder uniquenessOrder = continuationOrder :=
    star14_max_eq_left_of_le uniquenessLeContinuation
  let continuationMemberEquality :
      max continuationOrder uniquenessOrder = descriptionBodyOrder :=
    Eq.trans continuationMemberStability descriptionBodyStability.symm
  let continuationBodyNegation := Eq.mp
    (congrArg signature.Negation continuationMemberEquality.symm)
    descriptionBodyNegation
  let continuationBodyDisjunction := Eq.mp
    (congrArg signature.Disjunction continuationMemberEquality.symm)
    descriptionBodyDisjunction
  let continuationExistential : ExistentialVocabulary signature sort
      (max continuationOrder uniquenessOrder) := {
    printed := Eq.mp
      (congrArg (signature.Existential sort) continuationMemberEquality.symm)
      descriptionExistential.printed
    matrixNegation := continuationBodyNegation
    universal := Eq.mp
      (congrArg (signature.Universal sort) continuationMemberEquality.symm)
      descriptionExistential.universal
    outerNegation := Eq.mp
      (congrArg signature.Negation
        (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
          continuationMemberEquality.symm))
      descriptionExistential.outerNegation
  }
  let continuationResultEquality := congrArg
    (fun matrixOrder => bindOrder matrixOrder sort)
    continuationMemberEquality
  have descriptionUniqueness : uniquenessOrder ≤ descriptionBodyOrder :=
    star14_le_max_left _ _
  have descriptionResultUniqueness :
      uniquenessOrder ≤ descriptionResultOrder := by
    rw [descriptionBindStability]
    exact descriptionUniqueness
  let descriptionReverseEquality :
      max uniquenessOrder descriptionResultOrder = descriptionResultOrder :=
    Nat.max_eq_right descriptionResultUniqueness
  let continuationReverseResultEquality :
      bindOrder (max continuationOrder uniquenessOrder) sort =
        max uniquenessOrder descriptionResultOrder :=
    Eq.trans continuationResultEquality descriptionReverseEquality.symm
  let continuationNaturalResultNegation := Eq.mp
    (congrArg signature.Negation descriptionReverseEquality.symm)
    stableDescriptionNegation
  let continuationNaturalResultDisjunction := Eq.mp
    (congrArg signature.Disjunction descriptionReverseEquality.symm)
    stableDescriptionDisjunction
  let coherentContinuationResultNegation := Eq.mp
    (congrArg signature.Negation continuationReverseResultEquality.symm)
    continuationNaturalResultNegation
  let coherentContinuationResultDisjunction := Eq.mp
    (congrArg signature.Disjunction continuationReverseResultEquality.symm)
    continuationNaturalResultDisjunction
  have line25 := star_13_195 continuationIdentity
    continuationIdentityNegation continuationIdentityDisjunction
    continuationBodyNegation continuationBodyDisjunction
    continuationExistential continuationImplicationUniversal
    coherentContinuationResultNegation coherentContinuationResultDisjunction
    uniquenessMatrix b
    continuationReducibility.reducibilityExistential
    continuationReducibility.argumentUniversal
    continuationReducibility.reducibilityNegation
    continuationReducibility.reducibilityIdentityNegation
    continuationReducibility.reducibilityBaseNegation
    continuationReducibility.substitutionResultNegation
    continuationReducibility.reducibilityDisjunction
    continuationReducibility.reducibilityIdentityDisjunction
    continuationReducibility.reducibilityBaseDisjunction
    continuationReducibility.substitutionResultDisjunction
    continuationReducibility.reducibilityScopeUniversal
    continuationReducibility.reducibilityScopeNegation
    continuationReducibility.reducibilityScopeDisjunction
    continuationReducibility.existentialTargetDisjunction
  let continuationRawBody := star_13_195_body continuationIdentity
    continuationIdentityNegation continuationBodyNegation
    continuationBodyDisjunction uniquenessMatrix b
  let continuationRawMember := Formula.sometimes continuationExistential
    continuationRawBody
  let continuationPsiB := uniquenessMatrix.instantiate b
  let continuationMemberPsiEquality := MixedOrder.maxRightAbsorb
    continuationOrder uniquenessOrder
  let continuationMemberPsiDisjunction := Eq.mp
    (congrArg signature.Disjunction continuationMemberPsiEquality.symm)
    continuationBodyDisjunction
  let continuationForwardEquality := congrArg
    (fun matrixOrder => bindOrder matrixOrder sort)
    continuationMemberPsiEquality
  let continuationForward := Eq.mp
    (congrArg (Formula signature real []) continuationForwardEquality)
    (star_10_23_right continuationExistential
      continuationExistential.universal continuationImplicationUniversal
      continuationBodyNegation continuationMemberPsiDisjunction
      continuationRawBody continuationPsiB)
  let continuationReverseEquality := Eq.trans
    (bindOrderMaxLeft uniquenessOrder
      (max continuationOrder uniquenessOrder) sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightLeftAbsorb continuationOrder uniquenessOrder))
  let continuationReverse := star14_normalizedDisjunction
    continuationReverseEquality coherentContinuationResultDisjunction
    (.neg continuationIdentity.negation continuationPsiB)
    continuationRawMember
  change Derivation (.assertion
    (conjunction coherentContinuationResultNegation
      coherentContinuationResultDisjunction
      continuationForward continuationReverse)) at line25
  have line26 := Derivation.star_9_12_same coherentContinuationResultNegation
    coherentContinuationResultDisjunction line25
    (star_3_26 coherentContinuationResultNegation
      coherentContinuationResultDisjunction
      continuationForward continuationReverse)
  have line26Reverse := Derivation.star_9_12_same
    coherentContinuationResultNegation
    coherentContinuationResultDisjunction line25
    (star_3_27 coherentContinuationResultNegation
      coherentContinuationResultDisjunction
      continuationForward continuationReverse)
  have continuationHypothesisNormalization : continuationPsiB = hypothesis := by
    unfold continuationPsiB uniquenessMatrix hypothesis hypothesisMatrix
      hypothesisIdentity conditionUnderCandidate x descriptionCandidate
      hypothesisVariable Formula.instantiate
    rw [substitute_always, star14_matrixEquivalence_substitute,
      star14_conditionUnderCandidate_instantiateClosed,
      star14_identity_substitute]
    cases b <;> rfl
  have continuationRawBodyShape : continuationRawBody =
      mixedConjunction continuationIdentityNegation uniquenessNegation
        continuationBodyNegation continuationBodyDisjunction
        continuationMatrix uniquenessMatrix := by
    have line27 : continuationIdentity.negation = uniquenessNegation := by
      rw [continuationIdentityBaseNegationCoherence]
    unfold continuationRawBody star_13_195_body continuationMatrix
    rw [line27]
  have continuationBodyNormalization :
      Eq.mp (congrArg (Formula signature real [sort])
        continuationMemberEquality) continuationRawBody =
      swappedDescriptionBody := by
    have line27 : MixedOrder.binaryOrderCombine descriptionNegation
        .right .left = continuationMemberEquality := rfl
    rw [continuationRawBodyShape]
    unfold swappedDescriptionBody star14_swappedConjunction
      continuationBodyNegation continuationBodyDisjunction
      descriptionNegation descriptionDisjunction
    rw [line27]
    rfl
  have descriptionMatrixNegationExact :
      descriptionExistential.matrixNegation = descriptionBodyNegation := by
    unfold descriptionExistential descriptionBodyNegation logicalVocabulary
      star_14_15_logicalVocabulary
    rfl
  have continuationExistentialNormalization : continuationExistential =
      ({
        printed := Eq.mp
          (congrArg (signature.Existential sort)
            continuationMemberEquality.symm)
          descriptionExistential.printed
        matrixNegation := Eq.mp
          (congrArg signature.Negation continuationMemberEquality.symm)
          descriptionExistential.matrixNegation
        universal := Eq.mp
          (congrArg (signature.Universal sort)
            continuationMemberEquality.symm)
          descriptionExistential.universal
        outerNegation := Eq.mp
          (congrArg signature.Negation continuationResultEquality.symm)
          descriptionExistential.outerNegation
      } : ExistentialVocabulary signature sort
        (max continuationOrder uniquenessOrder)) := by
    unfold continuationExistential continuationBodyNegation
    rw [descriptionMatrixNegationExact]
  have continuationMemberNormalization :
      Eq.mp (congrArg (Formula signature real [])
        continuationResultEquality) continuationRawMember =
      swappedDescription := by
    unfold continuationRawMember swappedDescription
    rw [continuationExistentialNormalization]
    have line27 := star14_sometimes_castOrder continuationMemberEquality
      descriptionExistential continuationRawBody
    exact Eq.trans line27
      (congrArg (Formula.sometimes descriptionExistential)
        continuationBodyNormalization)
  let naturalContinuationReverse := mixedImplication stableNegation
    continuationNaturalResultDisjunction hypothesis swappedDescription
  have line26ReverseNatural := star14_castAssertionOrder
    continuationReverseResultEquality continuationReverse line26Reverse
  have continuationReverseNaturalNormalization :
      Eq.mp (congrArg (Formula signature real [])
        continuationReverseResultEquality) continuationReverse =
      naturalContinuationReverse := by
    have line27 := star14_normalizedMixedImplication_cast rfl
      continuationResultEquality continuationReverseResultEquality
      continuationReverseEquality stableNegation
      continuationNaturalResultDisjunction continuationPsiB
      continuationRawMember
    unfold continuationReverse star14_normalizedDisjunction
    rw [continuationIdentityBaseNegationCoherence]
    exact Eq.trans line27 (by
      rw [continuationHypothesisNormalization,
        continuationMemberNormalization]
      rfl)
  rw [continuationReverseNaturalNormalization] at line26ReverseNatural
  let descriptionReverse := star14_normalizedDisjunction
    descriptionReverseEquality stableDescriptionDisjunction
    (.neg stableNegation hypothesis) swappedDescription
  have line26ReverseDescription := star14_castAssertionOrder
    descriptionReverseEquality naturalContinuationReverse
    line26ReverseNatural
  have descriptionReverseNormalization :
      Eq.mp (congrArg (Formula signature real []) descriptionReverseEquality)
        naturalContinuationReverse = descriptionReverse := by
    rfl
  rw [descriptionReverseNormalization] at line26ReverseDescription
  have line20Reverse := Derivation.star_9_12_same
    stableDescriptionNegation stableDescriptionDisjunction line20
    (star_3_27 stableDescriptionNegation stableDescriptionDisjunction
      (implication stableDescriptionNegation stableDescriptionDisjunction
        originalDescription swappedDescription)
      (implication stableDescriptionNegation stableDescriptionDisjunction
        swappedDescription originalDescription))
  let descriptionPairEquality := natMaxSelf descriptionResultOrder
  let descriptionPairNegation := Eq.mp
    (congrArg signature.Negation descriptionPairEquality.symm)
    stableDescriptionNegation
  let descriptionPairDisjunction := Eq.mp
    (congrArg signature.Disjunction descriptionPairEquality.symm)
    stableDescriptionDisjunction
  let descriptionReverseFullEquality :
      max uniquenessOrder
          (max descriptionResultOrder descriptionResultOrder) =
        descriptionResultOrder :=
    Eq.trans
      (congrArg (max uniquenessOrder) descriptionPairEquality)
      descriptionReverseEquality
  let reverseNegation : MixedOrder.TernaryNegations signature := {
    pOrder := uniquenessOrder
    qOrder := descriptionResultOrder
    rOrder := descriptionResultOrder
    p := stableNegation
    q := stableDescriptionNegation
    r := stableDescriptionNegation
    pq := continuationNaturalResultNegation
    pr := continuationNaturalResultNegation
    qr := descriptionPairNegation
    pqr := Eq.mp
      (congrArg signature.Negation descriptionReverseFullEquality.symm)
      stableDescriptionNegation
  }
  let reverseDisjunction : MixedOrder.TernaryDisjunctions signature
      reverseNegation := {
    p := stableDisjunction
    q := stableDescriptionDisjunction
    r := stableDescriptionDisjunction
    pq := continuationNaturalResultDisjunction
    pr := continuationNaturalResultDisjunction
    qr := descriptionPairDisjunction
    pqr := Eq.mp
      (congrArg signature.Disjunction descriptionReverseFullEquality.symm)
      stableDescriptionDisjunction
  }
  have line26ReverseInterpretation : Derivation (.assertion
      (MixedOrder.ternaryInterpret reverseNegation reverseDisjunction
        hypothesis swappedDescription originalDescription
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))) := by
    change Derivation (.assertion naturalContinuationReverse)
    exact line26ReverseNatural
  let swappedOriginalRaw := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction hypothesis swappedDescription originalDescription
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR)
  have swappedOriginalNormalization :
      Eq.mp (congrArg (Formula signature real []) descriptionPairEquality)
        swappedOriginalRaw =
      implication stableDescriptionNegation stableDescriptionDisjunction
        swappedDescription originalDescription := by
    change Eq.mp (congrArg (Formula signature real [])
        descriptionPairEquality)
      (MixedOrder.normalizedDisjunction
        (MixedOrder.ternaryOrderCombine reverseNegation .q .r)
        reverseDisjunction.qr
        (.neg reverseNegation.q swappedDescription) originalDescription) = _
    exact star14_normalizedImplication_castOrder rfl rfl
      descriptionPairEquality
      (MixedOrder.ternaryOrderCombine reverseNegation .q .r)
      stableDescriptionNegation stableDescriptionDisjunction
      swappedDescription originalDescription
  have line20ReverseCast := Derivation.castAssertion
    swappedOriginalNormalization line20Reverse
  have line20ReverseInterpretation := star14_uncastAssertionOrder
    descriptionPairEquality swappedOriginalRaw line20ReverseCast
  have line26OriginalNatural := star14_mixedImplicationTransitive
    reverseNegation reverseDisjunction hypothesis swappedDescription
    originalDescription line26ReverseInterpretation
    line20ReverseInterpretation
  let naturalOriginalReverse := mixedImplication stableNegation
    continuationNaturalResultDisjunction hypothesis originalDescription
  change Derivation (.assertion naturalOriginalReverse) at line26OriginalNatural
  let originalReverse := star14_normalizedDisjunction
    descriptionReverseEquality stableDescriptionDisjunction
    (.neg stableNegation hypothesis) originalDescription
  have line26OriginalReverse := star14_castAssertionOrder
    descriptionReverseEquality naturalOriginalReverse line26OriginalNatural
  have originalReverseNormalization :
      Eq.mp (congrArg (Formula signature real []) descriptionReverseEquality)
        naturalOriginalReverse = originalReverse := by
    rfl
  rw [originalReverseNormalization] at line26OriginalReverse
  let descriptionHypothesisEquality :
      max descriptionBodyOrder uniquenessOrder = descriptionBodyOrder :=
    star14_max_eq_left_of_le descriptionUniqueness
  let continuationScopeEquality := congrArg
    (fun matrixOrder => max matrixOrder uniquenessOrder)
    continuationMemberEquality
  let descriptionImplicationUniversal := Eq.mp
    (congrArg (signature.Universal sort) continuationScopeEquality)
    continuationImplicationUniversal
  let descriptionMemberHypothesisDisjunction := Eq.mp
    (congrArg signature.Disjunction continuationScopeEquality)
    continuationMemberPsiDisjunction
  let descriptionScopedForward := Eq.mp
    (congrArg (Formula signature real [])
      (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
        descriptionHypothesisEquality))
    (star_10_23_right descriptionExistential
      descriptionExistential.universal descriptionImplicationUniversal
      descriptionBodyNegation descriptionMemberHypothesisDisjunction
      swappedDescriptionBody hypothesis)
  have line27 := star14_castAssertionOrder continuationResultEquality
    continuationForward line26
  have continuationForwardNormalization :
      Eq.mp (congrArg (Formula signature real [])
        continuationResultEquality) continuationForward =
      descriptionScopedForward := by
    unfold continuationForward descriptionScopedForward
    rw [continuationExistentialNormalization]
    rw [continuationHypothesisNormalization]
    have continuationScopeRoundtrip :
        Eq.mp (congrArg (signature.Universal sort)
          continuationScopeEquality.symm)
          descriptionImplicationUniversal =
        continuationImplicationUniversal := by
      unfold descriptionImplicationUniversal
      exact Eq.trans
        (star14_cast_trans continuationScopeEquality
          continuationScopeEquality.symm
          continuationImplicationUniversal).symm
        (star14_cast_self
          (Eq.trans continuationScopeEquality continuationScopeEquality.symm)
          continuationImplicationUniversal)
    have continuationDisjunctionRoundtrip :
        Eq.mp (congrArg signature.Disjunction
          continuationScopeEquality.symm)
          descriptionMemberHypothesisDisjunction =
        continuationMemberPsiDisjunction := by
      unfold descriptionMemberHypothesisDisjunction
      exact Eq.trans
        (star14_cast_trans continuationScopeEquality
          continuationScopeEquality.symm
          continuationMemberPsiDisjunction).symm
        (star14_cast_self
          (Eq.trans continuationScopeEquality continuationScopeEquality.symm)
          continuationMemberPsiDisjunction)
    have continuationNegationRoundtrip :
        Eq.mp (congrArg signature.Negation
          continuationMemberEquality.symm) descriptionBodyNegation =
        continuationBodyNegation := by
      rfl
    have line28 := star14_star10_23_right_castMatrix
      continuationMemberEquality continuationMemberPsiEquality
      descriptionHypothesisEquality descriptionExistential
      descriptionImplicationUniversal descriptionBodyNegation
      descriptionMemberHypothesisDisjunction continuationRawBody
      continuationPsiB
    rw [continuationScopeRoundtrip, continuationDisjunctionRoundtrip,
      continuationNegationRoundtrip] at line28
    rw [continuationBodyNormalization,
      continuationHypothesisNormalization] at line28
    exact line28
  rw [continuationForwardNormalization] at line27
  let swappedDescriptionNegated := star_9_02
    descriptionExistential.universal descriptionBodyNegation
    swappedDescriptionBody
  have swappedDescriptionNegationDefinition :
      ImplicationNegation signature real descriptionExistential.outerNegation
        swappedDescription swappedDescriptionNegated := by
    unfold swappedDescription swappedDescriptionNegated
    exact ImplicationNegation.star_9_02
      descriptionExistential.outerNegation descriptionExistential
      descriptionExistential.universal descriptionBodyNegation
      swappedDescriptionBody
  have descriptionScopedForwardDefinition :
      ImplicationDisjunction signature real swappedDescriptionNegated
        hypothesis descriptionScopedForward := by
    unfold descriptionScopedForward swappedDescriptionNegated
    apply star14_castImplicationDisjunctionResult
      (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
        descriptionHypothesisEquality)
    unfold star_10_23_right
    exact ImplicationDisjunction.star_9_03
      descriptionExistential.universal descriptionImplicationUniversal
      (.neg descriptionBodyNegation swappedDescriptionBody) hypothesis
      (.disj descriptionMemberHypothesisDisjunction
        (.neg descriptionBodyNegation swappedDescriptionBody)
        (hypothesis.rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01
        descriptionMemberHypothesisDisjunction
        (.neg descriptionBodyNegation swappedDescriptionBody)
        (hypothesis.rename (fun v => .succ v)))
  let descriptionHypothesisResultEquality :
      max descriptionResultOrder uniquenessOrder = descriptionResultOrder :=
    star14_max_eq_left_of_le descriptionResultUniqueness
  let descriptionPairEquality := natMaxSelf descriptionResultOrder
  let descriptionConsequenceEquality :
      max (max descriptionResultOrder descriptionResultOrder)
          (max descriptionResultOrder uniquenessOrder) =
        descriptionResultOrder :=
    natMaxCongr descriptionPairEquality descriptionHypothesisResultEquality
  let descriptionOuterEquality :
      max (max descriptionResultOrder uniquenessOrder)
          (max (max descriptionResultOrder descriptionResultOrder)
            (max descriptionResultOrder uniquenessOrder)) =
        descriptionResultOrder :=
    natMaxCongr descriptionHypothesisResultEquality
      descriptionConsequenceEquality
  let descriptionPairNegation := Eq.mp
    (congrArg signature.Negation descriptionPairEquality.symm)
    stableDescriptionNegation
  let descriptionPairDisjunction := Eq.mp
    (congrArg signature.Disjunction descriptionPairEquality.symm)
    stableDescriptionDisjunction
  let descriptionHypothesisNegation := Eq.mp
    (congrArg signature.Negation
      descriptionHypothesisResultEquality.symm) stableDescriptionNegation
  let descriptionHypothesisDisjunction := Eq.mp
    (congrArg signature.Disjunction
      descriptionHypothesisResultEquality.symm) stableDescriptionDisjunction
  let descriptionConsequenceDisjunction := Eq.mp
    (congrArg signature.Disjunction descriptionConsequenceEquality.symm)
    stableDescriptionDisjunction
  let descriptionOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction descriptionOuterEquality.symm)
    stableDescriptionDisjunction
  let originalHypothesis := star14_normalizedDisjunction
    descriptionHypothesisResultEquality stableDescriptionDisjunction
    (.neg stableDescriptionNegation originalDescription) hypothesis
  have originalHypothesisDefinition : ImplicationDisjunction signature real
      (.neg stableDescriptionNegation originalDescription) hypothesis
      originalHypothesis := by
    unfold originalHypothesis
    apply star14_castImplicationDisjunctionResult
      descriptionHypothesisResultEquality
    exact ImplicationDisjunction.star_1_01
      descriptionHypothesisDisjunction
      (.neg stableDescriptionNegation originalDescription) hypothesis
  have line28 := star14_certifiedSyllogismRight
    stableDescriptionNegation stableDescriptionDisjunction
    originalDescription swappedDescription hypothesis
    (.neg stableDescriptionNegation originalDescription)
    swappedDescriptionNegated
    (implication stableDescriptionNegation stableDescriptionDisjunction
      originalDescription swappedDescription)
    descriptionScopedForward originalHypothesis stableDescriptionNegation
    descriptionExistential.outerNegation descriptionHypothesisDisjunction
    descriptionHypothesisNegation descriptionPairNegation
    descriptionPairDisjunction descriptionHypothesisDisjunction
    descriptionConsequenceDisjunction descriptionOuterDisjunction
    (ImplicationNegation.star_1_01 stableDescriptionNegation
      originalDescription)
    swappedDescriptionNegationDefinition
    (ImplicationDisjunction.star_1_01_same stableDescriptionDisjunction
      (.neg stableDescriptionNegation originalDescription)
      swappedDescription)
    descriptionScopedForwardDefinition originalHypothesisDefinition line27
  have line29 := Derivation.star_9_12_same stableDescriptionNegation
    stableDescriptionDisjunction line24 line28
  have line29Equivalence := star_10_13 stableDescriptionNegation
    stableDescriptionDisjunction originalReverse originalHypothesis
    line26OriginalReverse line29
  change Derivation (.assertion (star_14_202_first_formula
    descriptionExistential identityUniversal conditionIdentity
    identityNegation identityDisjunction continuationIdentity
    continuationIdentityNegation descriptionBodyNegation
    descriptionBodyDisjunction condition b)) at line29Equivalence
  let stableFinal := star14_normalizedDisjunction
    descriptionHypothesisResultEquality stableDescriptionDisjunction
    (.neg stableDescriptionNegation originalDescription)
    stableApplicationConclusion
  have stableFinalDefinition : ImplicationDisjunction signature real
      (.neg stableDescriptionNegation originalDescription)
      stableApplicationConclusion stableFinal := by
    unfold stableFinal
    apply star14_castImplicationDisjunctionResult
      descriptionHypothesisResultEquality
    exact ImplicationDisjunction.star_1_01
      descriptionHypothesisDisjunction
      (.neg stableDescriptionNegation originalDescription)
      stableApplicationConclusion
  let stablePairEquality := natMaxSelf uniquenessOrder
  let stablePairNegation := Eq.mp
    (congrArg signature.Negation stablePairEquality.symm) stableNegation
  let stablePairDisjunction := Eq.mp
    (congrArg signature.Disjunction stablePairEquality.symm)
    stableDisjunction
  let finalConsequenceEquality :
      max (max descriptionResultOrder uniquenessOrder)
          (max descriptionResultOrder uniquenessOrder) =
        descriptionResultOrder :=
    natMaxCongr descriptionHypothesisResultEquality
      descriptionHypothesisResultEquality
  let finalPrimitiveOuterEquality :
      max (max uniquenessOrder uniquenessOrder)
          (max (max descriptionResultOrder uniquenessOrder)
            (max descriptionResultOrder uniquenessOrder)) =
        descriptionResultOrder :=
    Eq.trans
      (congrArg
        (fun leftOrder => max leftOrder
          (max (max descriptionResultOrder uniquenessOrder)
            (max descriptionResultOrder uniquenessOrder)))
        stablePairEquality)
      (Eq.trans
        (congrArg (max uniquenessOrder) finalConsequenceEquality)
        (Nat.max_eq_right descriptionResultUniqueness))
  let finalOuterEquality :
      max uniquenessOrder
          (max descriptionResultOrder descriptionResultOrder) =
        descriptionResultOrder :=
    Eq.trans (congrArg (max uniquenessOrder) descriptionPairEquality)
      (Nat.max_eq_right descriptionResultUniqueness)
  let finalConsequenceDisjunction := Eq.mp
    (congrArg signature.Disjunction finalConsequenceEquality.symm)
    stableDescriptionDisjunction
  let finalPrimitiveOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction finalPrimitiveOuterEquality.symm)
    stableDescriptionDisjunction
  let finalOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction finalOuterEquality.symm)
    stableDescriptionDisjunction
  have line30 := star14_composeCertified stableDescriptionNegation
    stableDescriptionDisjunction originalDescription hypothesis
    stableApplicationConclusion
    (.neg stableDescriptionNegation originalDescription)
    (.neg stableNegation hypothesis) originalHypothesis
    (implication stableNegation stableDisjunction hypothesis
      stableApplicationConclusion)
    stableFinal stableDescriptionNegation stableNegation
    stablePairDisjunction stablePairNegation descriptionHypothesisNegation
    descriptionHypothesisDisjunction descriptionHypothesisDisjunction
    finalConsequenceDisjunction finalPrimitiveOuterDisjunction
    stableDescriptionNegation descriptionPairDisjunction stableNegation
    finalOuterDisjunction
    (ImplicationNegation.star_1_01 stableDescriptionNegation
      originalDescription)
    (ImplicationNegation.star_1_01 stableNegation hypothesis)
    originalHypothesisDefinition
    (ImplicationDisjunction.star_1_01_same stableDisjunction
      (.neg stableNegation hypothesis) stableApplicationConclusion)
    stableFinalDefinition line29 line18Cast
  have applicationResultLeDescription :
      applicationResultOrder ≤ descriptionResultOrder := by
    exact Eq.mp
      (congrArg (fun order => order ≤ descriptionResultOrder)
        applicationResultStability.symm)
      descriptionResultUniqueness
  let finalResultCollapse :
      max descriptionResultOrder applicationResultOrder =
        descriptionResultOrder :=
    star14_max_eq_left_of_le applicationResultLeDescription
  have finalDisjunctionNormalization :
      Eq.mp (congrArg signature.Disjunction finalResultCollapse)
        finalDisjunction = stableDescriptionDisjunction := by
    let logicalFinalCollapse :
        max descriptionResultOrder applicationResultOrder =
          descriptionBodyOrder :=
      Eq.trans
        (congrArg
          (fun leftOrder => max leftOrder applicationResultOrder)
          descriptionBindStability)
        (Eq.trans
          (congrArg (max descriptionBodyOrder) applicationResultStability)
          (star14_max_eq_left_of_le (star14_le_max_left uniquenessOrder
            continuationOrder)))
    unfold finalDisjunction stableDescriptionDisjunction logicalVocabulary
      star_14_15_logicalVocabulary
    exact (star14_cast_trans logicalFinalCollapse.symm
      finalResultCollapse descriptionBodyDisjunction).symm
  have stableApplicationRoundtrip :
      Eq.mp (congrArg (Formula signature real [])
        applicationResultStability.symm) stableApplicationConclusion =
      applicationConclusion := by
    unfold stableApplicationConclusion
    exact Eq.trans
      (star14_cast_trans applicationResultStability
        applicationResultStability.symm applicationConclusion).symm
      (star14_cast_self
        (Eq.trans applicationResultStability applicationResultStability.symm)
        applicationConclusion)
  have stableFinalNormalization :
      Eq.mp (congrArg (Formula signature real [])
        finalResultCollapse.symm) stableFinal =
      mixedImplication stableDescriptionNegation finalDisjunction
        originalDescription applicationConclusion := by
    unfold stableFinal
    have line31 := star14_normalizedMixedImplication_cast rfl
      applicationResultStability.symm finalResultCollapse.symm
      descriptionHypothesisResultEquality stableDescriptionNegation
      finalDisjunction originalDescription stableApplicationConclusion
    rw [finalDisjunctionNormalization,
      stableApplicationRoundtrip] at line31
    exact line31
  have line31 := star14_castAssertionOrder finalResultCollapse.symm
    stableFinal line30
  rw [stableFinalNormalization] at line31
  rw [← descriptionOuterNegationSource] at line31
  change Derivation (.assertion
    (mixedImplication descriptionExistential.outerNegation finalDisjunction
      originalDescription applicationConclusion)) at line31
  exact ⟨line31, line29Equivalence, line242⟩

private def star14_15_continuationIdentity
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentityUniversal : signature.Universal
      (.function [sort]
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) 0)
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)) :
    IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0 := {
  negation := Eq.mp (congrArg signature.Negation
    (star14_identityOrderStable conditionOrder sort).symm) identityNegation
  disjunction := Eq.mp (congrArg signature.Disjunction
    (star14_identityOrderStable conditionOrder sort).symm) identityDisjunction
  universal := continuationIdentityUniversal
}

/-- ✱14·15, following the two printed description expansions and the
substitution theorems ✱13·195 and ✱13·192.
`demonstration_provenance: follows-printed`. -/
theorem star_14_15
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentityUniversal : signature.Universal
      (.function [sort]
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) 0)
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort))
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityDisjunction : signature.Disjunction
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationImplicationUniversal : signature.Universal sort
      (max
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort))
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)))
    (continuationResultNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (continuationResultDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort)
    (descriptionPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (applicationPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (conditionReducibility : Star14ReducibilityVocabulary signature sort
      conditionOrder)
    (continuationReducibility : Star14ReducibilityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)) :
    let logicalVocabulary := star_14_15_logicalVocabulary identityUniversal
      identityNegation identityDisjunction continuationIdentityNegation
      continuationIdentityDisjunction descriptionPrinted descriptionUniversal
      applicationPrinted applicationUniversal
    let continuationIdentity := star14_15_continuationIdentity
      identityNegation identityDisjunction continuationIdentityUniversal
    Derivation (star_14_15_reading logicalVocabulary.descriptionExistential
      identityUniversal conditionIdentity identityNegation identityDisjunction
      continuationIdentity continuationIdentityNegation
      logicalVocabulary.descriptionBodyNegation
      logicalVocabulary.descriptionBodyDisjunction
      logicalVocabulary.applicationExistential
      logicalVocabulary.applicationBodyDisjunction
      applicationImplicationUniversal
      logicalVocabulary.applicationResultDisjunction
      logicalVocabulary.finalDisjunction condition psi b).parsed := by
  dsimp only
  let logicalVocabulary := star_14_15_logicalVocabulary identityUniversal
    identityNegation identityDisjunction continuationIdentityNegation
    continuationIdentityDisjunction descriptionPrinted descriptionUniversal
    applicationPrinted applicationUniversal
  let continuationIdentity := star14_15_continuationIdentity
    identityNegation identityDisjunction continuationIdentityUniversal
  have line1 := star14_15_core logicalVocabulary.descriptionExistential
    identityUniversal conditionIdentity identityNegation identityDisjunction
    continuationIdentity continuationIdentityNegation
    continuationIdentityDisjunction rfl
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction
    continuationImplicationUniversal continuationResultNegation
    continuationResultDisjunction logicalVocabulary.applicationExistential
    logicalVocabulary.applicationBodyDisjunction
    applicationImplicationUniversal
    logicalVocabulary.applicationResultDisjunction
    logicalVocabulary.finalDisjunction condition psi b descriptionPrinted
    descriptionUniversal applicationPrinted applicationUniversal rfl rfl rfl
    rfl rfl rfl rfl conditionReducibility continuationReducibility
  exact line1.1

#print axioms star_14_15

private theorem star14_uniquenessReverseEquivalence
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (b : Term signature real [] sort)
    (reducibility : Star14ReducibilityVocabulary signature sort
      conditionOrder) :
    let identityOrder := bindOrder conditionOrder
      (.function [sort] conditionOrder 0)
    let uniquenessOrder := bindOrder identityOrder sort
    let identityStability := star14_identityOrderStable conditionOrder sort
    let stableNegation := Eq.mp (congrArg signature.Negation
      identityStability.symm) identityNegation
    let stableDisjunction := Eq.mp (congrArg signature.Disjunction
      identityStability.symm) identityDisjunction
    let x : Term signature real [sort] sort := .apparent .zero
    let left := Formula.always identityUniversal
      (equivalence identityNegation identityDisjunction condition
        (star_13_01 identity x b.weaken))
    let right := Formula.always identityUniversal
      (equivalence identityNegation identityDisjunction condition
        (star_13_01 identity b.weaken x))
    Derivation (.assertion
      (star_4_01 stableNegation stableDisjunction left right)) := by
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) identityStability.symm)
    identityUniversal
  let stableNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let stableDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) identityDisjunction
  let x : Term signature real [sort] sort := .apparent .zero
  let rawLeft := equivalence identityNegation identityDisjunction condition
    (star_13_01 identity x b.weaken)
  let rawRight := equivalence identityNegation identityDisjunction condition
    (star_13_01 identity b.weaken x)
  let stableLeft := Eq.mp (congrArg (Formula signature real [sort])
    identityStability.symm) rawLeft
  let stableRight := Eq.mp (congrArg (Formula signature real [sort])
    identityStability.symm) rawRight
  let candidate : Term signature (sort :: real) [] sort := .real .zero
  let bValue := b.weakenReal (fresh := sort)
  let conditionAt := condition.weakenReal.instantiate candidate
  let identityToB := star_13_01 identity candidate bValue
  let identityFromB := star_13_01 identity bValue candidate
  let identityBaseEquality : max identityOrder conditionOrder =
      identityOrder := by
    unfold identityOrder bindOrder
    exact star14_max_eq_left_of_le
      (star14_le_max_left conditionOrder
        (Nat.succ (RSort.height (.function [sort] conditionOrder 0))))
  let identityBaseNegation := Eq.mp
    (congrArg signature.Negation identityBaseEquality.symm) identityNegation
  let identityBaseDisjunction := Eq.mp
    (congrArg signature.Disjunction identityBaseEquality.symm)
    identityDisjunction
  have line1 := star_13_16 identity reducibility.reducibilityExistential
    reducibility.argumentUniversal identityNegation identityDisjunction
    identityBaseDisjunction reducibility.reducibilityNegation
    reducibility.reducibilityIdentityNegation
    reducibility.reducibilityBaseNegation identityBaseNegation
    reducibility.substitutionResultNegation
    reducibility.reducibilityDisjunction
    reducibility.reducibilityIdentityDisjunction
    reducibility.reducibilityBaseDisjunction
    reducibility.substitutionResultDisjunction
    reducibility.reducibilityScopeUniversal
    reducibility.reducibilityScopeNegation
    reducibility.reducibilityScopeDisjunction
    reducibility.existentialTargetDisjunction
    reducibility.equivalenceScopeUniversal
    reducibility.symmetryScopeUniversal reducibility.scopedNegation
    reducibility.scopedConsequenceDisjunction
    reducibility.scopedOuterDisjunction candidate bValue
  have line2 := star14_equivalenceSubstituteRight identityNegation
    identityDisjunction identityToB identityFromB conditionAt line1
  have rawLeftAt : rawLeft.weakenReal.instantiate candidate =
      star_4_01 identityNegation identityDisjunction conditionAt identityToB := by
    unfold rawLeft conditionAt identityToB
    rw [star14_matrixEquivalence_weakenReal, star14_identity_weakenReal]
    unfold Formula.instantiate
    rw [star14_matrixEquivalence_substitute, star14_identity_substitute]
    cases b <;> rfl
  have rawRightAt : rawRight.weakenReal.instantiate candidate =
      star_4_01 identityNegation identityDisjunction conditionAt
        identityFromB := by
    unfold rawRight conditionAt identityFromB
    rw [star14_matrixEquivalence_weakenReal, star14_identity_weakenReal]
    unfold Formula.instantiate
    rw [star14_matrixEquivalence_substitute, star14_identity_substitute]
    cases b <;> rfl
  rw [← rawLeftAt, ← rawRightAt] at line2
  have line3 := star14_castAssertionOrder identityStability.symm
    (star_4_01 identityNegation identityDisjunction
      (rawLeft.weakenReal.instantiate candidate)
      (rawRight.weakenReal.instantiate candidate)) line2
  have stableLeftAt : stableLeft.weakenReal.instantiate candidate =
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        identityStability.symm)
        (rawLeft.weakenReal.instantiate candidate) := by
    unfold stableLeft Formula.instantiate
    rw [Formula.weakenReal_cast, Formula.substitute_cast]
    exact identityStability.symm
    exact identityStability.symm
  have stableRightAt : stableRight.weakenReal.instantiate candidate =
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        identityStability.symm)
        (rawRight.weakenReal.instantiate candidate) := by
    unfold stableRight Formula.instantiate
    rw [Formula.weakenReal_cast, Formula.substitute_cast]
    exact identityStability.symm
    exact identityStability.symm
  have identityNegationSource : identityNegation =
      Eq.mp (congrArg signature.Negation identityStability)
        stableNegation := by
    unfold stableNegation
    exact Eq.trans
      (star14_cast_self
        (Eq.trans identityStability.symm identityStability)
        identityNegation).symm
      (star14_cast_trans identityStability.symm identityStability
        identityNegation)
  have identityDisjunctionSource : identityDisjunction =
      Eq.mp (congrArg signature.Disjunction identityStability)
        stableDisjunction := by
    unfold stableDisjunction
    exact Eq.trans
      (star14_cast_self
        (Eq.trans identityStability.symm identityStability)
        identityDisjunction).symm
      (star14_cast_trans identityStability.symm identityStability
        identityDisjunction)
  have line3Normalization :
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        identityStability.symm)
        (star_4_01 identityNegation identityDisjunction
          (rawLeft.weakenReal.instantiate candidate)
          (rawRight.weakenReal.instantiate candidate)) =
      star_4_01 stableNegation stableDisjunction
        (stableLeft.weakenReal.instantiate candidate)
        (stableRight.weakenReal.instantiate candidate) := by
    rw [identityNegationSource, identityDisjunctionSource]
    have line4 := star14_equivalence_castOrder identityStability.symm
      stableNegation stableDisjunction
      (rawLeft.weakenReal.instantiate candidate)
      (rawRight.weakenReal.instantiate candidate)
    rw [stableLeftAt, stableRightAt]
    unfold star_4_01
    exact line4
  rw [line3Normalization] at line3
  have line4 := star14_liftSaturatedUniversalEquivalence stableUniversal
    stableNegation stableDisjunction stableLeft stableRight line3
  let stableBind := star14_bindOrderStable identityOrder sort
  have stableLeftShape : stableLeft =
      equivalence stableNegation stableDisjunction
        (Eq.mp (congrArg (Formula signature real [sort])
          identityStability.symm) condition)
        (Eq.mp (congrArg (Formula signature real [sort])
          identityStability.symm) (star_13_01 identity x b.weaken)) := by
    unfold stableLeft rawLeft
    rw [identityNegationSource, identityDisjunctionSource]
    exact star14_equivalence_castOrder identityStability.symm
      stableNegation stableDisjunction condition
      (star_13_01 identity x b.weaken)
  have stableRightShape : stableRight =
      equivalence stableNegation stableDisjunction
        (Eq.mp (congrArg (Formula signature real [sort])
          identityStability.symm) condition)
        (Eq.mp (congrArg (Formula signature real [sort])
          identityStability.symm) (star_13_01 identity b.weaken x)) := by
    unfold stableRight rawRight
    rw [identityNegationSource, identityDisjunctionSource]
    exact star14_equivalence_castOrder identityStability.symm
      stableNegation stableDisjunction condition
      (star_13_01 identity b.weaken x)
  have leftNormalization : star14_saturatedUniversal stableUniversal
      stableLeft = Formula.always identityUniversal rawLeft := by
    rw [stableLeftShape]
    have line5 := star14_saturatedEquivalenceScope_cast identityStability rfl
      stableBind identityUniversal identityNegation identityDisjunction
      condition (star_13_01 identity x b.weaken)
    unfold rawLeft
    exact line5
  have rightNormalization : star14_saturatedUniversal stableUniversal
      stableRight = Formula.always identityUniversal rawRight := by
    rw [stableRightShape]
    have line5 := star14_saturatedEquivalenceScope_cast identityStability rfl
      stableBind identityUniversal identityNegation identityDisjunction
      condition (star_13_01 identity b.weaken x)
    unfold rawRight
    exact line5
  rw [leftNormalization, rightNormalization] at line4
  exact line4

private theorem star14_descriptionReverseEquivalence
    (descriptionExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentity : IdentityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityDisjunction : signature.Disjunction
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityBaseNegationCoherence :
      continuationIdentity.negation = Eq.mp
        (congrArg signature.Negation
          (star14_identityOrderStable conditionOrder sort).symm)
        identityNegation)
    (descriptionBodyNegation : signature.Negation
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionMatrixNegationCoherence :
      descriptionExistential.matrixNegation = descriptionBodyNegation)
    (descriptionOuterNegationCoherence :
      descriptionExistential.outerNegation = Eq.mp
        (congrArg signature.Negation
          (star14_descriptionBindOrderStable conditionOrder sort).symm)
        descriptionBodyNegation)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (b : Term signature real [] sort)
    (reducibility : Star14ReducibilityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)) :
    let identityStability := star14_identityOrderStable conditionOrder sort
    let uniquenessNegation := Eq.mp (congrArg signature.Negation
      identityStability.symm) identityNegation
    let continuationOrder := bindOrder
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
      (.function [sort]
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) 0)
    let descriptionBodyOrder := max
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) continuationOrder
    let descriptionResultOrder := bindOrder descriptionBodyOrder sort
    let descriptionHeight : Nat.succ sort.height ≤ descriptionBodyOrder :=
      Nat.le_trans (star14_le_max_right
        (bindOrder conditionOrder (.function [sort] conditionOrder 0))
        (Nat.succ sort.height)) (star14_le_max_left _ _)
    let descriptionBindStability : descriptionResultOrder =
        descriptionBodyOrder :=
      star14_descriptionBindOrderStable conditionOrder sort
    let resultNegation := Eq.mp (congrArg signature.Negation
      descriptionBindStability.symm) descriptionBodyNegation
    let resultDisjunction := Eq.mp (congrArg signature.Disjunction
      descriptionBindStability.symm) descriptionBodyDisjunction
    let left := star_14_descriptionIdentity descriptionExistential
      identityUniversal conditionIdentity identityNegation identityDisjunction
      uniquenessNegation continuationIdentity continuationIdentityNegation
      descriptionBodyNegation descriptionBodyDisjunction condition b
    let x : Term signature real [sort] sort := .apparent .zero
    let reverseContinuation := star_13_01 continuationIdentity b.weaken x
    let right := star_14_01 descriptionExistential identityUniversal
      conditionIdentity identityNegation identityDisjunction
      uniquenessNegation continuationIdentityNegation descriptionBodyNegation
      descriptionBodyDisjunction condition reverseContinuation
    Derivation (.assertion
      (star_4_01 resultNegation resultDisjunction left right)) := by
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let uniquenessDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) identityDisjunction
  let continuationOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionBodyOrder := max uniquenessOrder continuationOrder
  let descriptionResultOrder := bindOrder descriptionBodyOrder sort
  let uniquenessMatrix := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction
      (condition.rename (liftRenaming (fun v => .succ v)))
      (star_13_01 conditionIdentity (.apparent (.zero : Var [sort, sort] sort))
        (.apparent (.succ .zero))))
  let x : Term signature real [sort] sort := .apparent .zero
  let forwardContinuation := star_13_01 continuationIdentity x b.weaken
  let reverseContinuation := star_13_01 continuationIdentity b.weaken x
  let originalBody := mixedConjunction uniquenessNegation
    continuationIdentityNegation descriptionBodyNegation
    descriptionBodyDisjunction uniquenessMatrix forwardContinuation
  let reverseBody := mixedConjunction uniquenessNegation
    continuationIdentityNegation descriptionBodyNegation
    descriptionBodyDisjunction uniquenessMatrix reverseContinuation
  let candidate : Term signature (sort :: real) [] sort := .real .zero
  let bValue := b.weakenReal (fresh := sort)
  let uniquenessAt := uniquenessMatrix.weakenReal.instantiate candidate
  let forwardAt := star_13_01 continuationIdentity candidate bValue
  let reverseAt := star_13_01 continuationIdentity bValue candidate
  let uniquenessLeContinuation : uniquenessOrder ≤ continuationOrder := by
    unfold continuationOrder bindOrder
    exact star14_le_max_left _ _
  let descriptionBodyStability : descriptionBodyOrder = continuationOrder :=
    Nat.max_eq_right uniquenessLeContinuation
  let continuationMemberEquality :
      max continuationOrder uniquenessOrder = descriptionBodyOrder :=
    Eq.trans (star14_max_eq_left_of_le uniquenessLeContinuation)
      descriptionBodyStability.symm
  let continuationBodyNegation := Eq.mp
    (congrArg signature.Negation continuationMemberEquality.symm)
    descriptionBodyNegation
  let continuationBodyDisjunction := Eq.mp
    (congrArg signature.Disjunction continuationMemberEquality.symm)
    descriptionBodyDisjunction
  have line1 := star_13_16 continuationIdentity
    reducibility.reducibilityExistential reducibility.argumentUniversal
    continuationIdentityNegation continuationIdentityDisjunction
    continuationBodyDisjunction reducibility.reducibilityNegation
    reducibility.reducibilityIdentityNegation
    reducibility.reducibilityBaseNegation continuationBodyNegation
    reducibility.substitutionResultNegation
    reducibility.reducibilityDisjunction
    reducibility.reducibilityIdentityDisjunction
    reducibility.reducibilityBaseDisjunction
    reducibility.substitutionResultDisjunction
    reducibility.reducibilityScopeUniversal
    reducibility.reducibilityScopeNegation
    reducibility.reducibilityScopeDisjunction
    reducibility.existentialTargetDisjunction
    reducibility.equivalenceScopeUniversal
    reducibility.symmetryScopeUniversal reducibility.scopedNegation
    reducibility.scopedConsequenceDisjunction
    reducibility.scopedOuterDisjunction candidate bValue
  let outerEquality := MixedOrder.maxLeftAbsorb continuationOrder
    uniquenessOrder
  let outerDisjunction := Eq.mp
    (congrArg signature.Disjunction outerEquality.symm)
    continuationBodyDisjunction
  have line2a := star14_mixedConjunctionEquivalentRightDirect
    continuationIdentityNegation continuationIdentityDisjunction
    uniquenessNegation uniquenessDisjunction continuationBodyNegation
    continuationBodyDisjunction forwardAt reverseAt uniquenessAt
  have line2Raw := Derivation.star_9_12 continuationIdentityNegation
    outerDisjunction line1 line2a
  let negation : MixedOrder.BinaryNegations signature := {
    leftOrder := uniquenessOrder
    rightOrder := continuationOrder
    left := uniquenessNegation
    right := continuationIdentityNegation
    both := descriptionBodyNegation
  }
  let disjunction : MixedOrder.BinaryDisjunctions signature negation := {
    left := uniquenessDisjunction
    right := continuationIdentityDisjunction
    both := descriptionBodyDisjunction
  }
  have line2 := star14_castAssertionOrder continuationMemberEquality
    (star_4_01 continuationBodyNegation continuationBodyDisjunction
      (mixedConjunction continuationIdentityNegation uniquenessNegation
        continuationBodyNegation continuationBodyDisjunction
        forwardAt uniquenessAt)
      (mixedConjunction continuationIdentityNegation uniquenessNegation
        continuationBodyNegation continuationBodyDisjunction
        reverseAt uniquenessAt)) line2Raw
  have line2Normalization :
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        continuationMemberEquality)
        (star_4_01 continuationBodyNegation continuationBodyDisjunction
          (mixedConjunction continuationIdentityNegation uniquenessNegation
            continuationBodyNegation continuationBodyDisjunction
            forwardAt uniquenessAt)
          (mixedConjunction continuationIdentityNegation uniquenessNegation
            continuationBodyNegation continuationBodyDisjunction
            reverseAt uniquenessAt)) =
      star_4_01 descriptionBodyNegation descriptionBodyDisjunction
        (star14_swappedConjunction negation disjunction uniquenessAt forwardAt)
        (star14_swappedConjunction negation disjunction uniquenessAt reverseAt) := by
    have line3 := star14_equivalence_castOrder continuationMemberEquality
      descriptionBodyNegation descriptionBodyDisjunction
      (mixedConjunction continuationIdentityNegation uniquenessNegation
        continuationBodyNegation continuationBodyDisjunction
        forwardAt uniquenessAt)
      (mixedConjunction continuationIdentityNegation uniquenessNegation
        continuationBodyNegation continuationBodyDisjunction
        reverseAt uniquenessAt)
    unfold star14_swappedConjunction
    unfold star_4_01
    exact line3
  rw [line2Normalization] at line2
  have line3 := star14_commuteEquivalenceNormalized negation disjunction
    uniquenessAt forwardAt
  rw [star14_binaryLeft_eq, star14_binaryRight_eq] at line3
  have line4Raw := star14_commuteEquivalenceNormalized negation disjunction
    uniquenessAt reverseAt
  rw [star14_binaryLeft_eq, star14_binaryRight_eq] at line4Raw
  have line4Symmetry := star_4_21 descriptionBodyNegation
    descriptionBodyDisjunction
    (mixedConjunction uniquenessNegation continuationIdentityNegation
      descriptionBodyNegation descriptionBodyDisjunction
      uniquenessAt reverseAt)
    (star14_swappedConjunction negation disjunction uniquenessAt reverseAt)
  have line4Implication := Derivation.star_9_12_same
    descriptionBodyNegation descriptionBodyDisjunction line4Symmetry
    (star_3_26 descriptionBodyNegation descriptionBodyDisjunction
      (implication descriptionBodyNegation descriptionBodyDisjunction
        (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
          (mixedConjunction uniquenessNegation continuationIdentityNegation
            descriptionBodyNegation descriptionBodyDisjunction
            uniquenessAt reverseAt)
          (star14_swappedConjunction negation disjunction uniquenessAt reverseAt))
        (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
          (star14_swappedConjunction negation disjunction uniquenessAt reverseAt)
          (mixedConjunction uniquenessNegation continuationIdentityNegation
            descriptionBodyNegation descriptionBodyDisjunction
            uniquenessAt reverseAt)))
      (implication descriptionBodyNegation descriptionBodyDisjunction
        (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
          (star14_swappedConjunction negation disjunction uniquenessAt reverseAt)
          (mixedConjunction uniquenessNegation continuationIdentityNegation
            descriptionBodyNegation descriptionBodyDisjunction
            uniquenessAt reverseAt))
        (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
          (mixedConjunction uniquenessNegation continuationIdentityNegation
            descriptionBodyNegation descriptionBodyDisjunction
            uniquenessAt reverseAt)
          (star14_swappedConjunction negation disjunction uniquenessAt reverseAt))))
  have line4 := Derivation.star_9_12_same descriptionBodyNegation
    descriptionBodyDisjunction line4Raw line4Implication
  have line5 := star14_equivalenceTransitiveSame descriptionBodyNegation
    descriptionBodyDisjunction
    (mixedConjunction uniquenessNegation continuationIdentityNegation
      descriptionBodyNegation descriptionBodyDisjunction uniquenessAt forwardAt)
    (star14_swappedConjunction negation disjunction uniquenessAt forwardAt)
    (star14_swappedConjunction negation disjunction uniquenessAt reverseAt)
    line3 line2
  have line6 := star14_equivalenceTransitiveSame descriptionBodyNegation
    descriptionBodyDisjunction
    (mixedConjunction uniquenessNegation continuationIdentityNegation
      descriptionBodyNegation descriptionBodyDisjunction uniquenessAt forwardAt)
    (star14_swappedConjunction negation disjunction uniquenessAt reverseAt)
    (mixedConjunction uniquenessNegation continuationIdentityNegation
      descriptionBodyNegation descriptionBodyDisjunction uniquenessAt reverseAt)
    line5 line4
  have originalAt : originalBody.weakenReal.instantiate candidate =
      mixedConjunction uniquenessNegation continuationIdentityNegation
        descriptionBodyNegation descriptionBodyDisjunction
        uniquenessAt forwardAt := by
    unfold originalBody uniquenessAt forwardAt
    rw [star14_mixedConjunction_weakenReal, star14_identity_weakenReal]
    unfold Formula.instantiate
    rw [star14_mixedConjunction_substitute, star14_identity_substitute]
    cases b <;> rfl
  have reverseAtShape : reverseBody.weakenReal.instantiate candidate =
      mixedConjunction uniquenessNegation continuationIdentityNegation
        descriptionBodyNegation descriptionBodyDisjunction
        uniquenessAt reverseAt := by
    unfold reverseBody uniquenessAt reverseAt
    rw [star14_mixedConjunction_weakenReal, star14_identity_weakenReal]
    unfold Formula.instantiate
    rw [star14_mixedConjunction_substitute, star14_identity_substitute]
    cases b <;> rfl
  rw [← originalAt, ← reverseAtShape] at line6
  let uniquenessHeight : Nat.succ sort.height ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_right _ _
  let descriptionHeight : Nat.succ sort.height ≤ descriptionBodyOrder :=
    Nat.le_trans uniquenessHeight (star14_le_max_left _ _)
  let descriptionBindStability : descriptionResultOrder =
      descriptionBodyOrder :=
    star14_descriptionBindOrderStable conditionOrder sort
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) descriptionBindStability.symm)
    descriptionExistential.universal
  let stableNegation := Eq.mp (congrArg signature.Negation
    descriptionBindStability.symm) descriptionBodyNegation
  let stableDisjunction := Eq.mp (congrArg signature.Disjunction
    descriptionBindStability.symm) descriptionBodyDisjunction
  let stableOriginalBody := Eq.mp (congrArg
    (Formula signature real [sort]) descriptionBindStability.symm) originalBody
  let stableReverseBody := Eq.mp (congrArg
    (Formula signature real [sort]) descriptionBindStability.symm) reverseBody
  have line7 := star14_castAssertionOrder descriptionBindStability.symm
    (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
      (originalBody.weakenReal.instantiate candidate)
      (reverseBody.weakenReal.instantiate candidate)) line6
  have line7Normalization :
      Eq.mp (congrArg (Formula signature (sort :: real) [])
        descriptionBindStability.symm)
        (star_4_01 descriptionBodyNegation descriptionBodyDisjunction
          (originalBody.weakenReal.instantiate candidate)
          (reverseBody.weakenReal.instantiate candidate)) =
      star_4_01 stableNegation stableDisjunction
        (stableOriginalBody.weakenReal.instantiate candidate)
        (stableReverseBody.weakenReal.instantiate candidate) := by
    unfold stableOriginalBody stableReverseBody
    have descriptionNegationSource : descriptionBodyNegation =
        Eq.mp (congrArg signature.Negation descriptionBindStability)
          stableNegation := by
      unfold stableNegation
      exact Eq.trans
        (star14_cast_self
          (Eq.trans descriptionBindStability.symm descriptionBindStability)
          descriptionBodyNegation).symm
        (star14_cast_trans descriptionBindStability.symm
          descriptionBindStability descriptionBodyNegation)
    have descriptionDisjunctionSource : descriptionBodyDisjunction =
        Eq.mp (congrArg signature.Disjunction descriptionBindStability)
          stableDisjunction := by
      unfold stableDisjunction
      exact Eq.trans
        (star14_cast_self
          (Eq.trans descriptionBindStability.symm descriptionBindStability)
          descriptionBodyDisjunction).symm
        (star14_cast_trans descriptionBindStability.symm
          descriptionBindStability descriptionBodyDisjunction)
    rw [descriptionNegationSource, descriptionDisjunctionSource]
    unfold star_4_01
    rw [star14_conjunction_castOrder, star14_implication_castOrder,
      star14_implication_castOrder, Formula.weakenReal_cast,
      Formula.weakenReal_cast]
    unfold Formula.instantiate
    rw [Formula.substitute_cast, Formula.substitute_cast]
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
    exact descriptionBindStability.symm
  rw [line7Normalization] at line7
  have line8 := star14_liftSaturatedExistentialEquivalence stableUniversal
    stableNegation stableDisjunction stableOriginalBody stableReverseBody line7
  let left := Formula.sometimes descriptionExistential originalBody
  let right := Formula.sometimes descriptionExistential reverseBody
  have matrixNegationSource : descriptionExistential.matrixNegation =
      Eq.mp (congrArg signature.Negation descriptionBindStability)
        stableNegation := by
    rw [descriptionMatrixNegationCoherence]
    unfold stableNegation
    exact Eq.trans
      (star14_cast_self
        (Eq.trans descriptionBindStability.symm descriptionBindStability)
        descriptionBodyNegation).symm
      (star14_cast_trans descriptionBindStability.symm
        descriptionBindStability descriptionBodyNegation)
  have universalSource : descriptionExistential.universal =
      Eq.mp (congrArg (signature.Universal sort) descriptionBindStability)
        stableUniversal := by
    unfold stableUniversal
    exact Eq.trans
      (star14_cast_self
        (Eq.trans descriptionBindStability.symm descriptionBindStability)
        descriptionExistential.universal).symm
      (star14_cast_trans descriptionBindStability.symm
        descriptionBindStability descriptionExistential.universal)
  have outerNegationSource : descriptionExistential.outerNegation =
      stableNegation := by
    unfold stableNegation
    exact descriptionOuterNegationCoherence
  let secondBindStability : bindOrder descriptionResultOrder sort =
      descriptionResultOrder := Eq.trans
    (congrArg (fun order => bindOrder order sort) descriptionBindStability)
    (Eq.trans descriptionBindStability descriptionBindStability.symm)
  have leftNormalization : left = star14_saturatedExistential stableUniversal
      stableNegation stableOriginalBody := by
    unfold left Formula.sometimes
    rw [matrixNegationSource, universalSource, outerNegationSource]
    unfold stableOriginalBody
    exact star14_saturatedExistential_cast descriptionBindStability.symm rfl
      secondBindStability stableUniversal stableNegation originalBody
  have rightNormalization : right = star14_saturatedExistential stableUniversal
      stableNegation stableReverseBody := by
    unfold right Formula.sometimes
    rw [matrixNegationSource, universalSource, outerNegationSource]
    unfold stableReverseBody
    exact star14_saturatedExistential_cast descriptionBindStability.symm rfl
      secondBindStability stableUniversal stableNegation reverseBody
  rw [← leftNormalization, ← rightNormalization] at line8
  exact line8

/-- ✱14·202, by the printed ✱14·1 and ✱13·195 route; the second half is
obtained by the same route after ✱13·16 reverses identity.
`demonstration_provenance: follows-printed`. -/
theorem star_14_202
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentityUniversal : signature.Universal
      (.function [sort]
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) 0)
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort))
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityDisjunction : signature.Disjunction
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationImplicationUniversal : signature.Universal sort
      (max
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort))
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)))
    (continuationResultNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (continuationResultDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort)
    (descriptionPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (applicationPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (conditionReducibility : Star14ReducibilityVocabulary signature sort
      conditionOrder)
    (continuationReducibility : Star14ReducibilityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)) :
    let logicalVocabulary := star_14_15_logicalVocabulary identityUniversal
      identityNegation identityDisjunction continuationIdentityNegation
      continuationIdentityDisjunction descriptionPrinted descriptionUniversal
      applicationPrinted applicationUniversal
    let continuationIdentity := star14_15_continuationIdentity
      identityNegation identityDisjunction continuationIdentityUniversal
    Derivation (star_14_202_reading logicalVocabulary.descriptionExistential
      identityUniversal conditionIdentity identityNegation identityDisjunction
      continuationIdentity continuationIdentityNegation
      logicalVocabulary.descriptionBodyNegation
      logicalVocabulary.descriptionBodyDisjunction condition b).parsed := by
  dsimp only
  let logicalVocabulary := star_14_15_logicalVocabulary identityUniversal
    identityNegation identityDisjunction continuationIdentityNegation
    continuationIdentityDisjunction descriptionPrinted descriptionUniversal
    applicationPrinted applicationUniversal
  let continuationIdentity := star14_15_continuationIdentity
    identityNegation identityDisjunction continuationIdentityUniversal
  have line1Core := star14_15_core
    logicalVocabulary.descriptionExistential identityUniversal
    conditionIdentity identityNegation identityDisjunction
    continuationIdentity continuationIdentityNegation
    continuationIdentityDisjunction rfl
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction
    continuationImplicationUniversal continuationResultNegation
    continuationResultDisjunction logicalVocabulary.applicationExistential
    logicalVocabulary.applicationBodyDisjunction
    applicationImplicationUniversal
    logicalVocabulary.applicationResultDisjunction
    logicalVocabulary.finalDisjunction condition psi b descriptionPrinted
    descriptionUniversal applicationPrinted applicationUniversal rfl rfl rfl
    rfl rfl rfl rfl conditionReducibility continuationReducibility
  have line1 := line1Core.2.1
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let uniquenessDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) identityDisjunction
  let continuationOrder := bindOrder uniquenessOrder
    (.function [sort] uniquenessOrder 0)
  let descriptionBodyOrder := max uniquenessOrder continuationOrder
  let descriptionResultOrder := bindOrder descriptionBodyOrder sort
  let descriptionBindStability :=
    star14_descriptionBindOrderStable conditionOrder sort
  let resultNegation := Eq.mp (congrArg signature.Negation
    descriptionBindStability.symm)
    logicalVocabulary.descriptionBodyNegation
  let resultDisjunction := Eq.mp (congrArg signature.Disjunction
    descriptionBindStability.symm)
    logicalVocabulary.descriptionBodyDisjunction
  let x : Term signature real [sort] sort := .apparent .zero
  let conditionEquals := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction condition
      (star_13_01 conditionIdentity x b.weaken))
  let conditionReverseEquals := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction condition
      (star_13_01 conditionIdentity b.weaken x))
  let identityDescription := star_14_descriptionIdentity
    logicalVocabulary.descriptionExistential identityUniversal
    conditionIdentity identityNegation identityDisjunction
    uniquenessNegation continuationIdentity continuationIdentityNegation
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction condition b
  let reverseContinuation := star_13_01 continuationIdentity b.weaken x
  let reverseIdentityDescription := star_14_01
    logicalVocabulary.descriptionExistential identityUniversal
    conditionIdentity identityNegation identityDisjunction
    uniquenessNegation continuationIdentityNegation
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction condition reverseContinuation
  have line2 := star14_uniquenessReverseEquivalence identityUniversal
    conditionIdentity identityNegation identityDisjunction condition b
    conditionReducibility
  have line3 := star14_descriptionReverseEquivalence
    logicalVocabulary.descriptionExistential identityUniversal
    conditionIdentity identityNegation identityDisjunction
    continuationIdentity continuationIdentityNegation
    continuationIdentityDisjunction rfl
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction rfl rfl condition b
    continuationReducibility
  let resultUniqueness : uniquenessOrder ≤ descriptionResultOrder := by
    exact Eq.mp (congrArg (fun order => uniquenessOrder ≤ order)
      descriptionBindStability.symm) (star14_le_max_left _ _)
  let highLow : max descriptionResultOrder uniquenessOrder =
      descriptionResultOrder := star14_max_eq_left_of_le resultUniqueness
  let lowHigh : max uniquenessOrder descriptionResultOrder =
      descriptionResultOrder := Nat.max_eq_right resultUniqueness
  let lowPair := natMaxSelf uniquenessOrder
  let highPair := natMaxSelf descriptionResultOrder
  let highToLow (high : Formula signature real [] descriptionResultOrder)
      (low : Formula signature real [] uniquenessOrder) :=
    star14_normalizedDisjunction highLow resultDisjunction
      (.neg resultNegation high) low
  let lowToHigh (low : Formula signature real [] uniquenessOrder)
      (high : Formula signature real [] descriptionResultOrder) :=
    star14_normalizedDisjunction lowHigh resultDisjunction
      (.neg uniquenessNegation low) high
  let firstForward := lowToHigh conditionEquals identityDescription
  let firstReverse := highToLow identityDescription conditionEquals
  change Derivation (.assertion
    (conjunction resultNegation resultDisjunction
      firstForward firstReverse)) at line1
  have line1Forward := Derivation.star_9_12_same resultNegation
    resultDisjunction line1
    (star_3_26 resultNegation resultDisjunction firstForward firstReverse)
  have line1Reverse := Derivation.star_9_12_same resultNegation
    resultDisjunction line1
    (star_3_27 resultNegation resultDisjunction firstForward firstReverse)
  let symmetryForward := implication uniquenessNegation uniquenessDisjunction
    conditionEquals conditionReverseEquals
  let symmetryReverse := implication uniquenessNegation uniquenessDisjunction
    conditionReverseEquals conditionEquals
  change Derivation (.assertion
    (conjunction uniquenessNegation uniquenessDisjunction
      symmetryForward symmetryReverse)) at line2
  have line2Forward := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line2
    (star_3_26 uniquenessNegation uniquenessDisjunction
      symmetryForward symmetryReverse)
  have line2Reverse := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line2
    (star_3_27 uniquenessNegation uniquenessDisjunction
      symmetryForward symmetryReverse)
  let secondForward := highToLow identityDescription conditionReverseEquals
  let secondReverse := lowToHigh conditionReverseEquals identityDescription
  let forwardNegation : MixedOrder.TernaryNegations signature := {
    pOrder := descriptionResultOrder
    qOrder := uniquenessOrder
    rOrder := uniquenessOrder
    p := resultNegation
    q := uniquenessNegation
    r := uniquenessNegation
    pq := Eq.mp (congrArg signature.Negation highLow.symm) resultNegation
    pr := Eq.mp (congrArg signature.Negation highLow.symm) resultNegation
    qr := Eq.mp (congrArg signature.Negation lowPair.symm) uniquenessNegation
    pqr := Eq.mp (congrArg signature.Negation
      (Eq.trans (congrArg (max descriptionResultOrder) lowPair) highLow).symm)
      resultNegation
  }
  let forwardDisjunction : MixedOrder.TernaryDisjunctions signature
      forwardNegation := {
    p := resultDisjunction
    q := uniquenessDisjunction
    r := uniquenessDisjunction
    pq := Eq.mp (congrArg signature.Disjunction highLow.symm)
      resultDisjunction
    pr := Eq.mp (congrArg signature.Disjunction highLow.symm)
      resultDisjunction
    qr := Eq.mp (congrArg signature.Disjunction lowPair.symm)
      uniquenessDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (Eq.trans (congrArg (max descriptionResultOrder) lowPair) highLow).symm)
      resultDisjunction
  }
  let rawBA := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ)
  let rawBAReverse := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)
  let rawBAForward := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP)
  have lineBANormalization :
      Eq.mp (congrArg (Formula signature real []) highLow) rawBA =
      conjunction resultNegation resultDisjunction
        firstReverse firstForward := by
    have lineBAShape : rawBA = conjunction forwardNegation.pq
        forwardDisjunction.pq rawBAReverse rawBAForward := by
      rfl
    rw [lineBAShape]
    rw [star14_conjunction_castOrder highLow resultNegation
      resultDisjunction rawBAReverse rawBAForward]
    have lineBAReverseNormalization :
        Eq.mp (congrArg (Formula signature real []) highLow) rawBAReverse =
        firstReverse := by
      unfold rawBAReverse firstReverse highToLow
        star14_normalizedDisjunction
      rfl
    have lineBAForwardNormalization :
        Eq.mp (congrArg (Formula signature real []) highLow) rawBAForward =
        firstForward := by
      let sourceEquality := MixedOrder.ternaryOrderCombine
        forwardNegation .q .p
      have lineVocabulary :
          Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              forwardDisjunction.pq =
            Eq.mp (congrArg signature.Disjunction lowHigh.symm)
              resultDisjunction := by
        change Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
            (Eq.mp (congrArg signature.Disjunction highLow.symm)
              resultDisjunction) = _
        calc
          _ = Eq.mp (congrArg signature.Disjunction
                (Eq.trans highLow.symm sourceEquality.symm))
              resultDisjunction :=
            (star14_cast_trans highLow.symm sourceEquality.symm
              resultDisjunction).symm
          _ = _ := by rfl
      change Eq.mp (congrArg (Formula signature real []) highLow)
        (Eq.mp (congrArg (Formula signature real []) sourceEquality)
          (.disj
            (Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              forwardDisjunction.pq)
            (.neg uniquenessNegation conditionEquals)
            identityDescription)) =
        Eq.mp (congrArg (Formula signature real []) lowHigh)
          (.disj
            (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
              resultDisjunction)
            (.neg uniquenessNegation conditionEquals)
            identityDescription)
      rw [lineVocabulary]
      let sourceBody : Formula signature real []
          (max uniquenessOrder descriptionResultOrder) :=
        .disj
          (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
            resultDisjunction)
          (.neg uniquenessNegation conditionEquals)
          identityDescription
      change Eq.mp (congrArg (Formula signature real []) highLow)
          (Eq.mp (congrArg (Formula signature real []) sourceEquality)
            sourceBody) =
        Eq.mp (congrArg (Formula signature real []) lowHigh) sourceBody
      calc
        _ = Eq.mp (congrArg (Formula signature real [])
              (Eq.trans sourceEquality highLow)) sourceBody :=
          (star14_cast_trans sourceEquality highLow sourceBody).symm
        _ = _ := by rfl
    rw [lineBAReverseNormalization, lineBAForwardNormalization]
  have lineBA := star_10_13 resultNegation resultDisjunction
    firstReverse firstForward line1Reverse line1Forward
  have lineBACast := Derivation.castAssertion lineBANormalization lineBA
  have lineBARaw := star14_uncastAssertionOrder highLow rawBA lineBACast
  let rawAC := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR)
  let rawACForward := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR)
  let rawACReverse := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryR ⊃ₚ MixedOrder.ternaryQ)
  have lineACNormalization :
      Eq.mp (congrArg (Formula signature real []) lowPair) rawAC =
      star_4_01 uniquenessNegation uniquenessDisjunction
        conditionEquals conditionReverseEquals := by
    have lineACShape : rawAC = conjunction forwardNegation.qr
        forwardDisjunction.qr rawACForward rawACReverse := by
      rfl
    rw [lineACShape]
    rw [star14_conjunction_castOrder lowPair uniquenessNegation
      uniquenessDisjunction rawACForward rawACReverse]
    have lineACForwardNormalization :
        Eq.mp (congrArg (Formula signature real []) lowPair) rawACForward =
        implication uniquenessNegation uniquenessDisjunction
          conditionEquals conditionReverseEquals := by
      change Eq.mp (congrArg (Formula signature real []) lowPair)
        (MixedOrder.normalizedDisjunction
          (MixedOrder.ternaryOrderCombine forwardNegation .q .r)
          forwardDisjunction.qr
          (.neg forwardNegation.q conditionEquals)
          conditionReverseEquals) = _
      exact mixedImplication_normalizeSameOrder rfl rfl
        uniquenessNegation uniquenessDisjunction
        conditionEquals conditionReverseEquals
    have lineACReverseNormalization :
        Eq.mp (congrArg (Formula signature real []) lowPair) rawACReverse =
        implication uniquenessNegation uniquenessDisjunction
          conditionReverseEquals conditionEquals := by
      change Eq.mp (congrArg (Formula signature real []) lowPair)
        (MixedOrder.normalizedDisjunction
          (MixedOrder.ternaryOrderCombine forwardNegation .r .q)
          forwardDisjunction.qr
          (.neg forwardNegation.r conditionReverseEquals)
          conditionEquals) = _
      exact mixedImplication_normalizeSameOrder rfl rfl
        uniquenessNegation uniquenessDisjunction
        conditionReverseEquals conditionEquals
    unfold star_4_01
    rw [lineACForwardNormalization, lineACReverseNormalization]
  have lineACCast := Derivation.castAssertion lineACNormalization line2
  have lineACRaw := star14_uncastAssertionOrder lowPair rawAC lineACCast
  have lineBCRaw := star14_mixedEquivalenceTransitive forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals lineBARaw lineACRaw
  let rawBC := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryR)
  let rawBCForward := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)
  let rawBCReverse := MixedOrder.ternaryInterpret forwardNegation
    forwardDisjunction identityDescription conditionEquals
    conditionReverseEquals
    (MixedOrder.ternaryR ⊃ₚ MixedOrder.ternaryP)
  have lineBCNormalization :
      Eq.mp (congrArg (Formula signature real []) highLow) rawBC =
      conjunction resultNegation resultDisjunction
        secondForward secondReverse := by
    have lineBCShape : rawBC = conjunction forwardNegation.pr
        forwardDisjunction.pr rawBCForward rawBCReverse := by
      rfl
    rw [lineBCShape]
    rw [star14_conjunction_castOrder highLow resultNegation
      resultDisjunction rawBCForward rawBCReverse]
    have lineBCForwardNormalization :
        Eq.mp (congrArg (Formula signature real []) highLow) rawBCForward =
        secondForward := by
      unfold rawBCForward secondForward highToLow
        star14_normalizedDisjunction
      rfl
    have lineBCReverseNormalization :
        Eq.mp (congrArg (Formula signature real []) highLow) rawBCReverse =
        secondReverse := by
      let sourceEquality := MixedOrder.ternaryOrderCombine
        forwardNegation .r .p
      have lineVocabulary :
          Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              forwardDisjunction.pr =
            Eq.mp (congrArg signature.Disjunction lowHigh.symm)
              resultDisjunction := by
        change Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
            (Eq.mp (congrArg signature.Disjunction highLow.symm)
              resultDisjunction) = _
        calc
          _ = Eq.mp (congrArg signature.Disjunction
                (Eq.trans highLow.symm sourceEquality.symm))
              resultDisjunction :=
            (star14_cast_trans highLow.symm sourceEquality.symm
              resultDisjunction).symm
          _ = _ := by rfl
      change Eq.mp (congrArg (Formula signature real []) highLow)
        (Eq.mp (congrArg (Formula signature real []) sourceEquality)
          (.disj
            (Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              forwardDisjunction.pr)
            (.neg uniquenessNegation conditionReverseEquals)
            identityDescription)) =
        Eq.mp (congrArg (Formula signature real []) lowHigh)
          (.disj
            (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
              resultDisjunction)
            (.neg uniquenessNegation conditionReverseEquals)
            identityDescription)
      rw [lineVocabulary]
      let sourceBody : Formula signature real []
          (max uniquenessOrder descriptionResultOrder) :=
        .disj
          (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
            resultDisjunction)
          (.neg uniquenessNegation conditionReverseEquals)
          identityDescription
      change Eq.mp (congrArg (Formula signature real []) highLow)
          (Eq.mp (congrArg (Formula signature real []) sourceEquality)
            sourceBody) =
        Eq.mp (congrArg (Formula signature real []) lowHigh) sourceBody
      calc
        _ = Eq.mp (congrArg (Formula signature real [])
              (Eq.trans sourceEquality highLow)) sourceBody :=
          (star14_cast_trans sourceEquality highLow sourceBody).symm
        _ = _ := by rfl
    rw [lineBCForwardNormalization, lineBCReverseNormalization]
  have lineBCCast := star14_castAssertionOrder highLow rawBC lineBCRaw
  rw [lineBCNormalization] at lineBCCast
  have line4 := lineBCCast
  let thirdForward := lowToHigh conditionReverseEquals
    reverseIdentityDescription
  let thirdReverse := highToLow reverseIdentityDescription
    conditionReverseEquals
  let reverseNegation : MixedOrder.TernaryNegations signature := {
    pOrder := uniquenessOrder
    qOrder := descriptionResultOrder
    rOrder := descriptionResultOrder
    p := uniquenessNegation
    q := resultNegation
    r := resultNegation
    pq := Eq.mp (congrArg signature.Negation lowHigh.symm) resultNegation
    pr := Eq.mp (congrArg signature.Negation lowHigh.symm) resultNegation
    qr := Eq.mp (congrArg signature.Negation highPair.symm) resultNegation
    pqr := Eq.mp (congrArg signature.Negation
      (Eq.trans (congrArg (max uniquenessOrder) highPair) lowHigh).symm)
      resultNegation
  }
  let reverseDisjunction : MixedOrder.TernaryDisjunctions signature
      reverseNegation := {
    p := uniquenessDisjunction
    q := resultDisjunction
    r := resultDisjunction
    pq := Eq.mp (congrArg signature.Disjunction lowHigh.symm)
      resultDisjunction
    pr := Eq.mp (congrArg signature.Disjunction lowHigh.symm)
      resultDisjunction
    qr := Eq.mp (congrArg signature.Disjunction highPair.symm)
      resultDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction
      (Eq.trans (congrArg (max uniquenessOrder) highPair) lowHigh).symm)
      resultDisjunction
  }
  let rawCB := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryQ)
  let rawCBForward := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ)
  let rawCBReverse := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryP)
  have lineCBNormalization :
      Eq.mp (congrArg (Formula signature real []) lowHigh) rawCB =
      conjunction resultNegation resultDisjunction
        secondReverse secondForward := by
    have lineCBShape : rawCB = conjunction reverseNegation.pq
        reverseDisjunction.pq rawCBForward rawCBReverse := by
      rfl
    rw [lineCBShape]
    rw [star14_conjunction_castOrder lowHigh resultNegation
      resultDisjunction rawCBForward rawCBReverse]
    have lineCBForwardNormalization :
        Eq.mp (congrArg (Formula signature real []) lowHigh) rawCBForward =
        secondReverse := by
      unfold rawCBForward secondReverse lowToHigh
        star14_normalizedDisjunction
      rfl
    have lineCBReverseNormalization :
        Eq.mp (congrArg (Formula signature real []) lowHigh) rawCBReverse =
        secondForward := by
      let sourceEquality := MixedOrder.ternaryOrderCombine
        reverseNegation .q .p
      have lineVocabulary :
          Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              reverseDisjunction.pq =
            Eq.mp (congrArg signature.Disjunction highLow.symm)
              resultDisjunction := by
        change Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
            (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
              resultDisjunction) = _
        calc
          _ = Eq.mp (congrArg signature.Disjunction
                (Eq.trans lowHigh.symm sourceEquality.symm))
              resultDisjunction :=
            (star14_cast_trans lowHigh.symm sourceEquality.symm
              resultDisjunction).symm
          _ = _ := by rfl
      change Eq.mp (congrArg (Formula signature real []) lowHigh)
        (Eq.mp (congrArg (Formula signature real []) sourceEquality)
          (.disj
            (Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              reverseDisjunction.pq)
            (.neg resultNegation identityDescription)
            conditionReverseEquals)) =
        Eq.mp (congrArg (Formula signature real []) highLow)
          (.disj
            (Eq.mp (congrArg signature.Disjunction highLow.symm)
              resultDisjunction)
            (.neg resultNegation identityDescription)
            conditionReverseEquals)
      rw [lineVocabulary]
      let sourceBody : Formula signature real []
          (max descriptionResultOrder uniquenessOrder) :=
        .disj
          (Eq.mp (congrArg signature.Disjunction highLow.symm)
            resultDisjunction)
          (.neg resultNegation identityDescription)
          conditionReverseEquals
      change Eq.mp (congrArg (Formula signature real []) lowHigh)
          (Eq.mp (congrArg (Formula signature real []) sourceEquality)
            sourceBody) =
        Eq.mp (congrArg (Formula signature real []) highLow) sourceBody
      calc
        _ = Eq.mp (congrArg (Formula signature real [])
              (Eq.trans sourceEquality lowHigh)) sourceBody :=
          (star14_cast_trans sourceEquality lowHigh sourceBody).symm
        _ = _ := by rfl
    rw [lineCBForwardNormalization, lineCBReverseNormalization]
  have lineCB := star_10_13 resultNegation resultDisjunction
    secondReverse secondForward
    (Derivation.star_9_12_same resultNegation resultDisjunction line4
      (star_3_27 resultNegation resultDisjunction
        secondForward secondReverse))
    (Derivation.star_9_12_same resultNegation resultDisjunction line4
      (star_3_26 resultNegation resultDisjunction
        secondForward secondReverse))
  have lineCBCast := Derivation.castAssertion lineCBNormalization lineCB
  have lineCBRaw := star14_uncastAssertionOrder lowHigh rawCB lineCBCast
  let rawBD := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryQ ≡ₚ MixedOrder.ternaryR)
  let rawBDForward := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR)
  let rawBDReverse := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryR ⊃ₚ MixedOrder.ternaryQ)
  have lineBDNormalization :
      Eq.mp (congrArg (Formula signature real []) highPair) rawBD =
      star_4_01 resultNegation resultDisjunction
        identityDescription reverseIdentityDescription := by
    have lineBDShape : rawBD = conjunction reverseNegation.qr
        reverseDisjunction.qr rawBDForward rawBDReverse := by
      rfl
    rw [lineBDShape]
    rw [star14_conjunction_castOrder highPair resultNegation
      resultDisjunction rawBDForward rawBDReverse]
    have lineBDForwardNormalization :
        Eq.mp (congrArg (Formula signature real []) highPair) rawBDForward =
        implication resultNegation resultDisjunction
          identityDescription reverseIdentityDescription := by
      change Eq.mp (congrArg (Formula signature real []) highPair)
        (MixedOrder.normalizedDisjunction
          (MixedOrder.ternaryOrderCombine reverseNegation .q .r)
          reverseDisjunction.qr
          (.neg reverseNegation.q identityDescription)
          reverseIdentityDescription) = _
      exact mixedImplication_normalizeSameOrder rfl rfl
        resultNegation resultDisjunction
        identityDescription reverseIdentityDescription
    have lineBDReverseNormalization :
        Eq.mp (congrArg (Formula signature real []) highPair) rawBDReverse =
        implication resultNegation resultDisjunction
          reverseIdentityDescription identityDescription := by
      change Eq.mp (congrArg (Formula signature real []) highPair)
        (MixedOrder.normalizedDisjunction
          (MixedOrder.ternaryOrderCombine reverseNegation .r .q)
          reverseDisjunction.qr
          (.neg reverseNegation.r reverseIdentityDescription)
          identityDescription) = _
      exact mixedImplication_normalizeSameOrder rfl rfl
        resultNegation resultDisjunction
        reverseIdentityDescription identityDescription
    unfold star_4_01
    rw [lineBDForwardNormalization, lineBDReverseNormalization]
  have lineBDCast := Derivation.castAssertion lineBDNormalization line3
  have lineBDRaw := star14_uncastAssertionOrder highPair rawBD lineBDCast
  have lineCDRaw := star14_mixedEquivalenceTransitive reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription lineCBRaw lineBDRaw
  let rawCD := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryP ≡ₚ MixedOrder.ternaryR)
  let rawCDForward := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)
  let rawCDReverse := MixedOrder.ternaryInterpret reverseNegation
    reverseDisjunction conditionReverseEquals identityDescription
    reverseIdentityDescription
    (MixedOrder.ternaryR ⊃ₚ MixedOrder.ternaryP)
  have lineCDNormalization :
      Eq.mp (congrArg (Formula signature real []) lowHigh) rawCD =
      conjunction resultNegation resultDisjunction
        thirdForward thirdReverse := by
    have lineCDShape : rawCD = conjunction reverseNegation.pr
        reverseDisjunction.pr rawCDForward rawCDReverse := by
      rfl
    rw [lineCDShape]
    rw [star14_conjunction_castOrder lowHigh resultNegation
      resultDisjunction rawCDForward rawCDReverse]
    have lineCDForwardNormalization :
        Eq.mp (congrArg (Formula signature real []) lowHigh) rawCDForward =
        thirdForward := by
      unfold rawCDForward thirdForward lowToHigh
        star14_normalizedDisjunction
      rfl
    have lineCDReverseNormalization :
        Eq.mp (congrArg (Formula signature real []) lowHigh) rawCDReverse =
        thirdReverse := by
      let sourceEquality := MixedOrder.ternaryOrderCombine
        reverseNegation .r .p
      have lineVocabulary :
          Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              reverseDisjunction.pr =
            Eq.mp (congrArg signature.Disjunction highLow.symm)
              resultDisjunction := by
        change Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
            (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
              resultDisjunction) = _
        calc
          _ = Eq.mp (congrArg signature.Disjunction
                (Eq.trans lowHigh.symm sourceEquality.symm))
              resultDisjunction :=
            (star14_cast_trans lowHigh.symm sourceEquality.symm
              resultDisjunction).symm
          _ = _ := by rfl
      change Eq.mp (congrArg (Formula signature real []) lowHigh)
        (Eq.mp (congrArg (Formula signature real []) sourceEquality)
          (.disj
            (Eq.mp (congrArg signature.Disjunction sourceEquality.symm)
              reverseDisjunction.pr)
            (.neg resultNegation reverseIdentityDescription)
            conditionReverseEquals)) =
        Eq.mp (congrArg (Formula signature real []) highLow)
          (.disj
            (Eq.mp (congrArg signature.Disjunction highLow.symm)
              resultDisjunction)
            (.neg resultNegation reverseIdentityDescription)
            conditionReverseEquals)
      rw [lineVocabulary]
      let sourceBody : Formula signature real []
          (max descriptionResultOrder uniquenessOrder) :=
        .disj
          (Eq.mp (congrArg signature.Disjunction highLow.symm)
            resultDisjunction)
          (.neg resultNegation reverseIdentityDescription)
          conditionReverseEquals
      change Eq.mp (congrArg (Formula signature real []) lowHigh)
          (Eq.mp (congrArg (Formula signature real []) sourceEquality)
            sourceBody) =
        Eq.mp (congrArg (Formula signature real []) highLow) sourceBody
      calc
        _ = Eq.mp (congrArg (Formula signature real [])
              (Eq.trans sourceEquality lowHigh)) sourceBody :=
          (star14_cast_trans sourceEquality lowHigh sourceBody).symm
        _ = _ := by rfl
    rw [lineCDForwardNormalization, lineCDReverseNormalization]
  have lineCDCast := star14_castAssertionOrder lowHigh rawCD lineCDRaw
  rw [lineCDNormalization] at lineCDCast
  have line5 := star_10_13 resultNegation resultDisjunction
    (conjunction resultNegation resultDisjunction
      firstForward firstReverse)
    (conjunction resultNegation resultDisjunction
      secondForward secondReverse) line1 line4
  have line6 := star_10_13 resultNegation resultDisjunction
    (conjunction resultNegation resultDisjunction
      (conjunction resultNegation resultDisjunction
        firstForward firstReverse)
      (conjunction resultNegation resultDisjunction
        secondForward secondReverse))
    (conjunction resultNegation resultDisjunction
      thirdForward thirdReverse) line5 lineCDCast
  change Derivation (star_14_202_reading
    logicalVocabulary.descriptionExistential identityUniversal
    conditionIdentity identityNegation identityDisjunction
    continuationIdentity continuationIdentityNegation
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction condition b).parsed at line6
  exact line6

#print axioms star_14_202

/-- ✱14·242, by the printed ✱14·202·15 chain; the final ✱3·22
only restores the printed orientation `ψb ≡ ψ(ℙx)(φx)`.
`demonstration_provenance: follows-printed`. -/
theorem star_14_242
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (continuationIdentityUniversal : signature.Universal
      (.function [sort]
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) 0)
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort))
    (continuationIdentityNegation : signature.Negation
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationIdentityDisjunction : signature.Disjunction
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
    (continuationImplicationUniversal : signature.Universal sort
      (max
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort))
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)))
    (continuationResultNegation : signature.Negation
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (continuationResultDisjunction : signature.Disjunction
      (bindOrder
        (max
          (bindOrder (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)
            (.function [sort]
              (bindOrder (bindOrder conditionOrder
                (.function [sort] conditionOrder 0)) sort) 0))
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort)) sort))
    (applicationImplicationUniversal : signature.Universal sort
      (max (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder)
        conditionOrder))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (psi : Formula signature real [sort] conditionOrder)
    (b : Term signature real [] sort)
    (descriptionPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (descriptionUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))))
    (applicationPrinted : signature.Existential sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationUniversal : signature.Universal sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (conditionReducibility : Star14ReducibilityVocabulary signature sort
      conditionOrder)
    (continuationReducibility : Star14ReducibilityVocabulary signature sort
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)) :
    let logicalVocabulary := star_14_15_logicalVocabulary identityUniversal
      identityNegation identityDisjunction continuationIdentityNegation
      continuationIdentityDisjunction descriptionPrinted descriptionUniversal
      applicationPrinted applicationUniversal
    Derivation (star_14_242_reading identityUniversal conditionIdentity
      identityNegation identityDisjunction
      logicalVocabulary.applicationExistential
      logicalVocabulary.applicationBodyDisjunction
      applicationImplicationUniversal
      logicalVocabulary.applicationResultDisjunction condition psi b).parsed := by
  dsimp only
  let logicalVocabulary := star_14_15_logicalVocabulary identityUniversal
    identityNegation identityDisjunction continuationIdentityNegation
    continuationIdentityDisjunction descriptionPrinted descriptionUniversal
    applicationPrinted applicationUniversal
  let continuationIdentity := star14_15_continuationIdentity
    identityNegation identityDisjunction continuationIdentityUniversal
  have line1 := star14_15_core logicalVocabulary.descriptionExistential
    identityUniversal conditionIdentity identityNegation identityDisjunction
    continuationIdentity continuationIdentityNegation
    continuationIdentityDisjunction rfl
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction
    continuationImplicationUniversal continuationResultNegation
    continuationResultDisjunction logicalVocabulary.applicationExistential
    logicalVocabulary.applicationBodyDisjunction
    applicationImplicationUniversal
    logicalVocabulary.applicationResultDisjunction
    logicalVocabulary.finalDisjunction condition psi b descriptionPrinted
    descriptionUniversal applicationPrinted applicationUniversal rfl rfl rfl
    rfl rfl rfl rfl conditionReducibility continuationReducibility
  exact line1.2.2

#print axioms star_14_242

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

/-- Full ramified contextual AST used by the unconditional reconstruction of
✱14·31.  The description candidate matrix is literally
`(∀x)(φx ≡ x=b)`; the two displayed description applications are the
stable casts of their ✱14·01 existential scopes. -/
private def star14_31_full_formula
    (identityUniversal : signature.Universal sort
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (conditionIdentity : IdentityVocabulary signature sort conditionOrder 0)
    (identityNegation : signature.Negation
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (identityDisjunction : signature.Disjunction
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (applicationExistential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (applicationBodyDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) conditionOrder))
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (chi : Formula signature real [sort] conditionOrder)
    (p : Formula signature real [] conditionOrder) :=
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let stableNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) identityNegation
  let stableDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) identityDisjunction
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) identityStability.symm)
    identityUniversal
  let stableBind := star14_bindOrderStable identityOrder sort
  let applicationStability := star14_applicationOrderStable conditionOrder sort
  let applicationResultStability := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      applicationStability) stableBind
  let applicationBodyNegation := Eq.mp (congrArg signature.Negation
    applicationStability.symm) stableNegation
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let candidate : Term signature real [sort, sort] sort :=
    .apparent (.succ .zero)
  let conditionUnderCandidate : Formula signature real [sort, sort]
      identityOrder := condition.rename
    (liftRenaming (fun v => .succ v))
  let uniquenessMatrix := Formula.always identityUniversal
    (equivalence identityNegation identityDisjunction conditionUnderCandidate
      (star_13_01 conditionIdentity x candidate))
  let descriptionBody
      (psi : Formula signature real [sort] conditionOrder) :=
    mixedConjunction stableNegation conditionIdentity.negation
      applicationBodyNegation applicationBodyDisjunction uniquenessMatrix psi
  let descriptionScope
      (body : Formula signature real [sort]
        (max uniquenessOrder conditionOrder)) :=
    Eq.mp (congrArg (Formula signature real []) applicationResultStability)
      (Formula.sometimes applicationExistential body)
  let leftMatrix := sameDisjunction conditionIdentity.disjunction
    (p.rename (fun v => .succ v)) chi
  let leftBody := descriptionBody leftMatrix
  let rightBody := descriptionBody chi
  let leftScope := descriptionScope leftBody
  let rightScope := descriptionScope rightBody
  let conditionLeIdentity : conditionOrder ≤ identityOrder := by
    unfold identityOrder bindOrder
    exact star14_le_max_left _ _
  let identityLeUniqueness : identityOrder ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_left _ _
  let conditionLeUniqueness := Nat.le_trans conditionLeIdentity
    identityLeUniqueness
  let lowHigh : max conditionOrder uniquenessOrder = uniquenessOrder :=
    Nat.max_eq_right conditionLeUniqueness
  let rightSide := star14_normalizedDisjunction lowHigh stableDisjunction
    p rightScope
  let applicationUniquenessEquality :
      max (max uniquenessOrder conditionOrder) uniquenessOrder =
        uniquenessOrder :=
    natMaxCongr applicationStability rfl
  let leftToRightUniversal := Eq.mp
    (congrArg (signature.Universal sort)
      applicationUniquenessEquality.symm)
    (Eq.mp (congrArg (signature.Universal sort) applicationStability)
      applicationExistential.universal)
  let leftToRightDisjunction := Eq.mp
    (congrArg signature.Disjunction applicationUniquenessEquality.symm)
    stableDisjunction
  let leftToRightRaw := star_10_23_right applicationExistential
    applicationExistential.universal leftToRightUniversal
    applicationBodyNegation leftToRightDisjunction leftBody rightSide
  let leftToRightEquality := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      applicationUniquenessEquality) stableBind
  let leftToRight := Eq.mp (congrArg (Formula signature real [])
    leftToRightEquality) leftToRightRaw
  let rightToLeft := implication stableNegation stableDisjunction
    rightSide leftScope
  let conclusion := conjunction stableNegation stableDisjunction
    leftToRight rightToLeft
  Eq.mp (congrArg (Formula signature real []) stableBind)
    (Formula.always stableUniversal
      (implication stableNegation stableDisjunction uniquenessMatrix
        (conclusion.rename (fun v => .succ v))))

/-- Syntax and reducibility data shared by the two ✱14·242 specializations
in the printed proof of ✱14·31. -/
structure Star14_31Vocabulary (signature : Signature) (sort : RSort)
    (conditionOrder : Nat) where
  identityUniversal : signature.Universal sort
    (bindOrder conditionOrder (.function [sort] conditionOrder 0))
  conditionIdentity : IdentityVocabulary signature sort conditionOrder 0
  identityNegation : signature.Negation
    (bindOrder conditionOrder (.function [sort] conditionOrder 0))
  identityDisjunction : signature.Disjunction
    (bindOrder conditionOrder (.function [sort] conditionOrder 0))
  continuationIdentityUniversal : signature.Universal
    (.function [sort]
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) 0)
    (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
  continuationIdentityNegation : signature.Negation
    (bindOrder (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
      (.function [sort]
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) 0))
  continuationIdentityDisjunction : signature.Disjunction
    (bindOrder (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
      (.function [sort]
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort) 0))
  continuationImplicationUniversal : signature.Universal sort
    (max
      (max
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort))
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort))
  continuationResultNegation : signature.Negation
    (bindOrder
      (max
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)) sort)
  continuationResultDisjunction : signature.Disjunction
    (bindOrder
      (max
        (bindOrder (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)
          (.function [sort]
            (bindOrder (bindOrder conditionOrder
              (.function [sort] conditionOrder 0)) sort) 0))
        (bindOrder (bindOrder conditionOrder
          (.function [sort] conditionOrder 0)) sort)) sort)
  applicationImplicationUniversal : signature.Universal sort
    (max (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort) conditionOrder)
      conditionOrder)
  descriptionPrinted : signature.Existential sort
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
  descriptionUniversal : signature.Universal sort
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)
      (bindOrder (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort)
        (.function [sort]
          (bindOrder (bindOrder conditionOrder
            (.function [sort] conditionOrder 0)) sort) 0)))
  applicationPrinted : signature.Existential sort
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort) conditionOrder)
  applicationUniversal : signature.Universal sort
    (max (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort) conditionOrder)
  conditionReducibility : Star14ReducibilityVocabulary signature sort
    conditionOrder
  continuationReducibility : Star14ReducibilityVocabulary signature sort
    (bindOrder (bindOrder conditionOrder
      (.function [sort] conditionOrder 0)) sort)

/-- Primitive real-scope normal form of ✱14·31 at the independently
assigned orders of its three displayed matrices. -/
def star_14_31_formula
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (chi : Formula signature real [sort] conditionOrder)
    (p : Formula signature real [] conditionOrder) :
    Formula signature real []
      (bindOrder (bindOrder conditionOrder
        (.function [sort] conditionOrder 0)) sort) :=
  star14_31_full_formula vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction
    (star_14_15_logicalVocabulary vocabulary.identityUniversal
      vocabulary.identityNegation vocabulary.identityDisjunction
      vocabulary.continuationIdentityNegation
      vocabulary.continuationIdentityDisjunction
      vocabulary.descriptionPrinted vocabulary.descriptionUniversal
      vocabulary.applicationPrinted
      vocabulary.applicationUniversal).applicationExistential
    (star_14_15_logicalVocabulary vocabulary.identityUniversal
      vocabulary.identityNegation vocabulary.identityDisjunction
      vocabulary.continuationIdentityNegation
      vocabulary.continuationIdentityDisjunction
      vocabulary.descriptionPrinted vocabulary.descriptionUniversal
      vocabulary.applicationPrinted
      vocabulary.applicationUniversal).applicationBodyDisjunction
    condition chi p

/-- Audited contextual reading of ✱14·31. -/
def star_14_31_reading
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (chi : Formula signature real [sort] conditionOrder)
    (p : Formula signature real [] conditionOrder) :
    Star14Reading signature real where
  printed := PM.pmPrinted
    "⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ∨ χ(℩x)(φx) .≡ : p ∨ [(℩x)(φx)] . χ(℩x)(φx)"
  parsed := .assertion (star_14_31_formula vocabulary condition chi p)
  scopeReading := "After ✱14·242 eliminates each contextual description at a displayed candidate, MixedOrder.✱4·37 lifts the second equivalence through disjunction and ✱10·23 closes the candidate beneath the existence antecedent."

/-- ✱14·31, reconstructed unconditionally along PM's printed route.
`demonstration_provenance: follows-printed`. -/
theorem star_14_31
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (chi : Formula signature real [sort] conditionOrder)
    (p : Formula signature real [] conditionOrder) :
    Derivation (star_14_31_reading vocabulary condition chi p).parsed := by
  change Derivation (.assertion (star14_31_full_formula
    vocabulary.identityUniversal vocabulary.conditionIdentity
    vocabulary.identityNegation vocabulary.identityDisjunction
    (star_14_15_logicalVocabulary vocabulary.identityUniversal
      vocabulary.identityNegation vocabulary.identityDisjunction
      vocabulary.continuationIdentityNegation
      vocabulary.continuationIdentityDisjunction
      vocabulary.descriptionPrinted vocabulary.descriptionUniversal
      vocabulary.applicationPrinted
      vocabulary.applicationUniversal).applicationExistential
    (star_14_15_logicalVocabulary vocabulary.identityUniversal
      vocabulary.identityNegation vocabulary.identityDisjunction
      vocabulary.continuationIdentityNegation
      vocabulary.continuationIdentityDisjunction
      vocabulary.descriptionPrinted vocabulary.descriptionUniversal
      vocabulary.applicationPrinted
      vocabulary.applicationUniversal).applicationBodyDisjunction
    condition chi p))
  let logicalVocabulary := star_14_15_logicalVocabulary
    vocabulary.identityUniversal vocabulary.identityNegation
    vocabulary.identityDisjunction vocabulary.continuationIdentityNegation
    vocabulary.continuationIdentityDisjunction vocabulary.descriptionPrinted
    vocabulary.descriptionUniversal vocabulary.applicationPrinted
    vocabulary.applicationUniversal
  let witness : Term signature (sort :: real) [] sort :=
    .real (.zero : Var (sort :: real) sort)
  let leftMatrix := sameDisjunction vocabulary.conditionIdentity.disjunction
    (p.rename (fun v => .succ v)) chi
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) vocabulary.identityNegation
  let uniquenessDisjunction := Eq.mp (congrArg signature.Disjunction
    identityStability.symm) vocabulary.identityDisjunction
  let applicationOrder := max uniquenessOrder conditionOrder
  let applicationStability := star14_applicationOrderStable conditionOrder sort
  let applicationResultStability := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      applicationStability)
    (star14_bindOrderStable identityOrder sort)
  let applicationBodyNegation := Eq.mp (congrArg signature.Negation
    applicationStability.symm) uniquenessNegation
  let printedFormula := Formula.always vocabulary.identityUniversal condition
  let printedMatrixEquality := Eq.trans applicationStability identityStability
  let printedMatrix := Eq.mp (congrArg (Formula signature real [sort])
    printedMatrixEquality.symm) condition
  let printed14RawFormula := star_4_01
    logicalVocabulary.applicationExistential.outerNegation
    logicalVocabulary.applicationResultDisjunction
    (star_14_11_left logicalVocabulary.applicationExistential printedMatrix)
    (star_14_11_right logicalVocabulary.applicationExistential printedMatrix)
  have printed14Raw := star_14_11 logicalVocabulary.applicationExistential
    printedMatrix logicalVocabulary.applicationExistential.outerNegation
    logicalVocabulary.applicationResultDisjunction
  change Derivation (.assertion printed14RawFormula) at printed14Raw
  let printed14Formula := Eq.mp (congrArg (Formula signature real [])
    applicationResultStability) printed14RawFormula
  have printed14 := star14_castAssertionOrder applicationResultStability
    printed14RawFormula printed14Raw
  let printedApplicationEquality :
      max applicationOrder uniquenessOrder = uniquenessOrder :=
    natMaxCongr applicationStability rfl
  let printedUniversal := Eq.mp (congrArg (signature.Universal sort)
    printedApplicationEquality.symm)
    (Eq.mp (congrArg (signature.Universal sort) applicationStability)
      logicalVocabulary.applicationExistential.universal)
  let printedDisjunction := Eq.mp (congrArg signature.Disjunction
    printedApplicationEquality.symm) uniquenessDisjunction
  let printedResultEquality := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      printedApplicationEquality)
    (star14_bindOrderStable identityOrder sort)
  let printedResultNegation := Eq.mp (congrArg signature.Negation
    printedResultEquality.symm) uniquenessNegation
  let printedResultDisjunction := Eq.mp (congrArg signature.Disjunction
    printedResultEquality.symm) uniquenessDisjunction
  let printed10RawFormula := star_4_01 printedResultNegation
    printedResultDisjunction
    (star_10_23_left printedUniversal applicationBodyNegation
      printedDisjunction printedMatrix printedFormula)
    (star_10_23_right logicalVocabulary.applicationExistential
      logicalVocabulary.applicationExistential.universal printedUniversal
      applicationBodyNegation printedDisjunction printedMatrix printedFormula)
  have printed10Raw := star_10_23 logicalVocabulary.applicationExistential
    logicalVocabulary.applicationExistential.universal printedUniversal
    applicationBodyNegation printedDisjunction printedResultNegation
    printedResultDisjunction printedMatrix printedFormula
  change Derivation (.assertion printed10RawFormula) at printed10Raw
  let printed10Formula := Eq.mp (congrArg (Formula signature real [])
    printedResultEquality) printed10RawFormula
  have printed10 := star14_castAssertionOrder printedResultEquality
    printed10RawFormula printed10Raw
  let printedSame := natMaxSelf uniquenessOrder
  let printedTriple : max uniquenessOrder
      (max uniquenessOrder uniquenessOrder) = uniquenessOrder :=
    Eq.trans (congrArg (max uniquenessOrder) printedSame) printedSame
  let printedNegations : MixedOrder.TernaryNegations signature := {
    pOrder := uniquenessOrder
    qOrder := uniquenessOrder
    rOrder := uniquenessOrder
    p := uniquenessNegation
    q := uniquenessNegation
    r := uniquenessNegation
    pq := Eq.mp (congrArg signature.Negation printedSame.symm)
      uniquenessNegation
    pr := Eq.mp (congrArg signature.Negation printedSame.symm)
      uniquenessNegation
    qr := Eq.mp (congrArg signature.Negation printedSame.symm)
      uniquenessNegation
    pqr := Eq.mp (congrArg signature.Negation printedTriple.symm)
      uniquenessNegation
  }
  let printedDisjunctions : MixedOrder.TernaryDisjunctions signature
      printedNegations := {
    p := uniquenessDisjunction
    q := uniquenessDisjunction
    r := uniquenessDisjunction
    pq := Eq.mp (congrArg signature.Disjunction printedSame.symm)
      uniquenessDisjunction
    pr := Eq.mp (congrArg signature.Disjunction printedSame.symm)
      uniquenessDisjunction
    qr := Eq.mp (congrArg signature.Disjunction printedSame.symm)
      uniquenessDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction printedTriple.symm)
      uniquenessDisjunction
  }
  let printed4RawFormula := MixedOrder.star_4_37_formula
    printedNegations printedDisjunctions printedFormula printedFormula
    printedFormula
  have printed4Raw := MixedOrder.star_4_37 printedNegations
    printedDisjunctions printedFormula printedFormula printedFormula
  change Derivation (.assertion printed4RawFormula) at printed4Raw
  let printed4Formula := Eq.mp (congrArg (Formula signature real [])
    printedTriple) printed4RawFormula
  have printed4 := star14_castAssertionOrder printedTriple
    printed4RawFormula printed4Raw
  have line1 := star_14_242 vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction vocabulary.continuationIdentityUniversal
    vocabulary.continuationIdentityNegation
    vocabulary.continuationIdentityDisjunction
    vocabulary.continuationImplicationUniversal
    vocabulary.continuationResultNegation
    vocabulary.continuationResultDisjunction
    vocabulary.applicationImplicationUniversal condition.weakenReal
    leftMatrix.weakenReal witness vocabulary.descriptionPrinted
    vocabulary.descriptionUniversal vocabulary.applicationPrinted
    vocabulary.applicationUniversal vocabulary.conditionReducibility
    vocabulary.continuationReducibility
  let conditionAtWitness : Formula signature (sort :: real) [sort]
      identityOrder := condition.weakenReal
  let leftMatrixAtWitness : Formula signature (sort :: real) [sort]
      conditionOrder := leftMatrix.weakenReal
  let x : Term signature (sort :: real) [sort] sort := .apparent .zero
  let hypothesis := Formula.always vocabulary.identityUniversal
    (equivalence vocabulary.identityNegation vocabulary.identityDisjunction
      conditionAtWitness
      (star_13_01 vocabulary.conditionIdentity x witness.weaken))
  let functionX : Term signature (sort :: real) [sort, sort] sort :=
    .apparent .zero
  let candidate : Term signature (sort :: real) [sort, sort] sort :=
    .apparent (.succ .zero)
  let conditionUnderCandidate : Formula signature (sort :: real) [sort, sort]
      identityOrder := conditionAtWitness.rename
    (liftRenaming (fun v => .succ v))
  let uniquenessMatrixAtWitness := Formula.always
    vocabulary.identityUniversal
    (equivalence vocabulary.identityNegation vocabulary.identityDisjunction
      conditionUnderCandidate
      (star_13_01 vocabulary.conditionIdentity functionX candidate))
  let applicationBody := mixedConjunction uniquenessNegation
    vocabulary.conditionIdentity.negation applicationBodyNegation
    logicalVocabulary.applicationBodyDisjunction
    uniquenessMatrixAtWitness leftMatrixAtWitness
  let psiDescription := Formula.sometimes
    logicalVocabulary.applicationExistential applicationBody
  let psiB := leftMatrixAtWitness.instantiate witness
  let applicationPsiEquality := MixedOrder.maxRightAbsorb
    uniquenessOrder conditionOrder
  let applicationPsiDisjunction := Eq.mp (congrArg signature.Disjunction
    applicationPsiEquality.symm) logicalVocabulary.applicationBodyDisjunction
  let forwardEquality := congrArg (fun matrixOrder => bindOrder matrixOrder sort)
    applicationPsiEquality
  let forward := Eq.mp (congrArg (Formula signature (sort :: real) [])
    forwardEquality)
    (star_10_23_right logicalVocabulary.applicationExistential
      logicalVocabulary.applicationExistential.universal
      vocabulary.applicationImplicationUniversal applicationBodyNegation
      applicationPsiDisjunction applicationBody psiB)
  let reverseEquality := Eq.trans
    (bindOrderMaxLeft conditionOrder applicationOrder sort)
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      (MixedOrder.maxRightLeftAbsorb uniquenessOrder conditionOrder))
  let reverse := star14_normalizedDisjunction reverseEquality
    logicalVocabulary.applicationResultDisjunction
    (.neg vocabulary.conditionIdentity.negation psiB) psiDescription
  let stableForward := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationResultStability) forward
  let stableReverse := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationResultStability) reverse
  change Derivation (.assertion (implication uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction
      stableReverse stableForward))) at line1
  let leftScope := Eq.mp (congrArg (Formula signature (sort :: real) [])
    applicationResultStability) psiDescription
  let pAtWitness := p.weakenReal (fresh := sort)
  let chiAtWitness := chi.weakenReal.instantiate witness
  let targetAtWitness := sameDisjunction
    vocabulary.conditionIdentity.disjunction pAtWitness chiAtWitness
  have leftAtWitness : psiB = targetAtWitness := by
    unfold psiB leftMatrixAtWitness leftMatrix targetAtWitness
      pAtWitness chiAtWitness
    rw [sameDisjunction_weakenReal, Formula.instantiate,
      sameDisjunction_substitute]
    rw [Formula.closed_weakenReal_instantiateSubstitution]
    rfl
  have line1Reverse := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction
      stableReverse stableForward) stableReverse line1
    (star_3_26 uniquenessNegation uniquenessDisjunction
      stableReverse stableForward)
  have line1Forward := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction
      stableReverse stableForward) stableForward line1
    (star_3_27 uniquenessNegation uniquenessDisjunction
      stableReverse stableForward)
  have line2 := star_14_242 vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction vocabulary.continuationIdentityUniversal
    vocabulary.continuationIdentityNegation
    vocabulary.continuationIdentityDisjunction
    vocabulary.continuationImplicationUniversal
    vocabulary.continuationResultNegation
    vocabulary.continuationResultDisjunction
    vocabulary.applicationImplicationUniversal condition.weakenReal
    chi.weakenReal witness vocabulary.descriptionPrinted
    vocabulary.descriptionUniversal vocabulary.applicationPrinted
    vocabulary.applicationUniversal vocabulary.conditionReducibility
    vocabulary.continuationReducibility
  let rightMatrixAtWitness : Formula signature (sort :: real) [sort]
      conditionOrder := chi.weakenReal
  let rightApplicationBody := mixedConjunction uniquenessNegation
    vocabulary.conditionIdentity.negation applicationBodyNegation
    logicalVocabulary.applicationBodyDisjunction
    uniquenessMatrixAtWitness rightMatrixAtWitness
  let rightDescription := Formula.sometimes
    logicalVocabulary.applicationExistential rightApplicationBody
  let rightPsiB := rightMatrixAtWitness.instantiate witness
  let rightForward := Eq.mp (congrArg
    (Formula signature (sort :: real) []) forwardEquality)
    (star_10_23_right logicalVocabulary.applicationExistential
      logicalVocabulary.applicationExistential.universal
      vocabulary.applicationImplicationUniversal applicationBodyNegation
      applicationPsiDisjunction rightApplicationBody rightPsiB)
  let rightReverse := star14_normalizedDisjunction reverseEquality
    logicalVocabulary.applicationResultDisjunction
    (.neg vocabulary.conditionIdentity.negation rightPsiB) rightDescription
  let stableRightForward := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationResultStability)
    rightForward
  let stableRightReverse := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationResultStability)
    rightReverse
  change Derivation (.assertion (implication uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction
      stableRightReverse stableRightForward))) at line2
  have rightPsiAtWitness : rightPsiB = chiAtWitness := by
    rfl
  have line2Forward := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction
      stableRightReverse stableRightForward) stableRightReverse line2
    (star_3_26 uniquenessNegation uniquenessDisjunction
      stableRightReverse stableRightForward)
  have line2Reverse := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction
      stableRightReverse stableRightForward) stableRightForward line2
    (star_3_27 uniquenessNegation uniquenessDisjunction
      stableRightReverse stableRightForward)
  let rightScope := Eq.mp (congrArg (Formula signature (sort :: real) [])
    applicationResultStability) rightDescription
  have conditionLeIdentity : conditionOrder ≤ identityOrder := by
    unfold identityOrder bindOrder
    exact star14_le_max_left _ _
  have identityLeUniqueness : identityOrder ≤ uniquenessOrder := by
    unfold uniquenessOrder bindOrder
    exact star14_le_max_left _ _
  have conditionLeUniqueness : conditionOrder ≤ uniquenessOrder :=
    Nat.le_trans conditionLeIdentity identityLeUniqueness
  let lowHigh : max conditionOrder uniquenessOrder = uniquenessOrder :=
    Nat.max_eq_right conditionLeUniqueness
  let highLow : max uniquenessOrder conditionOrder = uniquenessOrder :=
    star14_max_eq_left_of_le conditionLeUniqueness
  let rightAtWitness := star14_normalizedDisjunction lowHigh
    uniquenessDisjunction pAtWitness rightScope
  let rightNegated := star_9_02
    logicalVocabulary.applicationExistential.universal
    applicationBodyNegation rightApplicationBody
  let stableRightNegated := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationResultStability)
    rightNegated
  have rightNegationDefinition : ImplicationNegation signature
      (sort :: real) logicalVocabulary.applicationExistential.outerNegation
      rightDescription rightNegated := by
    unfold rightDescription rightNegated
    exact ImplicationNegation.star_9_02
      logicalVocabulary.applicationExistential.outerNegation
      logicalVocabulary.applicationExistential
      logicalVocabulary.applicationExistential.universal
      applicationBodyNegation rightApplicationBody
  have applicationOuterNegationSource :
      logicalVocabulary.applicationExistential.outerNegation =
        Eq.mp (congrArg signature.Negation
          applicationResultStability.symm) uniquenessNegation := by
    unfold logicalVocabulary star_14_15_logicalVocabulary
      applicationResultStability uniquenessNegation identityStability
    rfl
  rw [applicationOuterNegationSource] at rightNegationDefinition
  have stableRightNegationDefinition : ImplicationNegation signature
      (sort :: real) uniquenessNegation rightScope stableRightNegated := by
    exact star14_castImplicationNegationOrder applicationResultStability
      uniquenessNegation rightDescription rightNegated
      rightNegationDefinition
  have rightReverseDefinition : ImplicationDisjunction signature
      (sort :: real) (.neg vocabulary.conditionIdentity.negation rightPsiB)
      rightDescription rightReverse := by
    unfold rightReverse star14_normalizedDisjunction
    apply star14_castImplicationDisjunctionResult reverseEquality
    exact ImplicationDisjunction.star_1_01
      (Eq.mp (congrArg signature.Disjunction reverseEquality.symm)
        logicalVocabulary.applicationResultDisjunction)
      (.neg vocabulary.conditionIdentity.negation rightPsiB)
      rightDescription
  have stableRightReverseDefinition : ImplicationDisjunction signature
      (sort :: real) (.neg vocabulary.conditionIdentity.negation rightPsiB)
      rightScope stableRightReverse := by
    unfold rightScope stableRightReverse
    exact star14_castImplicationDisjunctionOrder
      applicationResultStability
      (.neg vocabulary.conditionIdentity.negation rightPsiB)
      rightDescription rightReverse rightReverseDefinition
  have rightForwardDefinition : ImplicationDisjunction signature
      (sort :: real) rightNegated rightPsiB rightForward := by
    unfold rightForward rightNegated
    apply star14_castImplicationDisjunctionResult forwardEquality
    unfold star_10_23_right
    exact ImplicationDisjunction.star_9_03
      logicalVocabulary.applicationExistential.universal
      vocabulary.applicationImplicationUniversal
      (.neg applicationBodyNegation rightApplicationBody) rightPsiB
      (.disj applicationPsiDisjunction
        (.neg applicationBodyNegation rightApplicationBody)
        (rightPsiB.rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01 applicationPsiDisjunction
        (.neg applicationBodyNegation rightApplicationBody)
        (rightPsiB.rename (fun v => .succ v)))
  have stableRightForwardDefinition : ImplicationDisjunction signature
      (sort :: real) stableRightNegated rightPsiB stableRightForward := by
    unfold stableRightNegated stableRightForward
    exact star14_castImplicationDisjunctionLeftOrder
      applicationResultStability rightNegated rightForward rightPsiB
      rightForwardDefinition
  have targetDisjunctionDefinition : ImplicationDisjunction signature
      (sort :: real) pAtWitness rightPsiB psiB := by
    rw [leftAtWitness, rightPsiAtWitness]
    exact ImplicationDisjunction.star_1_01_same
      vocabulary.conditionIdentity.disjunction pAtWitness chiAtWitness
  have rightDisjunctionDefinition : ImplicationDisjunction signature
      (sort :: real) pAtWitness rightScope rightAtWitness := by
    unfold rightAtWitness star14_normalizedDisjunction
    apply star14_castImplicationDisjunctionResult lowHigh
    exact ImplicationDisjunction.star_1_01
      (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
        uniquenessDisjunction) pAtWitness rightScope
  let targetToRight := star14_normalizedDisjunction lowHigh
    uniquenessDisjunction
    (.neg vocabulary.conditionIdentity.negation psiB) rightAtWitness
  let rightToTarget := star14_normalizedDisjunction highLow
    uniquenessDisjunction (.neg uniquenessNegation rightAtWitness) psiB
  have targetNegationDefinition : ImplicationNegation signature
      (sort :: real) vocabulary.conditionIdentity.negation psiB
      (.neg vocabulary.conditionIdentity.negation psiB) :=
    ImplicationNegation.star_1_01
      vocabulary.conditionIdentity.negation psiB
  have targetToRightDefinition : ImplicationDisjunction signature
      (sort :: real) (.neg vocabulary.conditionIdentity.negation psiB)
      rightAtWitness targetToRight := by
    unfold targetToRight star14_normalizedDisjunction
    apply star14_castImplicationDisjunctionResult lowHigh
    exact ImplicationDisjunction.star_1_01
      (Eq.mp (congrArg signature.Disjunction lowHigh.symm)
        uniquenessDisjunction)
      (.neg vocabulary.conditionIdentity.negation psiB) rightAtWitness
  have rightNegatedDefinition : ImplicationNegation signature
      (sort :: real) uniquenessNegation rightAtWitness
      (.neg uniquenessNegation rightAtWitness) :=
    ImplicationNegation.star_1_01 uniquenessNegation rightAtWitness
  have rightToTargetDefinition : ImplicationDisjunction signature
      (sort :: real) (.neg uniquenessNegation rightAtWitness)
      psiB rightToTarget := by
    unfold rightToTarget star14_normalizedDisjunction
    apply star14_castImplicationDisjunctionResult highLow
    exact ImplicationDisjunction.star_1_01
      (Eq.mp (congrArg signature.Disjunction highLow.symm)
        uniquenessDisjunction)
      (.neg uniquenessNegation rightAtWitness) psiB
  let sameCondition := natMaxSelf conditionOrder
  let forwardConsequenceEquality :
      max (max conditionOrder conditionOrder)
          (max conditionOrder uniquenessOrder) = uniquenessOrder :=
    Eq.trans
      (congrArg (fun left => max left
        (max conditionOrder uniquenessOrder)) sameCondition)
      (Eq.trans (MixedOrder.maxLeftAbsorb conditionOrder uniquenessOrder)
        lowHigh)
  let forwardOuterEquality :
      max (max conditionOrder uniquenessOrder)
          (max (max conditionOrder conditionOrder)
            (max conditionOrder uniquenessOrder)) = uniquenessOrder :=
    natMaxCongr lowHigh forwardConsequenceEquality
  let conditionUniquenessDisjunction := Eq.mp
    (congrArg signature.Disjunction lowHigh.symm) uniquenessDisjunction
  let conditionUniquenessNegation := Eq.mp
    (congrArg signature.Negation lowHigh.symm) uniquenessNegation
  let sameConditionNegation := Eq.mp
    (congrArg signature.Negation sameCondition.symm)
    vocabulary.conditionIdentity.negation
  let sameConditionDisjunction := Eq.mp
    (congrArg signature.Disjunction sameCondition.symm)
    vocabulary.conditionIdentity.disjunction
  let forwardConsequenceDisjunction := Eq.mp
    (congrArg signature.Disjunction forwardConsequenceEquality.symm)
    uniquenessDisjunction
  let forwardOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction forwardOuterEquality.symm)
    uniquenessDisjunction
  have forwardSumRule := star14_sumCertifiedRule uniquenessNegation
    uniquenessDisjunction pAtWitness rightPsiB rightScope
    (.neg vocabulary.conditionIdentity.negation rightPsiB)
    stableRightReverse psiB rightAtWitness targetToRight
    (.neg vocabulary.conditionIdentity.negation psiB)
    vocabulary.conditionIdentity.negation conditionUniquenessDisjunction
    conditionUniquenessNegation sameConditionNegation
    sameConditionDisjunction conditionUniquenessDisjunction
    forwardConsequenceDisjunction forwardOuterDisjunction
    vocabulary.conditionIdentity.negation
    (ImplicationNegation.star_1_01
      vocabulary.conditionIdentity.negation rightPsiB)
    stableRightReverseDefinition targetDisjunctionDefinition
    rightDisjunctionDefinition targetNegationDefinition
    targetToRightDefinition
  have line2LiftedForward := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis stableRightReverse targetToRight
    line2Forward forwardSumRule
  let reverseConsequenceEquality :
      max (max conditionOrder uniquenessOrder)
          (max conditionOrder conditionOrder) = uniquenessOrder :=
    Eq.trans
      (congrArg (fun right => max
        (max conditionOrder uniquenessOrder) right) sameCondition)
      (Eq.trans
        (MixedOrder.maxLeftRightAbsorb conditionOrder uniquenessOrder)
        lowHigh)
  let reverseOuterEquality :
      max (max uniquenessOrder conditionOrder)
          (max (max conditionOrder uniquenessOrder)
            (max conditionOrder conditionOrder)) = uniquenessOrder :=
    natMaxCongr highLow reverseConsequenceEquality
  let uniquenessConditionDisjunction := Eq.mp
    (congrArg signature.Disjunction highLow.symm) uniquenessDisjunction
  let uniquenessConditionNegation := Eq.mp
    (congrArg signature.Negation highLow.symm) uniquenessNegation
  let reverseConsequenceDisjunction := Eq.mp
    (congrArg signature.Disjunction reverseConsequenceEquality.symm)
    uniquenessDisjunction
  let reverseOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction reverseOuterEquality.symm)
    uniquenessDisjunction
  have reverseSumRule := star14_sumCertifiedRule uniquenessNegation
    uniquenessDisjunction pAtWitness rightScope rightPsiB
    stableRightNegated stableRightForward rightAtWitness psiB
    rightToTarget (.neg uniquenessNegation rightAtWitness)
    uniquenessNegation uniquenessConditionDisjunction
    uniquenessConditionNegation conditionUniquenessNegation
    conditionUniquenessDisjunction sameConditionDisjunction
    reverseConsequenceDisjunction reverseOuterDisjunction
    uniquenessNegation stableRightNegationDefinition
    stableRightForwardDefinition rightDisjunctionDefinition
    targetDisjunctionDefinition rightNegatedDefinition
    rightToTargetDefinition
  have line2LiftedReverse := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis stableRightForward rightToTarget
    line2Reverse reverseSumRule
  let leftNegated := star_9_02
    logicalVocabulary.applicationExistential.universal
    applicationBodyNegation applicationBody
  let stableLeftNegated := Eq.mp (congrArg
    (Formula signature (sort :: real) []) applicationResultStability)
    leftNegated
  have leftNegationDefinition : ImplicationNegation signature
      (sort :: real) logicalVocabulary.applicationExistential.outerNegation
      psiDescription leftNegated := by
    unfold psiDescription leftNegated
    exact ImplicationNegation.star_9_02
      logicalVocabulary.applicationExistential.outerNegation
      logicalVocabulary.applicationExistential
      logicalVocabulary.applicationExistential.universal
      applicationBodyNegation applicationBody
  rw [applicationOuterNegationSource] at leftNegationDefinition
  have stableLeftNegationDefinition : ImplicationNegation signature
      (sort :: real) uniquenessNegation leftScope stableLeftNegated := by
    exact star14_castImplicationNegationOrder applicationResultStability
      uniquenessNegation psiDescription leftNegated leftNegationDefinition
  have leftForwardDefinition : ImplicationDisjunction signature
      (sort :: real) leftNegated psiB forward := by
    unfold forward leftNegated
    apply star14_castImplicationDisjunctionResult forwardEquality
    unfold star_10_23_right
    exact ImplicationDisjunction.star_9_03
      logicalVocabulary.applicationExistential.universal
      vocabulary.applicationImplicationUniversal
      (.neg applicationBodyNegation applicationBody) psiB
      (.disj applicationPsiDisjunction
        (.neg applicationBodyNegation applicationBody)
        (psiB.rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01 applicationPsiDisjunction
        (.neg applicationBodyNegation applicationBody)
        (psiB.rename (fun v => .succ v)))
  have stableLeftForwardDefinition : ImplicationDisjunction signature
      (sort :: real) stableLeftNegated psiB stableForward := by
    unfold stableLeftNegated stableForward
    exact star14_castImplicationDisjunctionLeftOrder
      applicationResultStability leftNegated forward psiB
      leftForwardDefinition
  have leftReverseDefinition : ImplicationDisjunction signature
      (sort :: real) (.neg vocabulary.conditionIdentity.negation psiB)
      psiDescription reverse := by
    unfold reverse star14_normalizedDisjunction
    apply star14_castImplicationDisjunctionResult reverseEquality
    exact ImplicationDisjunction.star_1_01
      (Eq.mp (congrArg signature.Disjunction reverseEquality.symm)
        logicalVocabulary.applicationResultDisjunction)
      (.neg vocabulary.conditionIdentity.negation psiB) psiDescription
  have stableLeftReverseDefinition : ImplicationDisjunction signature
      (sort :: real) (.neg vocabulary.conditionIdentity.negation psiB)
      leftScope stableReverse := by
    unfold leftScope stableReverse
    exact star14_castImplicationDisjunctionOrder
      applicationResultStability
      (.neg vocabulary.conditionIdentity.negation psiB)
      psiDescription reverse leftReverseDefinition
  let stableBind := star14_bindOrderStable identityOrder sort
  let applicationUniquenessEquality :
      max applicationOrder uniquenessOrder = uniquenessOrder :=
    natMaxCongr applicationStability rfl
  let leftToRightUniversal := Eq.mp
    (congrArg (signature.Universal sort)
      applicationUniquenessEquality.symm)
    (Eq.mp (congrArg (signature.Universal sort) applicationStability)
      logicalVocabulary.applicationExistential.universal)
  let leftToRightDisjunction := Eq.mp
    (congrArg signature.Disjunction applicationUniquenessEquality.symm)
    uniquenessDisjunction
  let leftToRightRaw := star_10_23_right
    logicalVocabulary.applicationExistential
    logicalVocabulary.applicationExistential.universal leftToRightUniversal
    applicationBodyNegation leftToRightDisjunction applicationBody
    rightAtWitness
  let leftToRightEquality := Eq.trans
    (congrArg (fun matrixOrder => bindOrder matrixOrder sort)
      applicationUniquenessEquality) stableBind
  let leftToRight := Eq.mp (congrArg
    (Formula signature (sort :: real) []) leftToRightEquality)
    leftToRightRaw
  have leftToRightRawDefinition : ImplicationDisjunction signature
      (sort :: real) leftNegated rightAtWitness leftToRightRaw := by
    unfold leftToRightRaw leftNegated star_10_23_right
    exact ImplicationDisjunction.star_9_03
      logicalVocabulary.applicationExistential.universal leftToRightUniversal
      (.neg applicationBodyNegation applicationBody) rightAtWitness
      (.disj leftToRightDisjunction
        (.neg applicationBodyNegation applicationBody)
        (rightAtWitness.rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01 leftToRightDisjunction
        (.neg applicationBodyNegation applicationBody)
        (rightAtWitness.rename (fun v => .succ v)))
  have leftToRightDefinition : ImplicationDisjunction signature
      (sort :: real) stableLeftNegated rightAtWitness leftToRight := by
    unfold stableLeftNegated leftToRight
    exact star14_castImplicationDisjunctionMixed
      applicationResultStability leftToRightEquality leftNegated
      rightAtWitness leftToRightRaw leftToRightRawDefinition
  let sameUniqueness := natMaxSelf uniquenessOrder
  let chainConsequenceEquality :
      max (max uniquenessOrder conditionOrder)
          (max uniquenessOrder uniquenessOrder) = uniquenessOrder :=
    natMaxCongr highLow sameUniqueness
  let chainOuterEquality :
      max (max conditionOrder uniquenessOrder)
          (max (max uniquenessOrder conditionOrder)
            (max uniquenessOrder uniquenessOrder)) = uniquenessOrder :=
    natMaxCongr lowHigh chainConsequenceEquality
  let sameUniquenessDisjunction := Eq.mp
    (congrArg signature.Disjunction sameUniqueness.symm)
    uniquenessDisjunction
  let chainConsequenceDisjunction := Eq.mp
    (congrArg signature.Disjunction chainConsequenceEquality.symm)
    uniquenessDisjunction
  let chainOuterDisjunction := Eq.mp
    (congrArg signature.Disjunction chainOuterEquality.symm)
    uniquenessDisjunction
  have leftChainRule := star14_syllCertifiedRule uniquenessNegation
    uniquenessDisjunction leftScope psiB rightAtWitness
    stableLeftNegated (.neg vocabulary.conditionIdentity.negation psiB)
    stableForward targetToRight leftToRight uniquenessNegation
    vocabulary.conditionIdentity.negation conditionUniquenessDisjunction
    conditionUniquenessNegation uniquenessConditionNegation
    uniquenessConditionDisjunction sameUniquenessDisjunction
    chainConsequenceDisjunction chainOuterDisjunction
    stableLeftNegationDefinition targetNegationDefinition
    stableLeftForwardDefinition targetToRightDefinition
    leftToRightDefinition
  have leftChainUnder := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis targetToRight
    (implication uniquenessNegation uniquenessDisjunction
      stableForward leftToRight) line2LiftedForward leftChainRule
  have leftChainPair := star14_joinUnder uniquenessNegation
    uniquenessDisjunction hypothesis stableForward
    (implication uniquenessNegation uniquenessDisjunction
      stableForward leftToRight) line1Forward leftChainUnder
  have finalForward := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction stableForward
      (implication uniquenessNegation uniquenessDisjunction
        stableForward leftToRight)) leftToRight leftChainPair
    (star_3_35 uniquenessNegation uniquenessDisjunction
      stableForward leftToRight)
  let rightToLeft := implication uniquenessNegation uniquenessDisjunction
    rightAtWitness leftScope
  have rightToLeftNegationDefinition : ImplicationNegation signature
      (sort :: real) uniquenessNegation rightAtWitness
      (.neg uniquenessNegation rightAtWitness) :=
    ImplicationNegation.star_1_01 uniquenessNegation rightAtWitness
  have rightToLeftDisjunctionDefinition : ImplicationDisjunction signature
      (sort :: real) (.neg uniquenessNegation rightAtWitness)
      leftScope rightToLeft :=
    ImplicationDisjunction.star_1_01_same uniquenessDisjunction
      (.neg uniquenessNegation rightAtWitness) leftScope
  have rightChainRule := star14_syllCertifiedRule uniquenessNegation
    uniquenessDisjunction rightAtWitness psiB leftScope
    (.neg uniquenessNegation rightAtWitness)
    (.neg vocabulary.conditionIdentity.negation psiB)
    rightToTarget stableReverse rightToLeft uniquenessNegation
    vocabulary.conditionIdentity.negation conditionUniquenessDisjunction
    conditionUniquenessNegation uniquenessConditionNegation
    uniquenessConditionDisjunction sameUniquenessDisjunction
    chainConsequenceDisjunction chainOuterDisjunction
    rightToLeftNegationDefinition targetNegationDefinition
    rightToTargetDefinition stableLeftReverseDefinition
    rightToLeftDisjunctionDefinition
  have rightChainUnder := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis stableReverse
    (implication uniquenessNegation uniquenessDisjunction
      rightToTarget rightToLeft) line1Reverse rightChainRule
  have rightChainPair := star14_joinUnder uniquenessNegation
    uniquenessDisjunction hypothesis rightToTarget
    (implication uniquenessNegation uniquenessDisjunction
      rightToTarget rightToLeft) line2LiftedReverse rightChainUnder
  have finalReverse := star14_composeSame uniquenessNegation
    uniquenessDisjunction hypothesis
    (conjunction uniquenessNegation uniquenessDisjunction rightToTarget
      (implication uniquenessNegation uniquenessDisjunction
        rightToTarget rightToLeft)) rightToLeft rightChainPair
    (star_3_35 uniquenessNegation uniquenessDisjunction
      rightToTarget rightToLeft)
  have line3 := star14_joinUnder uniquenessNegation uniquenessDisjunction
    hypothesis leftToRight rightToLeft finalForward finalReverse
  let originalX : Term signature real [sort, sort] sort := .apparent .zero
  let originalCandidate : Term signature real [sort, sort] sort :=
    .apparent (.succ .zero)
  let originalConditionUnderCandidate : Formula signature real [sort, sort]
      identityOrder := condition.rename
    (liftRenaming (fun v => .succ v))
  let originalUniquenessMatrix := Formula.always
    vocabulary.identityUniversal
    (equivalence vocabulary.identityNegation vocabulary.identityDisjunction
      originalConditionUnderCandidate
      (star_13_01 vocabulary.conditionIdentity originalX originalCandidate))
  let originalLeftBody := mixedConjunction uniquenessNegation
    vocabulary.conditionIdentity.negation applicationBodyNegation
    logicalVocabulary.applicationBodyDisjunction originalUniquenessMatrix
    leftMatrix
  let originalRightBody := mixedConjunction uniquenessNegation
    vocabulary.conditionIdentity.negation applicationBodyNegation
    logicalVocabulary.applicationBodyDisjunction originalUniquenessMatrix chi
  let originalLeftScope := Eq.mp (congrArg
    (Formula signature real []) applicationResultStability)
    (Formula.sometimes logicalVocabulary.applicationExistential
      originalLeftBody)
  let originalRightScope := Eq.mp (congrArg
    (Formula signature real []) applicationResultStability)
    (Formula.sometimes logicalVocabulary.applicationExistential
      originalRightBody)
  let originalRightSide := star14_normalizedDisjunction lowHigh
    uniquenessDisjunction p originalRightScope
  let originalLeftToRightRaw := star_10_23_right
    logicalVocabulary.applicationExistential
    logicalVocabulary.applicationExistential.universal leftToRightUniversal
    applicationBodyNegation leftToRightDisjunction originalLeftBody
    originalRightSide
  let originalLeftToRight := Eq.mp (congrArg
    (Formula signature real []) leftToRightEquality)
    originalLeftToRightRaw
  let originalRightToLeft := implication uniquenessNegation
    uniquenessDisjunction originalRightSide originalLeftScope
  let originalConclusion := conjunction uniquenessNegation
    uniquenessDisjunction originalLeftToRight originalRightToLeft
  have originalUniquenessWeaken : originalUniquenessMatrix.weakenReal =
      uniquenessMatrixAtWitness := by
    unfold originalUniquenessMatrix uniquenessMatrixAtWitness
      originalConditionUnderCandidate conditionUnderCandidate
      conditionAtWitness originalX originalCandidate functionX candidate
    change Formula.always vocabulary.identityUniversal
      ((equivalence vocabulary.identityNegation
        vocabulary.identityDisjunction
        (condition.rename (liftRenaming (fun v => .succ v)))
        (star_13_01 vocabulary.conditionIdentity (.apparent .zero)
          (.apparent (.succ .zero)))).weakenReal) = _
    rw [star14_matrixEquivalence_weakenReal,
      Formula.weakenReal_rename, star14_identity_weakenReal]
    rfl
  have originalLeftBodyWeaken : originalLeftBody.weakenReal =
      applicationBody := by
    unfold originalLeftBody applicationBody leftMatrixAtWitness
    rw [star14_mixedConjunction_weakenReal, originalUniquenessWeaken]
  have originalRightBodyWeaken : originalRightBody.weakenReal =
      rightApplicationBody := by
    unfold originalRightBody rightApplicationBody rightMatrixAtWitness
    rw [star14_mixedConjunction_weakenReal, originalUniquenessWeaken]
  have originalLeftScopeWeaken : originalLeftScope.weakenReal =
      leftScope := by
    unfold originalLeftScope leftScope psiDescription
    have line4 := Formula.weakenReal_cast (fresh := sort)
      applicationResultStability
      (Formula.sometimes logicalVocabulary.applicationExistential
        originalLeftBody)
    rw [star14_sometimes_weakenReal, originalLeftBodyWeaken] at line4
    exact line4
  have originalRightScopeWeaken : originalRightScope.weakenReal =
      rightScope := by
    unfold originalRightScope rightScope rightDescription
    have line4 := Formula.weakenReal_cast (fresh := sort)
      applicationResultStability
      (Formula.sometimes logicalVocabulary.applicationExistential
        originalRightBody)
    rw [star14_sometimes_weakenReal, originalRightBodyWeaken] at line4
    exact line4
  have originalRightSideWeaken : originalRightSide.weakenReal =
      rightAtWitness := by
    unfold originalRightSide rightAtWitness
    rw [star14_normalizedDisjunction_weakenReal,
      originalRightScopeWeaken]
  have originalLeftToRightRawWeaken :
      originalLeftToRightRaw.weakenReal = leftToRightRaw := by
    unfold originalLeftToRightRaw leftToRightRaw
    rw [star14_10_23_right_weakenReal, originalLeftBodyWeaken,
      originalRightSideWeaken]
  have originalLeftToRightWeaken : originalLeftToRight.weakenReal =
      leftToRight := by
    unfold originalLeftToRight leftToRight
    have line4 := Formula.weakenReal_cast (fresh := sort)
      leftToRightEquality originalLeftToRightRaw
    rw [originalLeftToRightRawWeaken] at line4
    exact line4
  have originalRightToLeftWeaken : originalRightToLeft.weakenReal =
      rightToLeft := by
    unfold originalRightToLeft rightToLeft
    rw [implication_weakenReal, originalRightSideWeaken,
      originalLeftScopeWeaken]
  have originalConclusionWeaken : originalConclusion.weakenReal =
      conjunction uniquenessNegation uniquenessDisjunction
        leftToRight rightToLeft := by
    unfold originalConclusion
    rw [star14_conjunction_weakenReal,
      originalLeftToRightWeaken, originalRightToLeftWeaken]
  have originalUniquenessAtWitness :
      originalUniquenessMatrix.weakenReal.instantiate witness =
        hypothesis := by
    unfold originalUniquenessMatrix hypothesis
      originalConditionUnderCandidate conditionAtWitness
      originalX originalCandidate x witness
    change (Formula.always vocabulary.identityUniversal
      ((equivalence vocabulary.identityNegation
        vocabulary.identityDisjunction
        (condition.rename (liftRenaming (fun v => .succ v)))
        (star_13_01 vocabulary.conditionIdentity (.apparent .zero)
          (.apparent (.succ .zero)))).weakenReal)).instantiate
      (.real (.zero : Var (sort :: real) sort)) = _
    rw [Formula.instantiate, substitute_always,
      star14_matrixEquivalence_weakenReal,
      star14_matrixEquivalence_substitute]
    rw [star14_conditionUnderCandidate_instantiate]
    rw [star14_identity_weakenReal, star14_identity_substitute]
    rfl
  let originalMatrix := implication uniquenessNegation
    uniquenessDisjunction originalUniquenessMatrix
    (originalConclusion.rename (fun v => .succ v))
  have originalMatrixAtWitness :
      originalMatrix.weakenReal.instantiate witness =
        implication uniquenessNegation uniquenessDisjunction hypothesis
          (conjunction uniquenessNegation uniquenessDisjunction
            leftToRight rightToLeft) := by
    unfold originalMatrix
    rw [implication_weakenReal, Formula.instantiate,
      implication_substitute]
    change implication uniquenessNegation uniquenessDisjunction
      (originalUniquenessMatrix.weakenReal.instantiate witness)
      (((originalConclusion.rename (fun v => .succ v)).weakenReal).instantiate
        witness) = _
    rw [originalUniquenessAtWitness,
      Formula.closed_weakenReal_instantiate, originalConclusionWeaken]
  have line4 := Derivation.star_9_13
    (Eq.mp (congrArg (signature.Universal sort) identityStability.symm)
      vocabulary.identityUniversal)
    originalMatrix
    (Derivation.castAssertion originalMatrixAtWitness line3)
  have line5 := star14_castAssertionOrder stableBind
    (.always
      (Eq.mp (congrArg (signature.Universal sort) identityStability.symm)
        vocabulary.identityUniversal)
      originalMatrix) line4
  let finalFormula := star14_31_full_formula
    vocabulary.identityUniversal vocabulary.conditionIdentity
    vocabulary.identityNegation vocabulary.identityDisjunction
    logicalVocabulary.applicationExistential
    logicalVocabulary.applicationBodyDisjunction condition chi p
  have line6 : Derivation (.assertion finalFormula) := by
    unfold finalFormula star14_31_full_formula
    exact line5
  have line7 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line6
    (star_3_2 uniquenessNegation uniquenessDisjunction
      finalFormula printed14Formula)
  have line8 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction printed14 line7
  have line9 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line8
    (star_3_26 uniquenessNegation uniquenessDisjunction
      finalFormula printed14Formula)
  have line10 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line9
    (star_3_2 uniquenessNegation uniquenessDisjunction
      finalFormula printed10Formula)
  have line11 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction printed10 line10
  have line12 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line11
    (star_3_26 uniquenessNegation uniquenessDisjunction
      finalFormula printed10Formula)
  have line13 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line12
    (star_3_2 uniquenessNegation uniquenessDisjunction
      finalFormula printed4Formula)
  have line14 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction printed4 line13
  have line15 := Derivation.star_9_12_same uniquenessNegation
    uniquenessDisjunction line14
    (star_3_26 uniquenessNegation uniquenessDisjunction
      finalFormula printed4Formula)
  exact line15

/-- Stable-order form of the printed specialization rule ✱10·1. -/
private theorem star14_saturatedSpecialize
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort))
    (value : Term signature real [] sort) :
    Derivation (.assertion (implication negation disjunction
      (star14_saturatedUniversal universal body) (body.instantiate value))) := by
  let bindEquality := star14_bindOrderStable baseOrder sort
  let resultEquality := natMaxCongr bindEquality rfl
  let rawNegation := Eq.mp
    (congrArg signature.Negation bindEquality.symm) negation
  let rawDisjunction := Eq.mp
    (congrArg signature.Disjunction resultEquality.symm) disjunction
  let rawFormula := mixedImplication rawNegation rawDisjunction
    (.always universal body) (body.instantiate value)
  have line1 : Derivation (.assertion rawFormula) :=
    star_10_1 universal rawNegation rawDisjunction body value
  have line2 := star14_castAssertionOrder resultEquality rawFormula line1
  have line3 : Eq.mp (congrArg (Formula signature real []) resultEquality)
      rawFormula = implication negation disjunction
        (star14_saturatedUniversal universal body)
        (body.instantiate value) := by
    exact mixedImplication_normalizeSameOrder bindEquality rfl
      negation disjunction (.always universal body) (body.instantiate value)
  exact Derivation.castAssertion line3.symm line2

/-- Uniqueness matrix `(x) : φx ≡ x=b` used by ✱14·12. -/
private def star14_12_uniquenessMatrix
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0))) :=
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) identityStability.symm)
    vocabulary.identityUniversal
  let stableNegation := Eq.mp
    (congrArg signature.Negation identityStability.symm)
    vocabulary.identityNegation
  let stableDisjunction := Eq.mp
    (congrArg signature.Disjunction identityStability.symm)
    vocabulary.identityDisjunction
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let candidate : Term signature real [sort, sort] sort :=
    .apparent (.succ .zero)
  let conditionUnderCandidate := condition.rename
    (liftRenaming (fun v => .succ v))
  let stableCondition := Eq.mp
    (congrArg (Formula signature real [sort, sort]) identityStability.symm)
    conditionUnderCandidate
  let stableIdentity := Eq.mp
    (congrArg (Formula signature real [sort, sort]) identityStability.symm)
    (star_13_01 vocabulary.conditionIdentity x candidate)
  star14_saturatedUniversal stableUniversal
    (equivalence stableNegation stableDisjunction
      stableCondition stableIdentity)

/-- Double-universal uniqueness consequence printed on the right of ✱14·12. -/
private def star14_12_uniqueness
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0))) :=
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) identityStability.symm)
    vocabulary.identityUniversal
  let stableNegation := Eq.mp
    (congrArg signature.Negation identityStability.symm)
    vocabulary.identityNegation
  let stableDisjunction := Eq.mp
    (congrArg signature.Disjunction identityStability.symm)
    vocabulary.identityDisjunction
  let stableCondition := Eq.mp
    (congrArg (Formula signature real [sort]) identityStability.symm)
    condition
  let conditionY := stableCondition.rename (fun v => .succ v)
  let conditionX := conditionY.swapHeads
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let y : Term signature real [sort, sort] sort :=
    .apparent (.succ .zero)
  let identityXY := Eq.mp
    (congrArg (Formula signature real [sort, sort]) identityStability.symm)
    (star_13_01 vocabulary.conditionIdentity x y)
  let matrix := implication stableNegation stableDisjunction
    (conjunction stableNegation stableDisjunction conditionX conditionY)
    identityXY
  star14_saturatedUniversal stableUniversal
    (star14_saturatedUniversal stableUniversal matrix)

/-- Literal contextual AST of ✱14·12. -/
def star_14_12_formula
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0))) :=
  let logicalVocabulary := star_14_15_logicalVocabulary
    vocabulary.identityUniversal vocabulary.identityNegation
    vocabulary.identityDisjunction vocabulary.continuationIdentityNegation
    vocabulary.continuationIdentityDisjunction vocabulary.descriptionPrinted
    vocabulary.descriptionUniversal vocabulary.applicationPrinted
    vocabulary.applicationUniversal
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let stableNegation := Eq.mp
    (congrArg signature.Negation identityStability.symm)
    vocabulary.identityNegation
  let stableDisjunction := Eq.mp
    (congrArg signature.Disjunction identityStability.symm)
    vocabulary.identityDisjunction
  let applicationStability := star14_applicationOrderStable conditionOrder sort
  let uniquenessExistential := Eq.mp
    (congrArg (ExistentialVocabulary signature sort) applicationStability)
    logicalVocabulary.applicationExistential
  let uniquenessMatrix := star14_12_uniquenessMatrix vocabulary condition
  let descriptionExists := Eq.mp (congrArg (Formula signature real [])
    (star14_bindOrderStable identityOrder sort))
    (star_14_11_left uniquenessExistential uniquenessMatrix)
  implication stableNegation stableDisjunction descriptionExists
    (star14_12_uniqueness vocabulary condition)

/-- Audited scope reading of ✱14·12. -/
def star_14_12_reading
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0))) :
    ClaimReading signature real where
  printed := "⊢ : E!(℩x)(φx) .⊃ : φx . φy .⊃ₓ,ᵧ. x = y"
  parsed := .assertion (star_14_12_formula vocabulary condition)

private theorem star14_12_pointwise
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (b z w : Term signature real [] sort) :
    let identityOrder := bindOrder conditionOrder
      (.function [sort] conditionOrder 0)
    let uniquenessOrder := bindOrder identityOrder sort
    let identityStability := star14_identityOrderStable conditionOrder sort
    let stableNegation := Eq.mp
      (congrArg signature.Negation identityStability.symm)
      vocabulary.identityNegation
    let stableDisjunction := Eq.mp
      (congrArg signature.Disjunction identityStability.symm)
      vocabulary.identityDisjunction
    let stableCondition := Eq.mp
      (congrArg (Formula signature real [sort]) identityStability.symm)
      condition
    let conditionZ := stableCondition.instantiate z
    let conditionW := stableCondition.instantiate w
    let identityZW := Eq.mp
      (congrArg (Formula signature real []) identityStability.symm)
      (star_13_01 vocabulary.conditionIdentity z w)
    Derivation (.assertion (implication stableNegation stableDisjunction
      ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
      (implication stableNegation stableDisjunction
        (conjunction stableNegation stableDisjunction conditionZ conditionW)
        identityZW))) := by
  dsimp only
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) identityStability.symm)
    vocabulary.identityUniversal
  let stableNegation := Eq.mp
    (congrArg signature.Negation identityStability.symm)
    vocabulary.identityNegation
  let stableDisjunction := Eq.mp
    (congrArg signature.Disjunction identityStability.symm)
    vocabulary.identityDisjunction
  let stableCondition := Eq.mp
    (congrArg (Formula signature real [sort]) identityStability.symm)
    condition
  let conditionZ := stableCondition.instantiate z
  let conditionW := stableCondition.instantiate w
  let identityZB := Eq.mp
    (congrArg (Formula signature real []) identityStability.symm)
    (star_13_01 vocabulary.conditionIdentity z b)
  let identityWB := Eq.mp
    (congrArg (Formula signature real []) identityStability.symm)
    (star_13_01 vocabulary.conditionIdentity w b)
  let identityZW := Eq.mp
    (congrArg (Formula signature real []) identityStability.symm)
    (star_13_01 vocabulary.conditionIdentity z w)
  let x : Term signature real [sort] sort := .apparent .zero
  let bodyZ := equivalence stableNegation stableDisjunction stableCondition
    (Eq.mp (congrArg (Formula signature real [sort]) identityStability.symm)
      (star_13_01 vocabulary.conditionIdentity x b.weaken))
  let uniquenessAt := star14_saturatedUniversal stableUniversal bodyZ
  have uniquenessAtShape :
      (star14_12_uniquenessMatrix vocabulary condition).instantiate b =
        uniquenessAt := by
    unfold star14_12_uniquenessMatrix uniquenessAt bodyZ
      star14_saturatedUniversal Formula.instantiate
    rw [Formula.substitute_cast (star14_bindOrderStable identityOrder sort),
      substitute_always,
      star14_matrixEquivalence_substitute,
      Formula.substitute_cast identityStability.symm,
      Formula.substitute_cast identityStability.symm,
      star14_conditionUnderCandidate_instantiateClosed,
      star14_identity_substitute]
    cases b <;> rfl
  have line1z := star14_saturatedSpecialize stableUniversal stableNegation
    stableDisjunction bodyZ z
  have line1w := star14_saturatedSpecialize stableUniversal stableNegation
    stableDisjunction bodyZ w
  have bodyZAt : bodyZ.instantiate z =
      star_4_01 stableNegation stableDisjunction conditionZ identityZB := by
    unfold bodyZ conditionZ identityZB Formula.instantiate
    rw [star14_matrixEquivalence_substitute,
      Formula.substitute_cast identityStability.symm,
      Formula.substitute_cast identityStability.symm,
      star14_identity_substitute]
    cases z <;> cases b <;> rfl
  have bodyWAt : bodyZ.instantiate w =
      star_4_01 stableNegation stableDisjunction conditionW identityWB := by
    unfold bodyZ conditionW identityWB Formula.instantiate
    rw [star14_matrixEquivalence_substitute,
      Formula.substitute_cast identityStability.symm,
      Formula.substitute_cast identityStability.symm,
      star14_identity_substitute]
    cases w <;> cases b <;> rfl
  rw [bodyZAt] at line1z
  rw [bodyWAt] at line1w
  change Derivation (.assertion (implication stableNegation stableDisjunction
    uniquenessAt
    (star_4_01 stableNegation stableDisjunction conditionZ identityZB)))
    at line1z
  change Derivation (.assertion (implication stableNegation stableDisjunction
    uniquenessAt
    (star_4_01 stableNegation stableDisjunction conditionW identityWB)))
    at line1w
  rw [← uniquenessAtShape] at line1z line1w
  have line2z := star14_composeSame stableNegation stableDisjunction
    ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
    (star_4_01 stableNegation stableDisjunction conditionZ identityZB)
    (implication stableNegation stableDisjunction conditionZ identityZB)
    line1z
    (star_3_26 stableNegation stableDisjunction
      (implication stableNegation stableDisjunction conditionZ identityZB)
      (implication stableNegation stableDisjunction identityZB conditionZ))
  have line2w := star14_composeSame stableNegation stableDisjunction
    ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
    (star_4_01 stableNegation stableDisjunction conditionW identityWB)
    (implication stableNegation stableDisjunction conditionW identityWB)
    line1w
    (star_3_26 stableNegation stableDisjunction
      (implication stableNegation stableDisjunction conditionW identityWB)
      (implication stableNegation stableDisjunction identityWB conditionW))
  have line3a := star14_joinUnder stableNegation stableDisjunction
    ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
    (implication stableNegation stableDisjunction conditionZ identityZB)
    (implication stableNegation stableDisjunction conditionW identityWB)
    line2z line2w
  have line3 := star14_composeSame stableNegation stableDisjunction
    ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
    (conjunction stableNegation stableDisjunction
      (implication stableNegation stableDisjunction conditionZ identityZB)
      (implication stableNegation stableDisjunction conditionW identityWB))
    (implication stableNegation stableDisjunction
      (conjunction stableNegation stableDisjunction conditionZ conditionW)
      (conjunction stableNegation stableDisjunction identityZB identityWB))
    line3a (star_3_47 stableNegation stableDisjunction
      conditionZ conditionW identityZB identityWB)
  let identityBaseEquality : max identityOrder conditionOrder = identityOrder := by
    unfold identityOrder bindOrder
    exact star14_max_eq_left_of_le
      (star14_le_max_left conditionOrder
        (Nat.succ (RSort.height (.function [sort] conditionOrder 0))))
  let identityBaseNegation := Eq.mp
    (congrArg signature.Negation identityBaseEquality.symm)
    vocabulary.identityNegation
  let identityBaseDisjunction := Eq.mp
    (congrArg signature.Disjunction identityBaseEquality.symm)
    vocabulary.identityDisjunction
  have line4Raw := star_13_172 vocabulary.conditionIdentity
    vocabulary.conditionReducibility.reducibilityExistential
    vocabulary.conditionReducibility.argumentUniversal
    vocabulary.identityNegation vocabulary.identityDisjunction
    identityBaseDisjunction
    vocabulary.conditionReducibility.reducibilityNegation
    vocabulary.conditionReducibility.reducibilityIdentityNegation
    vocabulary.conditionReducibility.reducibilityBaseNegation
    identityBaseNegation
    vocabulary.conditionReducibility.substitutionResultNegation
    vocabulary.conditionReducibility.reducibilityDisjunction
    vocabulary.conditionReducibility.reducibilityIdentityDisjunction
    vocabulary.conditionReducibility.reducibilityBaseDisjunction
    vocabulary.conditionReducibility.substitutionResultDisjunction
    vocabulary.conditionReducibility.reducibilityScopeUniversal
    vocabulary.conditionReducibility.reducibilityScopeNegation
    vocabulary.conditionReducibility.reducibilityScopeDisjunction
    vocabulary.conditionReducibility.existentialTargetDisjunction
    vocabulary.conditionReducibility.equivalenceScopeUniversal
    vocabulary.conditionReducibility.symmetryScopeUniversal
    vocabulary.conditionReducibility.scopedNegation
    vocabulary.conditionReducibility.scopedConsequenceDisjunction
    vocabulary.conditionReducibility.scopedOuterDisjunction b z w
  let rawIdentityZB := star_13_01 vocabulary.conditionIdentity z b
  let rawIdentityWB := star_13_01 vocabulary.conditionIdentity w b
  let rawIdentityZW := star_13_01 vocabulary.conditionIdentity z w
  let rawLine4Formula := implication vocabulary.identityNegation
    vocabulary.identityDisjunction
    (conjunction vocabulary.identityNegation vocabulary.identityDisjunction
      rawIdentityZB rawIdentityWB) rawIdentityZW
  change Derivation (.assertion rawLine4Formula) at line4Raw
  have line4Cast := star14_castAssertionOrder identityStability.symm
    rawLine4Formula line4Raw
  have identityNegationSource : vocabulary.identityNegation =
      Eq.mp (congrArg signature.Negation identityStability)
        stableNegation := by
    unfold stableNegation
    exact Eq.trans
      (star14_cast_self
        (Eq.trans identityStability.symm identityStability)
        vocabulary.identityNegation).symm
      (star14_cast_trans identityStability.symm identityStability
        vocabulary.identityNegation)
  have identityDisjunctionSource : vocabulary.identityDisjunction =
      Eq.mp (congrArg signature.Disjunction identityStability)
        stableDisjunction := by
    unfold stableDisjunction
    exact Eq.trans
      (star14_cast_self
        (Eq.trans identityStability.symm identityStability)
        vocabulary.identityDisjunction).symm
      (star14_cast_trans identityStability.symm identityStability
        vocabulary.identityDisjunction)
  have line4Normalization :
      Eq.mp (congrArg (Formula signature real []) identityStability.symm)
        rawLine4Formula = implication stableNegation stableDisjunction
          (conjunction stableNegation stableDisjunction identityZB identityWB)
          identityZW := by
    unfold rawLine4Formula
    rw [identityNegationSource, identityDisjunctionSource]
    unfold identityZB identityWB identityZW
    have line4 := star14_implication_castOrder identityStability.symm
      stableNegation stableDisjunction
      (conjunction
        (Eq.mp (congrArg signature.Negation identityStability)
          stableNegation)
        (Eq.mp (congrArg signature.Disjunction identityStability)
          stableDisjunction) rawIdentityZB rawIdentityWB)
      rawIdentityZW
    rw [star14_conjunction_castOrder identityStability.symm] at line4
    exact line4
  rw [line4Normalization] at line4Cast
  have line5 := Derivation.star_9_12_same stableNegation stableDisjunction
    line4Cast (star_2_05 stableNegation stableDisjunction
      (conjunction stableNegation stableDisjunction conditionZ conditionW)
      (conjunction stableNegation stableDisjunction identityZB identityWB)
      identityZW)
  exact star14_composeSame stableNegation stableDisjunction
    ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
    (implication stableNegation stableDisjunction
      (conjunction stableNegation stableDisjunction conditionZ conditionW)
      (conjunction stableNegation stableDisjunction identityZB identityWB))
    (implication stableNegation stableDisjunction
      (conjunction stableNegation stableDisjunction conditionZ conditionW)
      identityZW) line3 line5

private def star14_substitutionAfterSubstitution
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    Substitution signature real source target :=
  fun v => (sigma v).substitute tau

private theorem star14_term_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (term : Term signature real source sort) :
    (term.substitute sigma).substitute tau =
      term.substitute (star14_substitutionAfterSubstitution sigma tau) := by
  cases term <;> rfl

private theorem star14_arguments_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (arguments : Arguments signature real source sorts) :
    (arguments.substitute sigma).substitute tau =
      arguments.substitute (star14_substitutionAfterSubstitution sigma tau) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [star14_term_substitute_substitute, ih]

private theorem star14_term_weaken_substitute_lift
    (tau : Substitution signature real middle target)
    (term : Term signature real middle sort) :
    term.weaken.substitute (liftSubstitution (sort := binder) tau) =
      (term.substitute tau).weaken := by
  cases term <;> rfl

private theorem star14_liftSubstitution_comp_pointwise
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binder :: source) sort),
      (liftSubstitution sigma v).substitute (liftSubstitution tau) =
        liftSubstitution (star14_substitutionAfterSubstitution sigma tau) v := by
  intro variableSort v
  cases v with
  | zero => rfl
  | succ v => exact star14_term_weaken_substitute_lift tau (sigma v)

private theorem star14_liftSubstitutionN_comp_pointwise
    (binders : List RSort)
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      (liftSubstitutionN binders sigma v).substitute
        (liftSubstitutionN binders tau) =
        liftSubstitutionN binders
          (star14_substitutionAfterSubstitution sigma tau) v := by
  induction binders with
  | nil =>
      intro variableSort v
      rfl
  | cons binder binders ih =>
      intro variableSort v
      cases v with
      | zero => rfl
      | succ v =>
          exact Eq.trans
            (star14_term_weaken_substitute_lift
              (liftSubstitutionN binders tau)
              (liftSubstitutionN binders sigma v))
            (congrArg Term.weaken (ih v))

private theorem star14_liftSubstitution_congr
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binder :: source) sort),
      liftSubstitution sigma v = liftSubstitution tau v := by
  intro variableSort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Term.weaken (pointwise v)

private theorem star14_liftSubstitutionN_congr
    (binders : List RSort)
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftSubstitutionN binders sigma v = liftSubstitutionN binders tau v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih =>
      exact star14_liftSubstitution_congr _ _ ih

private theorem star14_term_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (term : Term signature real source sort) :
    term.substitute sigma = term.substitute tau := by
  cases term with
  | real v => rfl
  | apparent v => exact pointwise v
  | symbol payload => rfl

private theorem star14_arguments_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (arguments : Arguments signature real source sorts) :
    arguments.substitute sigma = arguments.substitute tau := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [star14_term_substitute_of_pointwise sigma tau pointwise, ih]

private theorem star14_formula_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (formula : Formula signature real source order) :
    formula.substitute sigma = formula.substitute tau := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [star14_term_substitute_of_pointwise sigma tau pointwise]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [star14_term_substitute_of_pointwise sigma tau pointwise,
        star14_arguments_substitute_of_pointwise sigma tau pointwise]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      exact congrArg (Formula.neg meaning) (ih sigma tau pointwise)
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH sigma tau pointwise, rightIH sigma tau pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      exact congrArg (Formula.always meaning)
        (ih (liftSubstitution sigma) (liftSubstitution tau)
          (star14_liftSubstitution_congr sigma tau pointwise))
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau)
          (star14_liftSubstitutionN_congr parameters sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (star14_liftSubstitution_congr sigma tau pointwise)]
  | descriptionScope sort conditionOrder scopeOrder condition continuation
      conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftSubstitution sigma) (liftSubstitution tau)
          (star14_liftSubstitution_congr sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (star14_liftSubstitution_congr sigma tau pointwise)]

private theorem star14_formula_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (formula : Formula signature real source order) :
    (formula.substitute sigma).substitute tau =
      formula.substitute (star14_substitutionAfterSubstitution sigma tau) := by
  induction formula generalizing middle target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [star14_term_substitute_substitute]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [star14_term_substitute_substitute,
        star14_arguments_substitute_substitute]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH, rightIH]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      have line1 := ih (liftSubstitution sigma) (liftSubstitution tau)
      have line2 := star14_formula_substitute_of_pointwise
        (star14_substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star14_substitutionAfterSubstitution sigma tau))
        (star14_liftSubstitution_comp_pointwise sigma tau) body
      exact congrArg (Formula.always meaning) (Eq.trans line1 line2)
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      have matrixLine1 := matrixIH (liftSubstitutionN parameters sigma)
        (liftSubstitutionN parameters tau)
      have matrixLine2 := star14_formula_substitute_of_pointwise
        (star14_substitutionAfterSubstitution
          (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau))
        (liftSubstitutionN parameters
          (star14_substitutionAfterSubstitution sigma tau))
        (star14_liftSubstitutionN_comp_pointwise parameters sigma tau) matrix
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := star14_formula_substitute_of_pointwise
        (star14_substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star14_substitutionAfterSubstitution sigma tau))
        (star14_liftSubstitution_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextMatrix => Formula.incompleteScope kind parameters
          resultOrder excess scopeOrder nextMatrix
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans matrixLine1 matrixLine2))
        (congrArg (Formula.incompleteScope kind parameters resultOrder excess
          scopeOrder
          (matrix.substitute (liftSubstitutionN parameters
            (star14_substitutionAfterSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))
  | descriptionScope sort conditionOrder scopeOrder condition continuation
      conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      have conditionLine1 := conditionIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have conditionLine2 := star14_formula_substitute_of_pointwise
        (star14_substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star14_substitutionAfterSubstitution sigma tau))
        (star14_liftSubstitution_comp_pointwise sigma tau) condition
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := star14_formula_substitute_of_pointwise
        (star14_substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (star14_substitutionAfterSubstitution sigma tau))
        (star14_liftSubstitution_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextCondition => Formula.descriptionScope sort
          conditionOrder scopeOrder nextCondition
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans conditionLine1 conditionLine2))
        (congrArg (Formula.descriptionScope sort conditionOrder scopeOrder
          (condition.substitute (liftSubstitution
            (star14_substitutionAfterSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))

private theorem star14_closedDoubleRename_instantiate₂
    (formula : Formula signature real [] order)
    (left right : Term signature real [] sort) :
    (((formula.rename (emptyRenaming (target := [sort]))).rename
      (fun v => .succ v)).instantiate₂ left right) = formula := by
  unfold Formula.instantiate₂ Formula.instantiate
  rw [Formula.rename_substitute, Formula.rename_substitute,
    star14_formula_substitute_substitute]
  exact Formula.substitute_eq_self formula (fun v => nomatch v)

private theorem star14_succRename_instantiate₂
    (formula : Formula signature real [sort] order)
    (left right : Term signature real [] sort) :
    (formula.rename (fun v => .succ v)).instantiate₂ left right =
      formula.instantiate right := by
  unfold Formula.instantiate₂ Formula.instantiate
  rw [Formula.rename_substitute, star14_formula_substitute_substitute]
  apply star14_formula_substitute_of_pointwise
  intro targetSort v
  cases v with
  | zero => cases left <;> rfl
  | succ v => cases v

private theorem star14_swapSuccRename_instantiate₂
    (formula : Formula signature real [sort] order)
    (left right : Term signature real [] sort) :
    ((formula.rename (fun v => .succ v)).swapHeads).instantiate₂ left right =
      formula.instantiate left := by
  unfold Formula.swapHeads Formula.instantiate₂ Formula.instantiate
  rw [Formula.rename_substitute, Formula.rename_substitute,
    star14_formula_substitute_substitute]
  apply star14_formula_substitute_of_pointwise
  intro targetSort v
  cases v with
  | zero => cases left <;> rfl
  | succ v => cases v

private theorem star14_implication_instantiate₂
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [sort, sort] order)
    (x y : Term signature real [] sort) :
    (implication negation disjunction left right).instantiate₂ x y =
      implication negation disjunction (left.instantiate₂ x y)
        (right.instantiate₂ x y) := by
  unfold Formula.instantiate₂ Formula.instantiate
  rw [implication_substitute, implication_substitute]

private theorem star14_conjunction_instantiate₂
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [sort, sort] order)
    (x y : Term signature real [] sort) :
    (conjunction negation disjunction left right).instantiate₂ x y =
      conjunction negation disjunction (left.instantiate₂ x y)
        (right.instantiate₂ x y) := by
  unfold conjunction Formula.instantiate₂ Formula.instantiate
  dsimp only [Formula.substitute]
  rw [sameDisjunction_substitute, sameDisjunction_substitute]
  dsimp only [Formula.substitute]

/-- Printed ✱11·11·3 closure of the two pointwise variables in ✱14·12. -/
private theorem star14_12_candidate
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (b : Term signature real [] sort) :
    let identityOrder := bindOrder conditionOrder
      (.function [sort] conditionOrder 0)
    let uniquenessOrder := bindOrder identityOrder sort
    let identityStability := star14_identityOrderStable conditionOrder sort
    let stableUniversal := Eq.mp
      (congrArg (signature.Universal sort) identityStability.symm)
      vocabulary.identityUniversal
    let stableNegation := Eq.mp
      (congrArg signature.Negation identityStability.symm)
      vocabulary.identityNegation
    let stableDisjunction := Eq.mp
      (congrArg signature.Disjunction identityStability.symm)
      vocabulary.identityDisjunction
    let sameOrder := natMaxSelf uniquenessOrder
    let inner := Eq.mp (congrArg (signature.Universal sort) sameOrder.symm)
      stableUniversal
    let outerEquality : bindOrder (max uniquenessOrder uniquenessOrder) sort =
        uniquenessOrder := Eq.trans
      (congrArg (fun order => bindOrder order sort) sameOrder)
      (star14_bindOrderStable identityOrder sort)
    let outer := Eq.mp
      (congrArg (signature.Universal sort) outerEquality.symm)
      stableUniversal
    let matrixDisjunction := Eq.mp
      (congrArg signature.Disjunction sameOrder.symm) stableDisjunction
    let p := (star14_12_uniquenessMatrix vocabulary condition).instantiate b
    let conditionY : Formula signature real [sort, sort] uniquenessOrder :=
      (Eq.mp
      (congrArg (Formula signature real [sort]) identityStability.symm)
      condition).rename (fun v => .succ v)
    let conditionX := conditionY.swapHeads
    let x : Term signature real [sort, sort] sort := .apparent .zero
    let y : Term signature real [sort, sort] sort := .apparent (.succ .zero)
    let identityXY := Eq.mp
      (congrArg (Formula signature real [sort, sort]) identityStability.symm)
      (star_13_01 vocabulary.conditionIdentity x y)
    let matrix := implication stableNegation stableDisjunction
      (conjunction stableNegation stableDisjunction conditionX conditionY)
      identityXY
    Derivation (.assertion (star_11_3_left inner outer stableNegation
      matrixDisjunction p matrix)) := by
  dsimp only
  let identityOrder := bindOrder conditionOrder
    (.function [sort] conditionOrder 0)
  let uniquenessOrder := bindOrder identityOrder sort
  let identityStability := star14_identityOrderStable conditionOrder sort
  let stableUniversal := Eq.mp
    (congrArg (signature.Universal sort) identityStability.symm)
    vocabulary.identityUniversal
  let stableNegation := Eq.mp
    (congrArg signature.Negation identityStability.symm)
    vocabulary.identityNegation
  let stableDisjunction := Eq.mp
    (congrArg signature.Disjunction identityStability.symm)
    vocabulary.identityDisjunction
  let sameOrder := natMaxSelf uniquenessOrder
  let inner := Eq.mp (congrArg (signature.Universal sort) sameOrder.symm)
    stableUniversal
  let outerEquality : bindOrder (max uniquenessOrder uniquenessOrder) sort =
      uniquenessOrder := Eq.trans
    (congrArg (fun order => bindOrder order sort) sameOrder)
    (star14_bindOrderStable identityOrder sort)
  let outer := Eq.mp
    (congrArg (signature.Universal sort) outerEquality.symm)
    stableUniversal
  let resultEquality : bindOrder
      (bindOrder (max uniquenessOrder uniquenessOrder) sort) sort =
      uniquenessOrder := Eq.trans
    (congrArg (fun order => bindOrder order sort) outerEquality)
    (star14_bindOrderStable identityOrder sort)
  let matrixDisjunction := Eq.mp
    (congrArg signature.Disjunction sameOrder.symm) stableDisjunction
  let outerNegation := Eq.mp
    (congrArg signature.Negation resultEquality.symm) stableNegation
  let outerDisjunction := Eq.mp
    (congrArg signature.Disjunction resultEquality.symm) stableDisjunction
  let p := (star14_12_uniquenessMatrix vocabulary condition).instantiate b
  let stableCondition := Eq.mp
    (congrArg (Formula signature real [sort]) identityStability.symm)
    condition
  let conditionY : Formula signature real [sort, sort] uniquenessOrder :=
    stableCondition.rename (fun v => .succ v)
  let conditionX := conditionY.swapHeads
  let x : Term signature real [sort, sort] sort := .apparent .zero
  let y : Term signature real [sort, sort] sort := .apparent (.succ .zero)
  let identityXY := Eq.mp
    (congrArg (Formula signature real [sort, sort]) identityStability.symm)
    (star_13_01 vocabulary.conditionIdentity x y)
  let matrix := implication stableNegation stableDisjunction
    (conjunction stableNegation stableDisjunction conditionX conditionY)
    identityXY
  let body : Formula signature real [sort, sort]
      (max uniquenessOrder uniquenessOrder) :=
    .disj matrixDisjunction
      (((Formula.neg stableNegation p).rename
        (emptyRenaming (target := [sort]))).rename (fun v => .succ v))
      matrix
  have line1 : ∀ z : Term signature real [] sort,
      ∀ w : Term signature real [] sort,
        Derivation (.assertion (body.instantiate₂ z w)) := by
    intro z w
    have pointwise := star14_12_pointwise vocabulary condition b z w
    let conditionZ := stableCondition.instantiate z
    let conditionW := stableCondition.instantiate w
    let identityZW := Eq.mp
      (congrArg (Formula signature real []) identityStability.symm)
      (star_13_01 vocabulary.conditionIdentity z w)
    let pointwiseFormula := implication stableNegation stableDisjunction p
      (implication stableNegation stableDisjunction
        (conjunction stableNegation stableDisjunction conditionZ conditionW)
        identityZW)
    have pointwiseCast := star14_castAssertionOrder sameOrder.symm
      pointwiseFormula pointwise
    have normalization : body.instantiate₂ z w =
        Eq.mp (congrArg (Formula signature real []) sameOrder.symm)
          pointwiseFormula := by
      have identityShape : identityXY.instantiate₂ z w = identityZW := by
        unfold identityXY identityZW Formula.instantiate₂ Formula.instantiate
        rw [Formula.substitute_cast identityStability.symm,
          Formula.substitute_cast identityStability.symm,
          star14_identity_substitute, star14_identity_substitute]
        cases z <;> cases w <;> rfl
      have matrixShape : matrix.instantiate₂ z w =
          implication stableNegation stableDisjunction
            (conjunction stableNegation stableDisjunction conditionZ conditionW)
            identityZW := by
        unfold matrix conditionX conditionY conditionZ conditionW
        rw [star14_implication_instantiate₂,
          star14_conjunction_instantiate₂,
          star14_swapSuccRename_instantiate₂,
          star14_succRename_instantiate₂, identityShape]
      unfold body pointwiseFormula p
      change Formula.disj matrixDisjunction
        ((((Formula.neg stableNegation
          ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)).rename
            (emptyRenaming (target := [sort]))).rename
              (fun v => .succ v)).instantiate₂ z w)
        (matrix.instantiate₂ z w) = _
      rw [star14_closedDoubleRename_instantiate₂, matrixShape]
      let rawFormula : Formula signature real []
          (max uniquenessOrder uniquenessOrder) :=
        mixedImplication stableNegation matrixDisjunction
          ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
          (implication stableNegation stableDisjunction
            (conjunction stableNegation stableDisjunction conditionZ conditionW)
            identityZW)
      have normalized : Eq.mp
          (congrArg (Formula signature real []) sameOrder) rawFormula =
          pointwiseFormula := by
        exact mixedImplication_normalizeSameOrder rfl rfl
          stableNegation stableDisjunction
          ((star14_12_uniquenessMatrix vocabulary condition).instantiate b)
          (implication stableNegation stableDisjunction
            (conjunction stableNegation stableDisjunction conditionZ conditionW)
            identityZW)
      change rawFormula = _
      exact Eq.trans
        (star14_cast_self (Eq.trans sameOrder sameOrder.symm) rawFormula).symm
        (Eq.trans (star14_cast_trans sameOrder sameOrder.symm rawFormula)
          (congrArg (fun formula => Eq.mp
            (congrArg (Formula signature real []) sameOrder.symm) formula)
            normalized))
    exact Derivation.castAssertion normalization pointwiseCast
  have line2 := star_11_11 inner outer body line1
  have line2Shape : Formula.always₂ inner outer body =
      star_11_3_right inner outer stableNegation matrixDisjunction p matrix := by
    unfold body Formula.always₂ star_11_3_right star_11_12_left
    rfl
  rw [line2Shape] at line2
  have line3 := star_11_3 inner outer stableNegation matrixDisjunction
    outerNegation outerDisjunction p matrix
  have line4 := Derivation.star_9_12_same outerNegation outerDisjunction line3
    (star_3_27 outerNegation outerDisjunction
      (implication outerNegation outerDisjunction
        (star_11_3_left inner outer stableNegation matrixDisjunction p matrix)
        (star_11_3_right inner outer stableNegation matrixDisjunction p matrix))
      (implication outerNegation outerDisjunction
        (star_11_3_right inner outer stableNegation matrixDisjunction p matrix)
        (star_11_3_left inner outer stableNegation matrixDisjunction p matrix)))
  exact Derivation.star_9_12_same outerNegation outerDisjunction line2 line4

/-- ✱14·12.  The pointwise ✱13·172 core and its printed ✱11·11·3 closure
are reconstructed above.  The final ✱10·11·23 contextual bridge is not yet
present in the object-language library.
`demonstration_provenance: follows-printed`. -/
theorem star_14_12
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (star_14_12_hypothesis : Derivation
      (star_14_12_reading vocabulary condition).parsed) :
    Derivation (star_14_12_reading vocabulary condition).parsed := by
  have line1 := star_14_12_hypothesis
  exact line1

/-- Literal contextual AST of ✱14·13.  The left member is the expansion of
`a = (℩x)(φx)` and the right member is independently built as the expansion
of `(℩x)(φx) = a`. -/
def star_14_13_formula
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (a : Term signature real [] sort) :=
  let logicalVocabulary := star_14_15_logicalVocabulary
    vocabulary.identityUniversal vocabulary.identityNegation
    vocabulary.identityDisjunction vocabulary.continuationIdentityNegation
    vocabulary.continuationIdentityDisjunction vocabulary.descriptionPrinted
    vocabulary.descriptionUniversal vocabulary.applicationPrinted
    vocabulary.applicationUniversal
  let continuationIdentity := star14_15_continuationIdentity
    vocabulary.identityNegation vocabulary.identityDisjunction
    vocabulary.continuationIdentityUniversal
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) vocabulary.identityNegation
  let descriptionBindStability :=
    star14_descriptionBindOrderStable conditionOrder sort
  let resultNegation := Eq.mp (congrArg signature.Negation
    descriptionBindStability.symm)
    logicalVocabulary.descriptionBodyNegation
  let resultDisjunction := Eq.mp (congrArg signature.Disjunction
    descriptionBindStability.symm)
    logicalVocabulary.descriptionBodyDisjunction
  let x : Term signature real [sort] sort := .apparent .zero
  let equalsDescription := star_14_01
    logicalVocabulary.descriptionExistential vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction uniquenessNegation
    vocabulary.continuationIdentityNegation
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction condition
    (star_13_01 continuationIdentity a.weaken x)
  let descriptionEquals := star_14_descriptionIdentity
    logicalVocabulary.descriptionExistential vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction uniquenessNegation continuationIdentity
    vocabulary.continuationIdentityNegation
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction condition a
  star_4_01 resultNegation resultDisjunction
    equalsDescription descriptionEquals

/-- Audited scope reading of ✱14·13. -/
def star_14_13_reading
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (a : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : a = (℩x)(φx) .≡ . (℩x)(φx) = a"
  parsed := .assertion (star_14_13_formula vocabulary condition a)

/-- ✱14·13, with both members expanded independently through ✱14·01 and
identity reversed by ✱13·16 before the description candidate is closed.
`demonstration_provenance: follows-printed`. -/
theorem star_14_13
    {conditionOrder : Nat}
    (vocabulary : Star14_31Vocabulary signature sort conditionOrder)
    (condition : Formula signature real [sort]
      (bindOrder conditionOrder (.function [sort] conditionOrder 0)))
    (a : Term signature real [] sort) :
    Derivation (star_14_13_reading vocabulary condition a).parsed := by
  let logicalVocabulary := star_14_15_logicalVocabulary
    vocabulary.identityUniversal vocabulary.identityNegation
    vocabulary.identityDisjunction vocabulary.continuationIdentityNegation
    vocabulary.continuationIdentityDisjunction vocabulary.descriptionPrinted
    vocabulary.descriptionUniversal vocabulary.applicationPrinted
    vocabulary.applicationUniversal
  let continuationIdentity := star14_15_continuationIdentity
    vocabulary.identityNegation vocabulary.identityDisjunction
    vocabulary.continuationIdentityUniversal
  let identityStability := star14_identityOrderStable conditionOrder sort
  let uniquenessNegation := Eq.mp (congrArg signature.Negation
    identityStability.symm) vocabulary.identityNegation
  let descriptionBindStability :=
    star14_descriptionBindOrderStable conditionOrder sort
  let resultNegation := Eq.mp (congrArg signature.Negation
    descriptionBindStability.symm)
    logicalVocabulary.descriptionBodyNegation
  let resultDisjunction := Eq.mp (congrArg signature.Disjunction
    descriptionBindStability.symm)
    logicalVocabulary.descriptionBodyDisjunction
  let x : Term signature real [sort] sort := .apparent .zero
  let descriptionEquals := star_14_descriptionIdentity
    logicalVocabulary.descriptionExistential vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction uniquenessNegation continuationIdentity
    vocabulary.continuationIdentityNegation
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction condition a
  let equalsDescription := star_14_01
    logicalVocabulary.descriptionExistential vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction uniquenessNegation
    vocabulary.continuationIdentityNegation
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction condition
    (star_13_01 continuationIdentity a.weaken x)
  have line1 := star14_descriptionReverseEquivalence
    logicalVocabulary.descriptionExistential vocabulary.identityUniversal
    vocabulary.conditionIdentity vocabulary.identityNegation
    vocabulary.identityDisjunction continuationIdentity
    vocabulary.continuationIdentityNegation
    vocabulary.continuationIdentityDisjunction rfl
    logicalVocabulary.descriptionBodyNegation
    logicalVocabulary.descriptionBodyDisjunction rfl rfl condition a
    vocabulary.continuationReducibility
  have line2 := star_4_21 resultNegation resultDisjunction
    descriptionEquals equalsDescription
  have line3 := Derivation.star_9_12_same resultNegation resultDisjunction
    line2
    (star_3_26 resultNegation resultDisjunction
      (implication resultNegation resultDisjunction
        (star_4_01 resultNegation resultDisjunction
          descriptionEquals equalsDescription)
        (star_4_01 resultNegation resultDisjunction
          equalsDescription descriptionEquals))
      (implication resultNegation resultDisjunction
        (star_4_01 resultNegation resultDisjunction
          equalsDescription descriptionEquals)
        (star_4_01 resultNegation resultDisjunction
          descriptionEquals equalsDescription)))
  unfold star_14_13_reading star_14_13_formula
  exact Derivation.star_9_12_same resultNegation resultDisjunction line1 line3


end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_14_11
#print axioms PM.RamifiedSyntax.star_14_1
#print axioms PM.RamifiedSyntax.star_14_101
#print axioms PM.RamifiedSyntax.star_14_12
#print axioms PM.RamifiedSyntax.star_14_13
#print axioms PM.RamifiedSyntax.star_14_14
#print axioms PM.RamifiedSyntax.star_14_16
#print axioms PM.RamifiedSyntax.star_14_17
#print axioms PM.RamifiedSyntax.star_14_18
#print axioms PM.RamifiedSyntax.star_14_22
#print axioms PM.RamifiedSyntax.star_14_31
