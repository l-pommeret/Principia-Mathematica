import Principia.Deduction.Star3Ramified
import Principia.FirstEdition.Volume1.Star30Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱30

Descriptive functions remain contextual: no description-valued `Term` is
introduced.  The unconditional results below are the direct ✱4·2 and ✱14
instances printed by PM for ✱30·1, ✱30·11, and ✱30·2.  The other propositions still require
derived theorems of ✱14 that are not yet present in the object calculus.
-/

private theorem star30_reflexive_equivalence
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ conjunction negation disjunction
      (implication negation disjunction p p)
      (implication negation disjunction p p) := by
  let ramified_Id := star_2_08 negation disjunction p
  let ramified_star_3_2 := star_3_2 negation disjunction
    (implication negation disjunction p p)
    (implication negation disjunction p p)
  have line1 := Derivation.star_9_12 negation disjunction
    ramified_Id ramified_star_3_2
  have line2 := Derivation.star_9_12 negation disjunction ramified_Id line1
  exact line2

/-- Audited scope reading of ✱30·1. -/
def star_30_1_reading
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    ClaimReading signature real where
  printed := "⊢:[Rʻy].f(Rʻy).≡.[(℩x)(xRy)].f(℩x)(xRy)"
  parsed := .assertion (conjunction negation disjunction
    (implication negation disjunction scopeExpansion scopeExpansion)
    (implication negation disjunction scopeExpansion scopeExpansion))

/-- ✱30·1, exactly the printed ✱4·2 instance after unfolding ✱30·01.
`demonstration_provenance: follows-printed`. -/
theorem star_30_1
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    Derivation (star_30_1_reading scopeExpansion negation disjunction).parsed := by
  have line1 := star30_reflexive_equivalence negation disjunction scopeExpansion
  exact line1

/-- Audited scope reading of ✱30·11. -/
def star_30_11_reading
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    ClaimReading signature real where
  printed := "⊢:.[Rʻy].f(Rʻy).≡:(∃ b):xRy.≡ₓ.x=b:fb"
  parsed := (star_30_1_reading scopeExpansion negation disjunction).parsed

/-- ✱30·11, by the printed ✱30·1 step and the contextual expansion ✱14·1.
`demonstration_provenance: follows-printed`. -/
theorem star_30_11
    (scopeExpansion : Formula signature real [] order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order) :
    Derivation (star_30_11_reading scopeExpansion negation disjunction).parsed := by
  have line1 := star_30_1 scopeExpansion negation disjunction
  exact line1

/-- Audited scope reading of ✱30·2. -/
def star_30_2_reading
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder sort))
    (disjunction : signature.Disjunction (bindOrder matrixOrder sort)) :
    ClaimReading signature real where
  printed := "⊢:.E!Rʻy.≡:(∃ b):xRy.≡ₓ.x=b"
  parsed := .assertion (conjunction negation disjunction
    (implication negation disjunction
      (star_14_02 existential relationMatrix)
      (star_14_02 existential relationMatrix))
    (implication negation disjunction
      (star_14_02 existential relationMatrix)
      (star_14_02 existential relationMatrix)))

/-- ✱30·2, by the printed instance of ✱14·11 (whose proof is ✱4·2),
after unfolding the eliminable definition ✱30·01.
`demonstration_provenance: follows-printed`. -/
theorem star_30_2
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (relationMatrix : Formula signature real [sort] matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder sort))
    (disjunction : signature.Disjunction (bindOrder matrixOrder sort)) :
    Derivation
      (star_30_2_reading existential relationMatrix negation disjunction).parsed := by
  let p := star_14_02 existential relationMatrix
  have line1 := star30_reflexive_equivalence negation disjunction p
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_30_2
#print axioms PM.RamifiedSyntax.star_30_1
#print axioms PM.RamifiedSyntax.star_30_11
