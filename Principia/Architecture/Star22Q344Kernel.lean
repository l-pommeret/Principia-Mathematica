import Principia.FirstEdition.Volume1.Part1.SectionA.Star3

namespace PM.Architecture.Star22Q344Kernel

/-- Audited scope reading of ✱22·44.  Here `p`, `q`, and `r` are the
membership propositions `x ε α`, `x ε β`, and `x ε γ` exposed by ✱22·01. -/
def star_22_44_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : α ⊂ β . β ⊂ γ .⊃ . α ⊂ γ"
  parsed := ((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r)
  scopeReading := "The two inclusions form the conjunctive antecedent; inclusion from α to γ is the consequent."

/-- ✱22·44, the instance of ✱3·33 cited through ✱10·3 by PM. -/
theorem star_22_44 { Γ : PM.RealContext } (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r)) :=
  PM.FirstEdition.Volume1.Star3.star_3_33 p q r

/-- Audited scope reading of ✱22·441.  `p` and `q` are the displayed
membership propositions, so α ⊂ β unfolds to `p ⊃ₚ q`. -/
def star_22_441_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : α ⊂ β . x ε α .⊃ . x ε β"
  parsed := ((p ⊃ₚ q) ∧ₚ p) ⊃ₚ q
  scopeReading := "The inclusion and membership assertion form the antecedent; membership in β is the consequent."

/-- ✱22·441, PM's `Imp` after unfolding ✱22·01. -/
theorem star_22_441 { Γ : PM.RealContext } (p q : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ p) ⊃ₚ q) := by
  have line1 : ⊢ₚ (((p ⊃ₚ q) ∧ₚ p) ⊃ₚ (p ∧ₚ (p ⊃ₚ q))) :=
    PM.FirstEdition.Volume1.Star3.star_3_22 (p ⊃ₚ q) p
  have line2 : ⊢ₚ ((p ∧ₚ (p ⊃ₚ q)) ⊃ₚ q) :=
    PM.FirstEdition.Volume1.Star3.star_3_35 p q
  exact PM.Derivation.detach line1
    (PM.Derivation.detach line2
      (PM.FirstEdition.Volume1.Star2.star_2_05
        ((p ⊃ₚ q) ∧ₚ p) (p ∧ₚ (p ⊃ₚ q)) q))

end PM.Architecture.Star22Q344Kernel
