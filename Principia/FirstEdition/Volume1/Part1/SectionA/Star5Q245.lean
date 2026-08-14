import Principia.FirstEdition.Volume1.Part1.SectionA.Star4Q244
import Principia.FirstEdition.Volume1.Part1.SectionA.Star5Kernel

namespace PM.FirstEdition.Volume1.Star5

open PM
open PM.Elementary

/-- Audited scope reading of ✱5·22. -/
def star_5_22_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼(p ≡ q) . ≡ : p . ∼q . ∨ . q . ∼p"
  parsed := ((∼ₚ (p ≡ₚ q)) ≡ₚ ((p ∧ₚ ∼ₚ q) ∨ₚ (q ∧ₚ ∼ₚ p)))
  scopeReading := "The principal equivalence relates ∼(p ≡ q) to the disjunction (p ∧ ∼q) ∨ (q ∧ ∼p)."

/-- PM I (1910), p. 130, ✱5·22. -/
theorem star_5_22 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ≡ₚ q)) ≡ₚ ((p ∧ₚ ∼ₚ q) ∨ₚ (q ∧ₚ ∼ₚ p))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have pair : ⊢ₚ (((∼ₚ (p ⊃ₚ q)) ≡ₚ (p ∧ₚ ∼ₚ q)) ∧ₚ
      ((∼ₚ (q ⊃ₚ p)) ≡ₚ (q ∧ₚ ∼ₚ p))) :=
    infer (PM.FirstEdition.Volume1.Star4.star_4_61 q p)
      (infer (PM.FirstEdition.Volume1.Star4.star_4_61 p q)
        (PM.FirstEdition.Volume1.Star3.star_3_2 _ _))
  have distributed : ⊢ₚ (((∼ₚ (p ⊃ₚ q)) ∨ₚ (∼ₚ (q ⊃ₚ p))) ≡ₚ
      ((p ∧ₚ ∼ₚ q) ∨ₚ (q ∧ₚ ∼ₚ p))) :=
    infer pair (PM.FirstEdition.Volume1.Star4.star_4_39
      (∼ₚ (p ⊃ₚ q)) (∼ₚ (q ⊃ₚ p))
      (p ∧ₚ ∼ₚ q) (q ∧ₚ ∼ₚ p))
  have deMorgan := PM.FirstEdition.Volume1.Star4.star_4_51
    (p ⊃ₚ q) (q ⊃ₚ p)
  have both := infer distributed (infer deMorgan
    (PM.FirstEdition.Volume1.Star3.star_3_2 _ _))
  exact infer both (PM.FirstEdition.Volume1.Star4.star_4_22
    (∼ₚ (p ≡ₚ q))
    ((∼ₚ (p ⊃ₚ q)) ∨ₚ (∼ₚ (q ⊃ₚ p)))
    ((p ∧ₚ ∼ₚ q) ∨ₚ (q ∧ₚ ∼ₚ p)))

end PM.FirstEdition.Volume1.Star5
