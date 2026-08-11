import Principia.FirstEdition.Volume1.Part1.SectionA.Star5

/-!
# PM I, first edition, ✱5 — kernel candidates

This module contains only bodies that are ready for remote kernel checking.
The diplomatic source remains in `Star5.lean`.
-/

namespace PM.FirstEdition.Volume1.Star5

open PM
open PM.Elementary

/-- PM I (1910), p. 129, ✱5·13.  The scan cites ✱2·521.  The displayed
disjunction needs one unprinted use of ✱2·54; the two primitive inference
branches make the generic real-variable context explicit. -/
theorem star_5_13 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ∨ₚ (q ⊃ₚ p)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer
    (PM.FirstEdition.Volume1.Star2.star_2_521 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_54 (p ⊃ₚ q) (q ⊃ₚ p))

end PM.FirstEdition.Volume1.Star5
