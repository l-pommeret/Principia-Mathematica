import Principia.FirstEdition.Volume1.Part1.SectionA.Star4Q240

namespace PM.FirstEdition.Volume1.Star4

open PM
open PM.Elementary

/-- PM I (1910), p. 124, ✱4·41. -/
theorem star_4_41 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∧ₚ r)) ≡ₚ ((p ∨ₚ q) ∧ₚ (p ∨ₚ r))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ A : PM.Elementary Γ, ⊢ₚ (A ⊃ₚ (A ∧ₚ A)) := by
    intro A
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 A A)
      (PM.FirstEdition.Volume1.Star2.star_2_43 A (A ∧ₚ A))
  have join : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (A ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ (B ∧ₚ C))) := by
    intro A B C hAB hAC
    have pair := infer hAC (infer hAB
      (PM.FirstEdition.Volume1.Star3.star_3_2 (A ⊃ₚ B) (A ⊃ₚ C)))
    exact comp (duplicate A) (infer pair
      (PM.FirstEdition.Volume1.Star3.star_3_47 A A B C))
  let A := (p ∨ₚ q) ∧ₚ (p ∨ₚ r)
  have forwardQ := infer (PM.FirstEdition.Volume1.Star3.star_3_26 q r)
    (PM.Derivation.star_1_6 p (q ∧ₚ r) q)
  have forwardR := infer (PM.FirstEdition.Volume1.Star3.star_3_27 q r)
    (PM.Derivation.star_1_6 p (q ∧ₚ r) r)
  have forward : ⊢ₚ ((p ∨ₚ (q ∧ₚ r)) ⊃ₚ ((p ∨ₚ q) ∧ₚ (p ∨ₚ r))) :=
    join forwardQ forwardR
  have toQ := comp (PM.FirstEdition.Volume1.Star3.star_3_26 (p ∨ₚ q) (p ∨ₚ r))
    (PM.FirstEdition.Volume1.Star2.star_2_53 p q)
  have toR := comp (PM.FirstEdition.Volume1.Star3.star_3_27 (p ∨ₚ q) (p ∨ₚ r))
    (PM.FirstEdition.Volume1.Star2.star_2_53 p r)
  have underNot : ⊢ₚ (A ⊃ₚ ((∼ₚ p) ⊃ₚ (q ∧ₚ r))) :=
    comp (join toQ toR) (PM.FirstEdition.Volume1.Star3.star_3_43 (∼ₚ p) q r)
  have backward : ⊢ₚ (A ⊃ₚ (p ∨ₚ (q ∧ₚ r))) :=
    comp underNot (PM.FirstEdition.Volume1.Star2.star_2_54 p (q ∧ₚ r))
  exact infer backward (infer forward
    (PM.FirstEdition.Volume1.Star3.star_3_2
      ((p ∨ₚ (q ∧ₚ r)) ⊃ₚ A) (A ⊃ₚ (p ∨ₚ (q ∧ₚ r)))))

/-- PM I (1910), p. 126, ✱4·61. -/
theorem star_4_61 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ⊃ₚ q)) ≡ₚ (p ∧ₚ (∼ₚ q))) := by
  have inner : ⊢ₚ ((∼ₚ p ∨ₚ q) ≡ₚ (∼ₚ p ∨ₚ ∼ₚ (∼ₚ q))) := by
    have pair := PM.Derivation.detach (star_4_13 q)
      (PM.Derivation.detach (star_4_2 (∼ₚ p))
        (PM.FirstEdition.Volume1.Star3.star_3_2
          ((∼ₚ p) ≡ₚ (∼ₚ p)) (q ≡ₚ ∼ₚ (∼ₚ q))))
    exact PM.Derivation.detach pair
      (star_4_39 (∼ₚ p) q (∼ₚ p) (∼ₚ (∼ₚ q)))
  have forward := PM.Derivation.detach
    (star_4_11 (∼ₚ p ∨ₚ q) (∼ₚ p ∨ₚ ∼ₚ (∼ₚ q)))
    (PM.FirstEdition.Volume1.Star3.star_3_26 _ _)
  exact PM.Derivation.detach inner forward

end PM.FirstEdition.Volume1.Star4
