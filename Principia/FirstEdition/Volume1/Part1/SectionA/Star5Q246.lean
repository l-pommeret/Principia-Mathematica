import Principia.FirstEdition.Volume1.Part1.SectionA.Star5Q245

namespace PM.FirstEdition.Volume1.Star5
open PM PM.Elementary

private theorem inferQ246 {Γ} {A B : PM.Elementary Γ} (hA : ⊢ₚ A) (hAB : ⊢ₚ (A ⊃ₚ B)) : ⊢ₚ B := by
  match Γ, A, B, hA, hAB with
  | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
  | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB

private theorem joinQ246 {Γ} {A B : PM.Elementary Γ} (hA : ⊢ₚ A) (hB : ⊢ₚ B) : ⊢ₚ (A ∧ₚ B) :=
  inferQ246 hB (inferQ246 hA (PM.FirstEdition.Volume1.Star3.star_3_2 A B))

private theorem transQ246 {Γ} {A B C : PM.Elementary Γ} (hAB : ⊢ₚ (A ≡ₚ B)) (hBC : ⊢ₚ (B ≡ₚ C)) : ⊢ₚ (A ≡ₚ C) :=
  inferQ246 (joinQ246 hAB hBC) (PM.FirstEdition.Volume1.Star4.star_4_22 A B C)

private theorem conjCommQ246 {Γ} (A B : PM.Elementary Γ) : ⊢ₚ ((A ∧ₚ B) ≡ₚ (B ∧ₚ A)) :=
  joinQ246 (PM.FirstEdition.Volume1.Star3.star_3_22 A B)
    (PM.FirstEdition.Volume1.Star3.star_3_22 B A)

private theorem equivForwardQ246 {Γ} {A B : PM.Elementary Γ} (h : ⊢ₚ (A ≡ₚ B)) : ⊢ₚ (A ⊃ₚ B) :=
  inferQ246 h (PM.FirstEdition.Volume1.Star3.star_3_26 (A ⊃ₚ B) (B ⊃ₚ A))

/-- PM I (1910), p. 130, ✱5·18. [✱5·15·16 . ✱5·17] -/
theorem star_5_18 {Γ} (p q : PM.Elementary Γ) : ⊢ₚ ((p ≡ₚ q) ≡ₚ ∼ₚ (p ≡ₚ ∼ₚ q)) := by
  let A := p ≡ₚ q; let B := p ≡ₚ ∼ₚ q
  have h := joinQ246 (star_5_15 p q) (star_5_16 p q)
  exact inferQ246 h (equivForwardQ246 (star_5_17 A B))

/-- Audited scope reading of ✱5·23. -/
def star_5_23_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ≡ q . ≡ : p . q . ∨ . ∼p . ∼q"
  parsed := ((p ≡ₚ q) ≡ₚ ((p ∧ₚ q) ∨ₚ (∼ₚ p ∧ₚ ∼ₚ q)))
  scopeReading := "The principal equivalence relates p ≡ q to (p ∧ q) ∨ (∼p ∧ ∼q)."

/-- PM I (1910), p. 130, ✱5·23. -/
theorem star_5_23 {Γ} (p q : PM.Elementary Γ) : ⊢ₚ ((p ≡ₚ q) ≡ₚ ((p ∧ₚ q) ∨ₚ (∼ₚ p ∧ₚ ∼ₚ q))) := by
  have dn := inferQ246 (PM.FirstEdition.Volume1.Star4.star_4_13 q)
    (equivForwardQ246 (PM.FirstEdition.Volume1.Star4.star_4_21 q (∼ₚ ∼ₚ q)))
  have left := transQ246 (conjCommQ246 p (∼ₚ ∼ₚ q))
    (transQ246 (inferQ246 dn (PM.FirstEdition.Volume1.Star4.star_4_36 (∼ₚ ∼ₚ q) q p)) (conjCommQ246 q p))
  have right := conjCommQ246 (∼ₚ q) (∼ₚ p)
  have mapped := inferQ246 (joinQ246 left right) (PM.FirstEdition.Volume1.Star4.star_4_39 _ _ _ _)
  exact transQ246 (star_5_18 p q) (transQ246 (star_5_22 p (∼ₚ q)) mapped)

/-- Audited scope reading of ✱5·24. -/
def star_5_24_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼(p . q . ∨ . ∼p . ∼q) . ≡ : p . ∼q . ∨ . q . ∼p"
  parsed := (∼ₚ ((p ∧ₚ q) ∨ₚ (∼ₚ p ∧ₚ ∼ₚ q)) ≡ₚ ((p ∧ₚ ∼ₚ q) ∨ₚ (q ∧ₚ ∼ₚ p)))
  scopeReading := "The principal equivalence relates the negation of (p ∧ q) ∨ (∼p ∧ ∼q) to (p ∧ ∼q) ∨ (q ∧ ∼p)."

/-- PM I (1910), p. 130, ✱5·24. -/
theorem star_5_24 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ ((p ∧ₚ q) ∨ₚ (∼ₚ p ∧ₚ ∼ₚ q)) ≡ₚ ((p ∧ₚ ∼ₚ q) ∨ₚ (q ∧ₚ ∼ₚ p))) := by
  have neg := inferQ246 (star_5_23 p q) (equivForwardQ246
    (PM.FirstEdition.Volume1.Star4.star_4_11 (p ≡ₚ q) ((p ∧ₚ q) ∨ₚ (∼ₚ p ∧ₚ ∼ₚ q))))
  have symm := inferQ246 neg (equivForwardQ246 (PM.FirstEdition.Volume1.Star4.star_4_21 _ _))
  exact transQ246 symm (star_5_22 p q)

end PM.FirstEdition.Volume1.Star5
