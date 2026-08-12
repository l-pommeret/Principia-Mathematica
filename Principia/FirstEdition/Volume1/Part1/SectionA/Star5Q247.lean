import Principia.FirstEdition.Volume1.Part1.SectionA.Star5Kernel

namespace PM.FirstEdition.Volume1.Star5

open PM
open PM.Elementary

/-- ✱5·32.  `⊢ :. p . ⊃ . q ≡ r : ≡ : p . q . ≡ . p . r`.

This proposition is constantly required in subsequent proofs. -/
theorem star_5_32 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ≡ₚ r)) ≡ₚ ((p ∧ₚ q) ≡ₚ (p ∧ₚ r))) := by
  -- [✱4·76.✱3·3·31.✱5·3]
  have eqFwd : ∀ {a b : PM.Elementary Γ}, (⊢ₚ (a ≡ₚ b)) → (⊢ₚ (a ⊃ₚ b)) :=
    fun {a b} h => PM.Derivation.detach h (PM.FirstEdition.Volume1.Star3.star_3_26 (a ⊃ₚ b) (b ⊃ₚ a))
  have eqBwd : ∀ {a b : PM.Elementary Γ}, (⊢ₚ (a ≡ₚ b)) → (⊢ₚ (b ⊃ₚ a)) :=
    fun {a b} h => PM.Derivation.detach h (PM.FirstEdition.Volume1.Star3.star_3_27 (a ⊃ₚ b) (b ⊃ₚ a))
  have prodI : ∀ {a b : PM.Elementary Γ}, (⊢ₚ a) → (⊢ₚ b) → (⊢ₚ (a ∧ₚ b)) :=
    fun {a b} ha hb => PM.Derivation.detach ha (eqFwd (PM.Derivation.detach hb (PM.FirstEdition.Volume1.Star4.star_4_73 a b)))
  have addHyp : ∀ a b : PM.Elementary Γ, (⊢ₚ (a ⊃ₚ (b ⊃ₚ a))) :=
    fun a b => PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_26 a b) (PM.FirstEdition.Volume1.Star3.star_3_3 a b a)
  have ident : ∀ a : PM.Elementary Γ, (⊢ₚ (a ⊃ₚ a)) := fun a =>
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_26 a (a ⊃ₚ (a ⊃ₚ a)))
      (eqBwd (PM.Derivation.detach (PM.Derivation.detach (addHyp a a) (PM.FirstEdition.Volume1.Star4.star_4_73 a (a ⊃ₚ (a ⊃ₚ a))))
        (PM.FirstEdition.Volume1.Star4.star_4_84 a (a ∧ₚ (a ⊃ₚ (a ⊃ₚ a))) a)))
  have compR : ∀ {a b c : PM.Elementary Γ},
      (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) :=
    fun {a b c} h₁ h₂ => PM.Derivation.detach (prodI h₁ h₂) (PM.FirstEdition.Volume1.Star3.star_3_43 a b c)
  have syl : ∀ {a b c : PM.Elementary Γ},
      (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (b ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ c)) :=
    fun {a b c} h₁ h₂ =>
      PM.Derivation.detach (PM.Derivation.detach (PM.Derivation.detach h₂ (addHyp (b ⊃ₚ c) a)) (PM.FirstEdition.Volume1.Star3.star_3_31 a b c))
        (eqBwd (PM.Derivation.detach
          (prodI (PM.Derivation.detach (prodI (ident a) h₁) (PM.FirstEdition.Volume1.Star3.star_3_43 a a b))
            (PM.FirstEdition.Volume1.Star3.star_3_26 a b))
          (PM.FirstEdition.Volume1.Star4.star_4_84 a (a ∧ₚ b) c)))
  -- By ✱4·76, `p . ⊃ . q ≡ r : ⊃ : p ⊃ (q ⊃ r) . p ⊃ (r ⊃ q)`.
  have hsplit : ⊢ₚ ((p ⊃ₚ (q ≡ₚ r)) ⊃ₚ ((p ⊃ₚ (q ⊃ₚ r)) ∧ₚ (p ⊃ₚ (r ⊃ₚ q)))) :=
    eqBwd (PM.FirstEdition.Volume1.Star4.star_4_76 p (q ⊃ₚ r) (r ⊃ₚ q))
  -- By Imp (✱3·31) and ✱5·3, each half gives one half of `p . q . ≡ . p . r`.
  have hA : ⊢ₚ (((p ⊃ₚ (q ⊃ₚ r)) ∧ₚ (p ⊃ₚ (r ⊃ₚ q))) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (p ∧ₚ r))) :=
    syl (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ (q ⊃ₚ r)) (p ⊃ₚ (r ⊃ₚ q)))
      (syl (PM.FirstEdition.Volume1.Star3.star_3_31 p q r) (eqFwd (star_5_3 p q r)))
  have hB : ⊢ₚ (((p ⊃ₚ (q ⊃ₚ r)) ∧ₚ (p ⊃ₚ (r ⊃ₚ q))) ⊃ₚ ((p ∧ₚ r) ⊃ₚ (p ∧ₚ q))) :=
    syl (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ (q ⊃ₚ r)) (p ⊃ₚ (r ⊃ₚ q)))
      (syl (PM.FirstEdition.Volume1.Star3.star_3_31 p r q) (eqFwd (star_5_3 p r q)))
  have fwd : ⊢ₚ ((p ⊃ₚ (q ≡ₚ r)) ⊃ₚ ((p ∧ₚ q) ≡ₚ (p ∧ₚ r))) :=
    syl hsplit (compR hA hB)
  -- Conversely, by ✱5·3 and Exp (✱3·3).
  have hA' : ⊢ₚ (((p ∧ₚ q) ≡ₚ (p ∧ₚ r)) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r))) :=
    syl (PM.FirstEdition.Volume1.Star3.star_3_26 ((p ∧ₚ q) ⊃ₚ (p ∧ₚ r)) ((p ∧ₚ r) ⊃ₚ (p ∧ₚ q)))
      (syl (eqBwd (star_5_3 p q r)) (PM.FirstEdition.Volume1.Star3.star_3_3 p q r))
  have hB' : ⊢ₚ (((p ∧ₚ q) ≡ₚ (p ∧ₚ r)) ⊃ₚ (p ⊃ₚ (r ⊃ₚ q))) :=
    syl (PM.FirstEdition.Volume1.Star3.star_3_27 ((p ∧ₚ q) ⊃ₚ (p ∧ₚ r)) ((p ∧ₚ r) ⊃ₚ (p ∧ₚ q)))
      (syl (eqBwd (star_5_3 p r q)) (PM.FirstEdition.Volume1.Star3.star_3_3 p r q))
  have bwd : ⊢ₚ (((p ∧ₚ q) ≡ₚ (p ∧ₚ r)) ⊃ₚ (p ⊃ₚ (q ≡ₚ r))) :=
    syl (compR hA' hB') (eqFwd (PM.FirstEdition.Volume1.Star4.star_4_76 p (q ⊃ₚ r) (r ⊃ₚ q)))
  exact prodI fwd bwd

-- This proposition is constantly required in subsequent proofs.

/-- ✱5·33.  `⊢ :. p . q ⊃ r . ≡ : p : p . q . ⊃ . r`.

(The colon without an explicit connective after the second `p` is PM's product
dot at the stronger scope: the right-hand side is `p . ((p . q) ⊃ r)`.) -/
theorem star_5_33 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ (q ⊃ₚ r)) ≡ₚ (p ∧ₚ ((p ∧ₚ q) ⊃ₚ r))) := by
  -- [✱4·73·84.✱5·32]
  have eqFwd : ∀ {a b : PM.Elementary Γ}, (⊢ₚ (a ≡ₚ b)) → (⊢ₚ (a ⊃ₚ b)) :=
    fun {a b} h => PM.Derivation.detach h (PM.FirstEdition.Volume1.Star3.star_3_26 (a ⊃ₚ b) (b ⊃ₚ a))
  have eqBwd : ∀ {a b : PM.Elementary Γ}, (⊢ₚ (a ≡ₚ b)) → (⊢ₚ (b ⊃ₚ a)) :=
    fun {a b} h => PM.Derivation.detach h (PM.FirstEdition.Volume1.Star3.star_3_27 (a ⊃ₚ b) (b ⊃ₚ a))
  have prodI : ∀ {a b : PM.Elementary Γ}, (⊢ₚ a) → (⊢ₚ b) → (⊢ₚ (a ∧ₚ b)) :=
    fun {a b} ha hb => PM.Derivation.detach ha (eqFwd (PM.Derivation.detach hb (PM.FirstEdition.Volume1.Star4.star_4_73 a b)))
  have addHyp : ∀ a b : PM.Elementary Γ, (⊢ₚ (a ⊃ₚ (b ⊃ₚ a))) :=
    fun a b => PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_26 a b) (PM.FirstEdition.Volume1.Star3.star_3_3 a b a)
  have ident : ∀ a : PM.Elementary Γ, (⊢ₚ (a ⊃ₚ a)) := fun a =>
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_26 a (a ⊃ₚ (a ⊃ₚ a)))
      (eqBwd (PM.Derivation.detach (PM.Derivation.detach (addHyp a a) (PM.FirstEdition.Volume1.Star4.star_4_73 a (a ⊃ₚ (a ⊃ₚ a))))
        (PM.FirstEdition.Volume1.Star4.star_4_84 a (a ∧ₚ (a ⊃ₚ (a ⊃ₚ a))) a)))
  have compR : ∀ {a b c : PM.Elementary Γ},
      (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) :=
    fun {a b c} h₁ h₂ => PM.Derivation.detach (prodI h₁ h₂) (PM.FirstEdition.Volume1.Star3.star_3_43 a b c)
  have syl : ∀ {a b c : PM.Elementary Γ},
      (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (b ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ c)) :=
    fun {a b c} h₁ h₂ =>
      PM.Derivation.detach (PM.Derivation.detach (PM.Derivation.detach h₂ (addHyp (b ⊃ₚ c) a)) (PM.FirstEdition.Volume1.Star3.star_3_31 a b c))
        (eqBwd (PM.Derivation.detach
          (prodI (PM.Derivation.detach (prodI (ident a) h₁) (PM.FirstEdition.Volume1.Star3.star_3_43 a a b))
            (PM.FirstEdition.Volume1.Star3.star_3_26 a b))
          (PM.FirstEdition.Volume1.Star4.star_4_84 a (a ∧ₚ b) c)))
  -- By ✱4·73 (in the form given by Exp ✱3·3 and Simp), `p . ⊃ . q ≡ p . q`.
  have h₁ : ⊢ₚ (p ⊃ₚ (q ⊃ₚ (p ∧ₚ q))) :=
    PM.Derivation.detach (ident (p ∧ₚ q)) (PM.FirstEdition.Volume1.Star3.star_3_3 p q (p ∧ₚ q))
  have h₂ : ⊢ₚ (p ⊃ₚ ((p ∧ₚ q) ⊃ₚ q)) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_27 p q) (addHyp ((p ∧ₚ q) ⊃ₚ q) p)
  have hEq : ⊢ₚ (p ⊃ₚ (q ≡ₚ (p ∧ₚ q))) := compR h₁ h₂
  -- Whence by ✱4·84, `p . ⊃ : q ⊃ r . ≡ . p . q . ⊃ . r`.
  have hmain : ⊢ₚ (p ⊃ₚ ((q ⊃ₚ r) ≡ₚ ((p ∧ₚ q) ⊃ₚ r))) :=
    syl hEq (PM.FirstEdition.Volume1.Star4.star_4_84 q (p ∧ₚ q) r)
  -- Whence the result by ✱5·32.
  exact PM.Derivation.detach hmain (eqFwd (star_5_32 p (q ⊃ₚ r) ((p ∧ₚ q) ⊃ₚ r)))

end PM.FirstEdition.Volume1.Star5

