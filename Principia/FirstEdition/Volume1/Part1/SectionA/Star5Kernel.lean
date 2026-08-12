import Principia.FirstEdition.Volume1.Part1.SectionA.Star5
import Principia.FirstEdition.Volume1.Part1.SectionA.Star4

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

/-- PM I (1910), p. 130, ✱5·25.  The printed pair ✱2·62·68 supplies the
two directions; ✱3·2 packages them according to the definitional reading of
equivalence. -/
theorem star_5_25 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ≡ₚ ((p ⊃ₚ q) ⊃ₚ q)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer
    (PM.FirstEdition.Volume1.Star2.star_2_68 p q)
    (infer
      (PM.FirstEdition.Volume1.Star2.star_2_62 p q)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ∨ₚ q) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q))
        (((p ⊃ₚ q) ⊃ₚ q) ⊃ₚ (p ∨ₚ q))))

/-- PM I (1910), p. 129, ✱5·1.  The two simplifications of `p ∧ q` are
curryfied separately, then lifted together; all detachment is explicit. -/
theorem star_5_1 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (p ≡ₚ q)) := by
  let h := p ∧ₚ q
  let forward := p ⊃ₚ q
  let backward := q ⊃ₚ p
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have hForwardBase : ⊢ₚ ((h ∧ₚ p) ⊃ₚ q) :=
    compose (PM.FirstEdition.Volume1.Star3.star_3_26 h p)
      (PM.FirstEdition.Volume1.Star3.star_3_27 p q)
  have hForward : ⊢ₚ (h ⊃ₚ forward) :=
    infer hForwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 h p q)
  have hBackwardBase : ⊢ₚ ((h ∧ₚ q) ⊃ₚ p) :=
    compose (PM.FirstEdition.Volume1.Star3.star_3_26 h q)
      (PM.FirstEdition.Volume1.Star3.star_3_26 p q)
  have hBackward : ⊢ₚ (h ⊃ₚ backward) :=
    infer hBackwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 h q p)
  have hPair : ⊢ₚ ((h ⊃ₚ forward) ∧ₚ (h ⊃ₚ backward)) :=
    infer hBackward
      (infer hForward
        (PM.FirstEdition.Volume1.Star3.star_3_2 (h ⊃ₚ forward) (h ⊃ₚ backward)))
  have hLift : ⊢ₚ ((h ∧ₚ h) ⊃ₚ (forward ∧ₚ backward)) :=
    infer hPair
      (PM.FirstEdition.Volume1.Star3.star_3_47 h h forward backward)
  have hDuplicate : ⊢ₚ (h ⊃ₚ (h ∧ₚ h)) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_2 h h)
      (PM.FirstEdition.Volume1.Star2.star_2_43 h (h ∧ₚ h))
  exact compose hDuplicate hLift

/-- PM I (1910), p. 130, ✱5·21.  Apply ✱5·1 to the two negations and take
the reverse component of the accepted transposition equivalence ✱4·11. -/
theorem star_5_21 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∧ₚ (∼ₚ q)) ⊃ₚ (p ≡ₚ q)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have backward : ⊢ₚ (((∼ₚ p) ≡ₚ (∼ₚ q)) ⊃ₚ (p ≡ₚ q)) :=
    infer (PM.FirstEdition.Volume1.Star4.star_4_11 p q)
      (PM.FirstEdition.Volume1.Star3.star_3_27
        ((p ≡ₚ q) ⊃ₚ ((∼ₚ p) ≡ₚ (∼ₚ q)))
        (((∼ₚ p) ≡ₚ (∼ₚ q)) ⊃ₚ (p ≡ₚ q)))
  exact infer (star_5_1 (∼ₚ p) (∼ₚ q))
    (infer backward
      (PM.FirstEdition.Volume1.Star2.star_2_05
        ((∼ₚ p) ∧ₚ (∼ₚ q)) ((∼ₚ p) ≡ₚ (∼ₚ q)) (p ≡ₚ q)))

/-- PM I (1910), p. 130, ✱5·41.  ✱2·77 and ✱2·86 are the two displayed
directions; ✱3·2 packages them as the defined equivalence. -/
theorem star_5_41 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ⊃ₚ r))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer
    (PM.FirstEdition.Volume1.Star2.star_2_77 p q r)
    (infer
      (PM.FirstEdition.Volume1.Star2.star_2_86 p q r)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        (((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r)))
        ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)))))

/-- PM I (1910), p. 130, ✱5·4.  ✱2·43 contracts the repeated antecedent,
while ✱2·02 supplies its converse instance. -/
theorem star_5_4 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (p ⊃ₚ q)) ≡ₚ (p ⊃ₚ q)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer
    (PM.FirstEdition.Volume1.Star2.star_2_02 p (p ⊃ₚ q))
    (infer
      (PM.FirstEdition.Volume1.Star2.star_2_43 p q)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ⊃ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ q))
        ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ (p ⊃ₚ q)))))

/-- PM I (1910), p. 130, ✱5·31.  The printed `Simp . Comp` abbreviations
are expanded through accepted simplification, conjunction lifting, and
curryfication theorems. -/
theorem star_5_31 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((r ∧ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ (q ∧ₚ r))) := by
  let h := r ∧ₚ (p ⊃ₚ q)
  let x := h ∧ₚ p
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ a : PM.Elementary Γ, ⊢ₚ (a ⊃ₚ (a ∧ₚ a)) := by
    intro a
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 a a)
      (PM.FirstEdition.Volume1.Star2.star_2_43 a (a ∧ₚ a))
  have join : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) →
      (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) := by
    intro a b c hab hac
    have pair : ⊢ₚ ((a ⊃ₚ b) ∧ₚ (a ⊃ₚ c)) :=
      infer hac (infer hab (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    have lifted : ⊢ₚ ((a ∧ₚ a) ⊃ₚ (b ∧ₚ c)) := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c)
    exact compose (duplicate a) lifted
  have hxH : ⊢ₚ (x ⊃ₚ h) := PM.FirstEdition.Volume1.Star3.star_3_26 h p
  have hxP : ⊢ₚ (x ⊃ₚ p) := PM.FirstEdition.Volume1.Star3.star_3_27 h p
  have hImp : ⊢ₚ (h ⊃ₚ (p ⊃ₚ q)) := PM.FirstEdition.Volume1.Star3.star_3_27 r (p ⊃ₚ q)
  have hxImp : ⊢ₚ (x ⊃ₚ (p ⊃ₚ q)) := compose hxH hImp
  have hxQ : ⊢ₚ (x ⊃ₚ q) := compose (join hxP hxImp) (PM.FirstEdition.Volume1.Star3.star_3_35 p q)
  have hxR : ⊢ₚ (x ⊃ₚ r) := compose hxH (PM.FirstEdition.Volume1.Star3.star_3_26 r (p ⊃ₚ q))
  exact infer (join hxQ hxR) (PM.FirstEdition.Volume1.Star3.star_3_3 h p (q ∧ₚ r))

/-- PM I (1910), p. 130, ✱5·35.  Under the two displayed implications, the
antecedent `p` yields both `q` and `r`; ✱5·1 then supplies their equivalence. -/
theorem star_5_35 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ⊃ₚ (p ⊃ₚ (q ≡ₚ r))) := by
  let h := (p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)
  let x := h ∧ₚ p
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ a : PM.Elementary Γ, ⊢ₚ (a ⊃ₚ (a ∧ₚ a)) := by
    intro a
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 a a) (PM.FirstEdition.Volume1.Star2.star_2_43 a (a ∧ₚ a))
  have join : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) := by
    intro a b c hab hac
    have pair : ⊢ₚ ((a ⊃ₚ b) ∧ₚ (a ⊃ₚ c)) := infer hac (infer hab (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    exact compose (duplicate a) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c))
  have hxH : ⊢ₚ (x ⊃ₚ h) := PM.FirstEdition.Volume1.Star3.star_3_26 h p
  have hxP : ⊢ₚ (x ⊃ₚ p) := PM.FirstEdition.Volume1.Star3.star_3_27 h p
  have hxQ : ⊢ₚ (x ⊃ₚ q) :=
    compose (join hxP (compose hxH (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (p ⊃ₚ r)))) (PM.FirstEdition.Volume1.Star3.star_3_35 p q)
  have hxR : ⊢ₚ (x ⊃ₚ r) :=
    compose (join hxP (compose hxH (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (p ⊃ₚ r)))) (PM.FirstEdition.Volume1.Star3.star_3_35 p r)
  exact infer (compose (join hxQ hxR) (star_5_1 q r)) (PM.FirstEdition.Volume1.Star3.star_3_3 h p (q ≡ₚ r))

/-- PM I (1910), p. 130, ✱5·5. -/
theorem star_5_5 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ ((p ⊃ₚ q) ≡ₚ q)) := by
  let a := p ⊃ₚ q
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have forward : ⊢ₚ (p ⊃ₚ (a ⊃ₚ q)) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_35 p q) (PM.FirstEdition.Volume1.Star3.star_3_3 p a q)
  have backward : ⊢ₚ (p ⊃ₚ (q ⊃ₚ a)) :=
    infer (PM.FirstEdition.Volume1.Star2.star_2_02 p q)
      (PM.FirstEdition.Volume1.Star2.star_2_02 p (q ⊃ₚ a))
  have pair := infer backward (infer forward
    (PM.FirstEdition.Volume1.Star3.star_3_2
      (p ⊃ₚ (a ⊃ₚ q)) (p ⊃ₚ (q ⊃ₚ a))))
  have lift := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 p p (a ⊃ₚ q) (q ⊃ₚ a))
  have dup := infer (PM.FirstEdition.Volume1.Star3.star_3_2 p p) (PM.FirstEdition.Volume1.Star2.star_2_43 p (p ∧ₚ p))
  exact compose dup lift

/-- PM I (1910), p. 130, ✱5·501. -/
theorem star_5_501 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (q ≡ₚ (p ≡ₚ q))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have forward : ⊢ₚ (p ⊃ₚ (q ⊃ₚ (p ≡ₚ q))) :=
    infer (star_5_1 p q) (PM.FirstEdition.Volume1.Star3.star_3_3 p q (p ≡ₚ q))
  have backwardBase : ⊢ₚ ((p ∧ₚ (p ≡ₚ q)) ⊃ₚ q) := by
    have hp : ⊢ₚ ((p ∧ₚ (p ≡ₚ q)) ⊃ₚ p) := PM.FirstEdition.Volume1.Star3.star_3_26 p (p ≡ₚ q)
    have he : ⊢ₚ ((p ∧ₚ (p ≡ₚ q)) ⊃ₚ (p ⊃ₚ q)) :=
      compose (PM.FirstEdition.Volume1.Star3.star_3_27 p (p ≡ₚ q)) (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p))
    have pair := infer he (infer hp
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ∧ₚ (p ≡ₚ q)) ⊃ₚ p)
        ((p ∧ₚ (p ≡ₚ q)) ⊃ₚ (p ⊃ₚ q))))
    have lift := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 (p ∧ₚ (p ≡ₚ q)) (p ∧ₚ (p ≡ₚ q)) p (p ⊃ₚ q))
    have dup := infer (PM.FirstEdition.Volume1.Star3.star_3_2 (p ∧ₚ (p ≡ₚ q)) (p ∧ₚ (p ≡ₚ q))) (PM.FirstEdition.Volume1.Star2.star_2_43 (p ∧ₚ (p ≡ₚ q)) ((p ∧ₚ (p ≡ₚ q)) ∧ₚ (p ∧ₚ (p ≡ₚ q))))
    exact compose (compose dup lift) (PM.FirstEdition.Volume1.Star3.star_3_35 p q)
  have backward := infer backwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 p (p ≡ₚ q) q)
  have pair := infer backward (infer forward
    (PM.FirstEdition.Volume1.Star3.star_3_2
      (p ⊃ₚ (q ⊃ₚ (p ≡ₚ q)))
      (p ⊃ₚ ((p ≡ₚ q) ⊃ₚ q))))
  have lift := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 p p (q ⊃ₚ (p ≡ₚ q)) ((p ≡ₚ q) ⊃ₚ q))
  have dup := infer (PM.FirstEdition.Volume1.Star3.star_3_2 p p) (PM.FirstEdition.Volume1.Star2.star_2_43 p (p ∧ₚ p))
  exact compose dup lift

/-- PM I (1910), p. 130, ✱5·53.  Instantiate ✱4·77 first at `p,q` and
then at `p ∨ q,r`; ✱4·36 transports the first equivalence beneath the
remaining conditional before the two explicit directions are recomposed. -/
theorem star_5_53 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ ((((p ∨ₚ q) ∨ₚ r) ⊃ₚ s) ≡ₚ (((p ⊃ₚ s) ∧ₚ (q ⊃ₚ s)) ∧ₚ (r ⊃ₚ s))) := by
  let a := (p ⊃ₚ s) ∧ₚ (q ⊃ₚ s)
  let b := (p ∨ₚ q) ⊃ₚ s
  let c := r ⊃ₚ s
  let d := ((p ∨ₚ q) ∨ₚ r) ⊃ₚ s
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have first : ⊢ₚ (a ≡ₚ b) := PM.FirstEdition.Volume1.Star4.star_4_77 s p q
  have second : ⊢ₚ ((b ∧ₚ c) ≡ₚ d) :=
    PM.FirstEdition.Volume1.Star4.star_4_77 s (p ∨ₚ q) r
  have transported : ⊢ₚ ((a ∧ₚ c) ≡ₚ (b ∧ₚ c)) :=
    infer first (PM.FirstEdition.Volume1.Star4.star_4_36 a b c)
  have forward1 : ⊢ₚ ((a ∧ₚ c) ⊃ₚ (b ∧ₚ c)) :=
    infer transported
      (PM.FirstEdition.Volume1.Star3.star_3_26
        ((a ∧ₚ c) ⊃ₚ (b ∧ₚ c)) ((b ∧ₚ c) ⊃ₚ (a ∧ₚ c)))
  have backward1 : ⊢ₚ ((b ∧ₚ c) ⊃ₚ (a ∧ₚ c)) :=
    infer transported
      (PM.FirstEdition.Volume1.Star3.star_3_27
        ((a ∧ₚ c) ⊃ₚ (b ∧ₚ c)) ((b ∧ₚ c) ⊃ₚ (a ∧ₚ c)))
  have forward2 : ⊢ₚ ((b ∧ₚ c) ⊃ₚ d) :=
    infer second
      (PM.FirstEdition.Volume1.Star3.star_3_26
        ((b ∧ₚ c) ⊃ₚ d) (d ⊃ₚ (b ∧ₚ c)))
  have backward2 : ⊢ₚ (d ⊃ₚ (b ∧ₚ c)) :=
    infer second
      (PM.FirstEdition.Volume1.Star3.star_3_27
        ((b ∧ₚ c) ⊃ₚ d) (d ⊃ₚ (b ∧ₚ c)))
  have forward : ⊢ₚ ((a ∧ₚ c) ⊃ₚ d) := compose forward1 forward2
  have backward : ⊢ₚ (d ⊃ₚ (a ∧ₚ c)) := compose backward2 backward1
  exact infer forward
    (infer backward
      (PM.FirstEdition.Volume1.Star3.star_3_2
        (d ⊃ₚ (a ∧ₚ c)) ((a ∧ₚ c) ⊃ₚ d)))

/-- PM I (1910), p. 130, ✱5·44.  With `p ⊃ q` fixed, the two implications
are proved from the three projections of the explicit conjunction; the
defined equivalence is then assembled under that same hypothesis. -/
theorem star_5_44 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ⊃ₚ r) ≡ₚ (p ⊃ₚ (q ∧ₚ r)))) := by
  let h := p ⊃ₚ q
  let a := p ⊃ₚ r
  let b := p ⊃ₚ (q ∧ₚ r)
  let x := (h ∧ₚ a) ∧ₚ p
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ},
      (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair : ⊢ₚ ((u ⊃ₚ v) ∧ₚ (u ⊃ₚ w)) :=
      infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have xha : ⊢ₚ (x ⊃ₚ (h ∧ₚ a)) := PM.FirstEdition.Volume1.Star3.star_3_26 (h ∧ₚ a) p
  have xh : ⊢ₚ (x ⊃ₚ h) := compose xha (PM.FirstEdition.Volume1.Star3.star_3_26 h a)
  have xa : ⊢ₚ (x ⊃ₚ a) := compose xha (PM.FirstEdition.Volume1.Star3.star_3_27 h a)
  have xp : ⊢ₚ (x ⊃ₚ p) := PM.FirstEdition.Volume1.Star3.star_3_27 (h ∧ₚ a) p
  have xq : ⊢ₚ (x ⊃ₚ q) :=
    compose (join xp xh) (PM.FirstEdition.Volume1.Star3.star_3_35 p q)
  have xr : ⊢ₚ (x ⊃ₚ r) :=
    compose (join xp xa) (PM.FirstEdition.Volume1.Star3.star_3_35 p r)
  have xqr : ⊢ₚ (x ⊃ₚ (q ∧ₚ r)) := join xq xr
  have forwardBase : ⊢ₚ ((h ∧ₚ a) ⊃ₚ b) :=
    infer xqr (PM.FirstEdition.Volume1.Star3.star_3_3 (h ∧ₚ a) p (q ∧ₚ r))
  have forward : ⊢ₚ (h ⊃ₚ (a ⊃ₚ b)) :=
    infer forwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 h a b)
  have backwardBase : ⊢ₚ (b ⊃ₚ a) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_27 q r)
      (PM.FirstEdition.Volume1.Star2.star_2_05 p (q ∧ₚ r) r)
  have backward : ⊢ₚ (h ⊃ₚ (b ⊃ₚ a)) :=
    infer backwardBase (PM.FirstEdition.Volume1.Star2.star_2_02 h (b ⊃ₚ a))
  exact join forward backward

/-- PM I (1910), p. 130, ✱5·42.  Each direction is reduced to an explicit
proof under `p` and `q`: the forward direction adjoins the available `p` to
`r`, and the reverse direction projects that same conjunction. -/
theorem star_5_42 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ⊃ₚ (p ∧ₚ r)))) := by
  let a := p ⊃ₚ (q ⊃ₚ r)
  let b := p ⊃ₚ (q ⊃ₚ (p ∧ₚ r))
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ},
      (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair : ⊢ₚ ((u ⊃ₚ v) ∧ₚ (u ⊃ₚ w)) :=
      infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  let xf := (a ∧ₚ p) ∧ₚ q
  have xfap : ⊢ₚ (xf ⊃ₚ (a ∧ₚ p)) := PM.FirstEdition.Volume1.Star3.star_3_26 (a ∧ₚ p) q
  have xfa : ⊢ₚ (xf ⊃ₚ a) := compose xfap (PM.FirstEdition.Volume1.Star3.star_3_26 a p)
  have xfp : ⊢ₚ (xf ⊃ₚ p) := compose xfap (PM.FirstEdition.Volume1.Star3.star_3_27 a p)
  have xfq : ⊢ₚ (xf ⊃ₚ q) := PM.FirstEdition.Volume1.Star3.star_3_27 (a ∧ₚ p) q
  have xfpq : ⊢ₚ (xf ⊃ₚ (p ∧ₚ q)) := join xfp xfq
  have xfh : ⊢ₚ (xf ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)) :=
    compose xfa (PM.FirstEdition.Volume1.Star3.star_3_31 p q r)
  have xfpr : ⊢ₚ (xf ⊃ₚ r) :=
    compose (join xfpq xfh) (PM.FirstEdition.Volume1.Star3.star_3_35 (p ∧ₚ q) r)
  have forwardBase : ⊢ₚ (xf ⊃ₚ (p ∧ₚ r)) := join xfp xfpr
  have forward : ⊢ₚ (a ⊃ₚ b) :=
    infer (infer forwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 (a ∧ₚ p) q (p ∧ₚ r)))
      (PM.FirstEdition.Volume1.Star3.star_3_3 a p (q ⊃ₚ (p ∧ₚ r)))
  let xb := (b ∧ₚ p) ∧ₚ q
  have xbap : ⊢ₚ (xb ⊃ₚ (b ∧ₚ p)) := PM.FirstEdition.Volume1.Star3.star_3_26 (b ∧ₚ p) q
  have xbb : ⊢ₚ (xb ⊃ₚ b) := compose xbap (PM.FirstEdition.Volume1.Star3.star_3_26 b p)
  have xbp : ⊢ₚ (xb ⊃ₚ p) := compose xbap (PM.FirstEdition.Volume1.Star3.star_3_27 b p)
  have xbq : ⊢ₚ (xb ⊃ₚ q) := PM.FirstEdition.Volume1.Star3.star_3_27 (b ∧ₚ p) q
  have xbpq : ⊢ₚ (xb ⊃ₚ (p ∧ₚ q)) := join xbp xbq
  have xbh : ⊢ₚ (xb ⊃ₚ ((p ∧ₚ q) ⊃ₚ (p ∧ₚ r))) :=
    compose xbb (PM.FirstEdition.Volume1.Star3.star_3_31 p q (p ∧ₚ r))
  have xbpr : ⊢ₚ (xb ⊃ₚ (p ∧ₚ r)) :=
    compose (join xbpq xbh) (PM.FirstEdition.Volume1.Star3.star_3_35 (p ∧ₚ q) (p ∧ₚ r))
  have backwardBase : ⊢ₚ (xb ⊃ₚ r) :=
    compose xbpr (PM.FirstEdition.Volume1.Star3.star_3_27 p r)
  have backward : ⊢ₚ (b ⊃ₚ a) :=
    infer (infer backwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 (b ∧ₚ p) q r))
      (PM.FirstEdition.Volume1.Star3.star_3_3 b p (q ⊃ₚ r))
  exact infer backward
    (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

/-- PM I (1910), p. 130, ✱5·3.  Under `p ∧ q`, an available conclusion
`r` pairs with the first projection `p`; conversely the second component of
that pair recovers `r`. -/
theorem star_5_3 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ≡ₚ ((p ∧ₚ q) ⊃ₚ (p ∧ₚ r))) := by
  let h := p ∧ₚ q
  let a := h ⊃ₚ r
  let b := h ⊃ₚ (p ∧ₚ r)
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ},
      (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair : ⊢ₚ ((u ⊃ₚ v) ∧ₚ (u ⊃ₚ w)) :=
      infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have forwardBase : ⊢ₚ ((a ∧ₚ h) ⊃ₚ (p ∧ₚ r)) := by
    have ha : ⊢ₚ ((a ∧ₚ h) ⊃ₚ a) := PM.FirstEdition.Volume1.Star3.star_3_26 a h
    have hh : ⊢ₚ ((a ∧ₚ h) ⊃ₚ h) := PM.FirstEdition.Volume1.Star3.star_3_27 a h
    have hp : ⊢ₚ ((a ∧ₚ h) ⊃ₚ p) := compose hh (PM.FirstEdition.Volume1.Star3.star_3_26 p q)
    have hr : ⊢ₚ ((a ∧ₚ h) ⊃ₚ r) :=
    compose (join hh ha) (PM.FirstEdition.Volume1.Star3.star_3_35 h r)
    exact join hp hr
  have forward : ⊢ₚ (a ⊃ₚ b) :=
    infer forwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 a h (p ∧ₚ r))
  have backward : ⊢ₚ (b ⊃ₚ a) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_27 p r)
      (PM.FirstEdition.Volume1.Star2.star_2_05 h (p ∧ₚ r) r)
  exact infer backward
    (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

/-- PM I (1910), p. 130, ✱5·36.  The printed `Ass . ✱4·38` is
expanded by projecting the two directions of `p ≡ q`, applying each under
the corresponding conjunction, and retaining the common equivalence factor. -/
theorem star_5_36 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ (p ≡ₚ q)) ≡ₚ (q ∧ₚ (p ≡ₚ q))) := by
  let e := p ≡ₚ q
  let a := p ∧ₚ e
  let b := q ∧ₚ e
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ},
      (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair : ⊢ₚ ((u ⊃ₚ v) ∧ₚ (u ⊃ₚ w)) :=
      infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have forward : ⊢ₚ (a ⊃ₚ b) := by
    have haP : ⊢ₚ (a ⊃ₚ p) := PM.FirstEdition.Volume1.Star3.star_3_26 p e
    have haE : ⊢ₚ (a ⊃ₚ e) := PM.FirstEdition.Volume1.Star3.star_3_27 p e
    have haPQ : ⊢ₚ (a ⊃ₚ (p ⊃ₚ q)) :=
      compose haE (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p))
    have haQ : ⊢ₚ (a ⊃ₚ q) :=
      compose (join haP haPQ) (PM.FirstEdition.Volume1.Star3.star_3_35 p q)
    exact join haQ haE
  have backward : ⊢ₚ (b ⊃ₚ a) := by
    have hbQ : ⊢ₚ (b ⊃ₚ q) := PM.FirstEdition.Volume1.Star3.star_3_26 q e
    have hbE : ⊢ₚ (b ⊃ₚ e) := PM.FirstEdition.Volume1.Star3.star_3_27 q e
    have hbQP : ⊢ₚ (b ⊃ₚ (q ⊃ₚ p)) :=
      compose hbE (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p))
    have hbP : ⊢ₚ (b ⊃ₚ p) :=
      compose (join hbQ hbQP) (PM.FirstEdition.Volume1.Star3.star_3_35 q p)
    exact join hbP hbE
  exact infer backward
    (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

/-- PM I (1910), p. 129, ✱5·11. -/
theorem star_5_11 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ∨ₚ ((∼ₚ p) ⊃ₚ q)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer (PM.FirstEdition.Volume1.Star2.star_2_5 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_54 (p ⊃ₚ q) ((∼ₚ p) ⊃ₚ q))

/-- PM I (1910), p. 129, ✱5·12. -/
theorem star_5_12 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ (∼ₚ q))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer (PM.FirstEdition.Volume1.Star2.star_2_51 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_54 (p ⊃ₚ q) (p ⊃ₚ (∼ₚ q)))

/-- PM I (1910), p. 130, ✱5·61.  Under `∼q`, ✱2·55 eliminates
the `q` branch of `p ∨ q`; the converse adds that branch by ✱2·2. -/
theorem star_5_61 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∧ₚ (∼ₚ q)) ≡ₚ (p ∧ₚ (∼ₚ q))) := by
  let a := (p ∨ₚ q) ∧ₚ (∼ₚ q)
  let b := p ∧ₚ (∼ₚ q)
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t) (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair : ⊢ₚ ((u ⊃ₚ v) ∧ₚ (u ⊃ₚ w)) := infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have forward : ⊢ₚ (a ⊃ₚ b) := by
    have haDisj : ⊢ₚ (a ⊃ₚ (p ∨ₚ q)) := PM.FirstEdition.Volume1.Star3.star_3_26 (p ∨ₚ q) (∼ₚ q)
    have haNotQ : ⊢ₚ (a ⊃ₚ (∼ₚ q)) := PM.FirstEdition.Volume1.Star3.star_3_27 (p ∨ₚ q) (∼ₚ q)
    have haElim : ⊢ₚ (a ⊃ₚ ((q ∨ₚ p) ⊃ₚ p)) := compose haNotQ (PM.FirstEdition.Volume1.Star2.star_2_55 q p)
    have haSwap : ⊢ₚ (a ⊃ₚ (q ∨ₚ p)) := compose haDisj (PM.Derivation.star_1_4 p q)
    have haP : ⊢ₚ (a ⊃ₚ p) := compose (join haSwap haElim) (PM.FirstEdition.Volume1.Star3.star_3_35 (q ∨ₚ p) p)
    exact join haP haNotQ
  have backward : ⊢ₚ (b ⊃ₚ a) := by
    have hbP : ⊢ₚ (b ⊃ₚ p) := PM.FirstEdition.Volume1.Star3.star_3_26 p (∼ₚ q)
    have hbNotQ : ⊢ₚ (b ⊃ₚ (∼ₚ q)) := PM.FirstEdition.Volume1.Star3.star_3_27 p (∼ₚ q)
    have hbDisj : ⊢ₚ (b ⊃ₚ (p ∨ₚ q)) := compose hbP (PM.FirstEdition.Volume1.Star2.star_2_2 p q)
    exact join hbDisj hbNotQ
  exact infer backward (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

/-- PM I (1910), p. 131, ✱5·71. -/
theorem star_5_71 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ (∼ₚ r)) ⊃ₚ ((((p ∨ₚ q) ∧ₚ r) ≡ₚ (p ∧ₚ r)))) := by
  let h := q ⊃ₚ (∼ₚ r)
  let a := (p ∨ₚ q) ∧ₚ r
  let b := p ∧ₚ r
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t) (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have forwardBase : ⊢ₚ ((h ∧ₚ a) ⊃ₚ b) := by
    let x := h ∧ₚ a
    have hxH : ⊢ₚ (x ⊃ₚ h) := PM.FirstEdition.Volume1.Star3.star_3_26 h a
    have hxA : ⊢ₚ (x ⊃ₚ a) := PM.FirstEdition.Volume1.Star3.star_3_27 h a
    have hxDisj := compose hxA (PM.FirstEdition.Volume1.Star3.star_3_26 (p ∨ₚ q) r)
    have hxR := compose hxA (PM.FirstEdition.Volume1.Star3.star_3_27 (p ∨ₚ q) r)
    have hxTrans := compose hxH (PM.FirstEdition.Volume1.Star2.star_2_16 q (∼ₚ r))
    have hxNNR := compose hxR (PM.FirstEdition.Volume1.Star2.star_2_12 r)
    have hxNotQ := compose (join hxNNR hxTrans) (PM.FirstEdition.Volume1.Star3.star_3_35 (∼ₚ (∼ₚ r)) (∼ₚ q))
    have hxElim := compose hxNotQ (PM.FirstEdition.Volume1.Star2.star_2_55 q p)
    have hxSwap := compose hxDisj (PM.Derivation.star_1_4 p q)
    have hxP := compose (join hxSwap hxElim) (PM.FirstEdition.Volume1.Star3.star_3_35 (q ∨ₚ p) p)
    exact join hxP hxR
  have forward : ⊢ₚ (h ⊃ₚ (a ⊃ₚ b)) := infer forwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 h a b)
  have backward0 : ⊢ₚ (b ⊃ₚ a) := by
    have bp := PM.FirstEdition.Volume1.Star3.star_3_26 p r
    have br := PM.FirstEdition.Volume1.Star3.star_3_27 p r
    exact join (compose bp (PM.FirstEdition.Volume1.Star2.star_2_2 p q)) br
  have backward : ⊢ₚ (h ⊃ₚ (b ⊃ₚ a)) := infer backward0 (PM.FirstEdition.Volume1.Star2.star_2_02 h (b ⊃ₚ a))
  have pair := infer backward (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (h ⊃ₚ (a ⊃ₚ b)) (h ⊃ₚ (b ⊃ₚ a))))
  have lifted := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 h h (a ⊃ₚ b) (b ⊃ₚ a))
  exact compose (duplicate h) lifted

/-- PM I (1910), p. 130, ✱5·55. -/
theorem star_5_55 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ≡ₚ p) ∨ₚ ((p ∨ₚ q) ≡ₚ q)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have dup : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t) (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) := by
    intro a b c hab hac
    have pair := infer hac (infer hab (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    exact comp (dup a) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c))
  have mapOr : ∀ {a b x y : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ x)) → (⊢ₚ (b ⊃ₚ y)) → (⊢ₚ ((a ∨ₚ b) ⊃ₚ (x ∨ₚ y))) := by
    intro a b x y hax hby
    have l := infer hax (PM.FirstEdition.Volume1.Star2.star_2_36 b a x)
    have r0 := infer hby (PM.FirstEdition.Volume1.Star2.star_2_36 x b y)
    exact comp (PM.Derivation.star_1_4 a b) (comp l (comp r0 (PM.Derivation.star_1_4 y x)))
  have eQ : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ∨ₚ q) ≡ₚ q)) := by
    have f := PM.FirstEdition.Volume1.Star2.star_2_621 p q
    have g : ⊢ₚ (q ⊃ₚ (p ∨ₚ q)) := comp (PM.FirstEdition.Volume1.Star2.star_2_2 q p) (PM.Derivation.star_1_4 q p)
    exact join f (infer g (PM.FirstEdition.Volume1.Star2.star_2_02 (p ⊃ₚ q) (q ⊃ₚ (p ∨ₚ q))))
  have eP : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ ((p ∨ₚ q) ≡ₚ p)) := by
    have raw := PM.FirstEdition.Volume1.Star2.star_2_621 q p
    have perm : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) := PM.Derivation.star_1_4 p q
    have syll := PM.FirstEdition.Volume1.Star2.star_2_05 (p ∨ₚ q) (q ∨ₚ p) p
    have reorder := infer syll (PM.FirstEdition.Volume1.Star2.star_2_04 ((q ∨ₚ p) ⊃ₚ p) ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) ((p ∨ₚ q) ⊃ₚ p))
    have cvt : ⊢ₚ (((q ∨ₚ p) ⊃ₚ p) ⊃ₚ ((p ∨ₚ q) ⊃ₚ p)) := infer perm reorder
    have f := comp raw cvt
    have g : ⊢ₚ (p ⊃ₚ (p ∨ₚ q)) := PM.FirstEdition.Volume1.Star2.star_2_2 p q
    exact join f (infer g (PM.FirstEdition.Volume1.Star2.star_2_02 (q ⊃ₚ p) (p ⊃ₚ (p ∨ₚ q))))
  have mapped : ⊢ₚ (((p ∨ₚ q) ≡ₚ q) ∨ₚ ((p ∨ₚ q) ≡ₚ p)) := infer (star_5_13 p q) (mapOr eQ eP)
  exact infer mapped (PM.Derivation.star_1_4 ((p ∨ₚ q) ≡ₚ q) ((p ∨ₚ q) ≡ₚ p))

/-- PM I (1910), p. 130, ✱5·62.  Exact printed substitution
`(q,p)/(p,q)` in ✱4·7, using implication's definitional disjunction. -/
theorem star_5_62 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ∨ₚ (∼ₚ q)) ≡ₚ (p ∨ₚ (∼ₚ q))) := by
  let a := (∼ₚ q) ∨ₚ p
  let b := (∼ₚ q) ∨ₚ (q ∧ₚ p)
  let c := (p ∧ₚ q) ∨ₚ (∼ₚ q)
  let d := p ∨ₚ (∼ₚ q)
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have e := PM.FirstEdition.Volume1.Star4.star_4_7 q p
  have eForward : ⊢ₚ (a ⊃ₚ b) := infer e (PM.FirstEdition.Volume1.Star3.star_3_26 (a ⊃ₚ b) (b ⊃ₚ a))
  have eBackward : ⊢ₚ (b ⊃ₚ a) := infer e (PM.FirstEdition.Volume1.Star3.star_3_27 (a ⊃ₚ b) (b ⊃ₚ a))
  have cToB : ⊢ₚ (c ⊃ₚ b) := by
    have swapOuter : ⊢ₚ (c ⊃ₚ ((∼ₚ q) ∨ₚ (p ∧ₚ q))) := PM.Derivation.star_1_4 (p ∧ₚ q) (∼ₚ q)
    have liftInner : ⊢ₚ (((∼ₚ q) ∨ₚ (p ∧ₚ q)) ⊃ₚ b) :=
      infer (PM.FirstEdition.Volume1.Star3.star_3_22 p q) (PM.Derivation.star_1_6 (∼ₚ q) (p ∧ₚ q) (q ∧ₚ p))
    exact compose swapOuter liftInner
  have bToC : ⊢ₚ (b ⊃ₚ c) := by
    have liftInner : ⊢ₚ (b ⊃ₚ ((∼ₚ q) ∨ₚ (p ∧ₚ q))) :=
      infer (PM.FirstEdition.Volume1.Star3.star_3_22 q p) (PM.Derivation.star_1_6 (∼ₚ q) (q ∧ₚ p) (p ∧ₚ q))
    exact compose liftInner (PM.Derivation.star_1_4 (∼ₚ q) (p ∧ₚ q))
  have forward : ⊢ₚ (c ⊃ₚ d) := compose cToB (compose eBackward (PM.Derivation.star_1_4 (∼ₚ q) p))
  have backward : ⊢ₚ (d ⊃ₚ c) := compose (PM.Derivation.star_1_4 p (∼ₚ q)) (compose eForward bToC)
  exact infer backward (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (c ⊃ₚ d) (d ⊃ₚ c)))

/-- PM I (1910), p. 131, ✱5·63. -/
theorem star_5_63 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ q) ≡ₚ (p ∨ₚ ((∼ₚ p) ∧ₚ q))) := by
  let x := (q ∧ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ p))
  let y := q ∨ₚ (∼ₚ (∼ₚ p))
  let a := p ∨ₚ q
  let b := p ∨ₚ ((∼ₚ p) ∧ₚ q)
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC; exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have lift : ∀ (r : PM.Elementary Γ) {u v}, (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ ((r ∨ₚ u) ⊃ₚ (r ∨ₚ v))) := by
    intro r u v huv; exact infer huv (PM.Derivation.star_1_6 r u v)
  have e := star_5_62 q (∼ₚ p)
  have exy : ⊢ₚ (x ⊃ₚ y) := infer e (PM.FirstEdition.Volume1.Star3.star_3_26 (x ⊃ₚ y) (y ⊃ₚ x))
  have eyx : ⊢ₚ (y ⊃ₚ x) := infer e (PM.FirstEdition.Volume1.Star3.star_3_27 (x ⊃ₚ y) (y ⊃ₚ x))
  have aToY : ⊢ₚ (a ⊃ₚ y) := comp (PM.Derivation.star_1_4 p q) (lift q (PM.FirstEdition.Volume1.Star2.star_2_12 p))
  have yToA : ⊢ₚ (y ⊃ₚ a) := comp (lift q (PM.FirstEdition.Volume1.Star2.star_2_14 p)) (PM.Derivation.star_1_4 q p)
  have bToX : ⊢ₚ (b ⊃ₚ x) := by
    have s1 := PM.Derivation.star_1_4 p ((∼ₚ p) ∧ₚ q)
    have s2 := lift ((∼ₚ p) ∧ₚ q) (PM.FirstEdition.Volume1.Star2.star_2_12 p)
    have s3 := lift (∼ₚ (∼ₚ p)) (PM.FirstEdition.Volume1.Star3.star_3_22 (∼ₚ p) q)
    exact comp s1 (comp s2 (comp (PM.Derivation.star_1_4 ((∼ₚ p) ∧ₚ q) (∼ₚ (∼ₚ p))) (comp s3 (PM.Derivation.star_1_4 (∼ₚ (∼ₚ p)) (q ∧ₚ (∼ₚ p))))))
  have xToB : ⊢ₚ (x ⊃ₚ b) := by
    have s1 := PM.Derivation.star_1_4 (q ∧ₚ (∼ₚ p)) (∼ₚ (∼ₚ p))
    have s2 := lift (∼ₚ (∼ₚ p)) (PM.FirstEdition.Volume1.Star3.star_3_22 q (∼ₚ p))
    have s3 := lift ((∼ₚ p) ∧ₚ q) (PM.FirstEdition.Volume1.Star2.star_2_14 p)
    exact comp s1 (comp s2 (comp (PM.Derivation.star_1_4 (∼ₚ (∼ₚ p)) ((∼ₚ p) ∧ₚ q)) (comp s3 (PM.Derivation.star_1_4 ((∼ₚ p) ∧ₚ q) p))))
  have forward := comp aToY (comp eyx xToB)
  have backward := comp bToX (comp exy yToA)
  exact infer backward (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

/-- PM I (1910), p. 130, ✱5·54. -/
theorem star_5_54 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ≡ₚ p) ∨ₚ ((p ∧ₚ q) ≡ₚ q)) := by
  let h := p ∧ₚ q
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have dup : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t) (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) := by
    intro a b c hab hac
    have pair := infer hac (infer hab (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    exact comp (dup a) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c))
  have mapOr : ∀ {a b x y : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ x)) → (⊢ₚ (b ⊃ₚ y)) → (⊢ₚ ((a ∨ₚ b) ⊃ₚ (x ∨ₚ y))) := by
    intro a b x y hax hby
    have l := infer hax (PM.FirstEdition.Volume1.Star2.star_2_36 b a x)
    have r0 := infer hby (PM.FirstEdition.Volume1.Star2.star_2_36 x b y)
    exact comp (PM.Derivation.star_1_4 a b) (comp l (comp r0 (PM.Derivation.star_1_4 y x)))
  have toP : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (h ≡ₚ p)) := by
    have e := PM.FirstEdition.Volume1.Star4.star_4_7 p q
    have reverse : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ h)) :=
      infer e (PM.FirstEdition.Volume1.Star3.star_3_26 ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ h)) ((p ⊃ₚ h) ⊃ₚ (p ⊃ₚ q)))
    have forward : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (h ⊃ₚ p)) := infer (PM.FirstEdition.Volume1.Star3.star_3_26 p q) (PM.FirstEdition.Volume1.Star2.star_2_02 (p ⊃ₚ q) (h ⊃ₚ p))
    exact join forward reverse
  have toQ : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (h ≡ₚ q)) := by
    have e := PM.FirstEdition.Volume1.Star4.star_4_7 q p
    have raw : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (q ⊃ₚ (q ∧ₚ p))) :=
      infer e (PM.FirstEdition.Volume1.Star3.star_3_26 ((q ⊃ₚ p) ⊃ₚ (q ⊃ₚ (q ∧ₚ p))) ((q ⊃ₚ (q ∧ₚ p)) ⊃ₚ (q ⊃ₚ p)))
    have swap : ⊢ₚ ((q ∧ₚ p) ⊃ₚ h) := PM.FirstEdition.Volume1.Star3.star_3_22 q p
    have liftedSwap : ⊢ₚ ((q ⊃ₚ (q ∧ₚ p)) ⊃ₚ (q ⊃ₚ h)) :=
      infer (infer swap (PM.FirstEdition.Volume1.Star2.star_2_02 q ((q ∧ₚ p) ⊃ₚ h)))
        (PM.FirstEdition.Volume1.Star2.star_2_77 q (q ∧ₚ p) h)
    have reverse : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (q ⊃ₚ h)) := comp raw liftedSwap
    have forward : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (h ⊃ₚ q)) := infer (PM.FirstEdition.Volume1.Star3.star_3_27 p q) (PM.FirstEdition.Volume1.Star2.star_2_02 (q ⊃ₚ p) (h ⊃ₚ q))
    exact join forward reverse
  exact infer (star_5_13 p q) (mapOr toP toQ)

/-- PM I (1910), p. 130, ✱5·6.  The exportation component of ✱4·87 is
followed by the explicitly packaged equivalence `∼q ⊃ r ≡ q ∨ r` under `p`. -/
theorem star_5_6 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ (∼ₚ q)) ⊃ₚ r) ≡ₚ (p ⊃ₚ (q ∨ₚ r))) := by
  let a := (p ∧ₚ (∼ₚ q)) ⊃ₚ r
  let b := p ⊃ₚ ((∼ₚ q) ⊃ₚ r)
  let c := p ⊃ₚ (q ∨ₚ r)
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have exportation : ⊢ₚ (a ≡ₚ b) := by
    have chain := PM.FirstEdition.Volume1.Star4.star_4_87 p (∼ₚ q) r
    have firstPair := infer chain (PM.FirstEdition.Volume1.Star3.star_3_26
      ((a ≡ₚ b) ∧ₚ ((b) ≡ₚ ((∼ₚ q) ⊃ₚ (p ⊃ₚ r))))
      (((∼ₚ q) ⊃ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚ q ∧ₚ p) ⊃ₚ r)))
    exact infer firstPair (PM.FirstEdition.Volume1.Star3.star_3_26
      (a ≡ₚ b) ((b) ≡ₚ ((∼ₚ q) ⊃ₚ (p ⊃ₚ r))))
  have midForward : ⊢ₚ (((∼ₚ q) ⊃ₚ r) ⊃ₚ (q ∨ₚ r)) := PM.FirstEdition.Volume1.Star2.star_2_54 q r
  have midBackward : ⊢ₚ ((q ∨ₚ r) ⊃ₚ ((∼ₚ q) ⊃ₚ r)) := PM.FirstEdition.Volume1.Star2.star_2_53 q r
  have bToC : ⊢ₚ (b ⊃ₚ c) :=
    infer (infer midForward (PM.FirstEdition.Volume1.Star2.star_2_02 p (((∼ₚ q) ⊃ₚ r) ⊃ₚ (q ∨ₚ r))))
      (PM.FirstEdition.Volume1.Star2.star_2_77 p ((∼ₚ q) ⊃ₚ r) (q ∨ₚ r))
  have cToB : ⊢ₚ (c ⊃ₚ b) :=
    infer (infer midBackward (PM.FirstEdition.Volume1.Star2.star_2_02 p ((q ∨ₚ r) ⊃ₚ ((∼ₚ q) ⊃ₚ r))))
      (PM.FirstEdition.Volume1.Star2.star_2_77 p (q ∨ₚ r) ((∼ₚ q) ⊃ₚ r))
  have aToB : ⊢ₚ (a ⊃ₚ b) := infer exportation (PM.FirstEdition.Volume1.Star3.star_3_26 (a ⊃ₚ b) (b ⊃ₚ a))
  have bToA : ⊢ₚ (b ⊃ₚ a) := infer exportation (PM.FirstEdition.Volume1.Star3.star_3_27 (a ⊃ₚ b) (b ⊃ₚ a))
  have forward : ⊢ₚ (a ⊃ₚ c) := comp aToB bToC
  have backward : ⊢ₚ (c ⊃ₚ a) := comp cToB bToA
  exact infer backward (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ c) (c ⊃ₚ a)))

/-- PM I (1910), p. 131, ✱5·7. -/
theorem star_5_7 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((((p ∨ₚ r) ≡ₚ (q ∨ₚ r)) ≡ₚ (r ∨ₚ (p ≡ₚ q)))) := by
  let A := p ∨ₚ r; let B := q ∨ₚ r; let E := A ≡ₚ B
  let P := p ≡ₚ q; let F := r ∨ₚ P; let n := ∼ₚ r; let x := n ∧ₚ E
  have infer : ∀ {a b : PM.Elementary Γ}, (⊢ₚ a) → (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ b) := by
    intro a b ha hab; match Γ, a, b, ha, hab with
    | [], _, _, ha, hab => exact PM.Derivation.star_1_1 ha hab
    | (τ :: Δ), _, _, ha, hab => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) ha hab
  have comp : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (b ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ c)) := by
    intro a b c hab hbc; exact infer hab (infer hbc (PM.FirstEdition.Volume1.Star2.star_2_05 a b c))
  have dup : ∀ a : PM.Elementary Γ, ⊢ₚ (a ⊃ₚ (a ∧ₚ a)) := by
    intro a; exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 a a) (PM.FirstEdition.Volume1.Star2.star_2_43 a (a ∧ₚ a))
  have join : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) := by
    intro a b c hab hac
    have pair := infer hac (infer hab (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    exact comp (dup a) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c))
  have xN := PM.FirstEdition.Volume1.Star3.star_3_26 n E
  have xE := PM.FirstEdition.Volume1.Star3.star_3_27 n E
  have eliminate : ∀ z : PM.Elementary Γ, ⊢ₚ (x ⊃ₚ ((z ∨ₚ r) ⊃ₚ z)) := by
    intro z
    have base : ⊢ₚ (n ⊃ₚ ((r ∨ₚ z) ⊃ₚ z)) := PM.FirstEdition.Volume1.Star2.star_2_55 r z
    have cvt : ⊢ₚ (((r ∨ₚ z) ⊃ₚ z) ⊃ₚ ((z ∨ₚ r) ⊃ₚ z)) :=
      infer (PM.Derivation.star_1_4 z r) (PM.FirstEdition.Volume1.Star2.star_2_06 (z ∨ₚ r) (r ∨ₚ z) z)
    exact comp xN (comp base cvt)
  have xPQ : ⊢ₚ (x ⊃ₚ (p ⊃ₚ q)) := by
    let y := x ∧ₚ p
    have yX := PM.FirstEdition.Volume1.Star3.star_3_26 x p
    have yP := PM.FirstEdition.Volume1.Star3.star_3_27 x p
    have yA := comp yP (PM.FirstEdition.Volume1.Star2.star_2_2 p r)
    have yEF := comp yX (comp xE (PM.FirstEdition.Volume1.Star3.star_3_26 (A ⊃ₚ B) (B ⊃ₚ A)))
    have yB := comp (join yA yEF) (PM.FirstEdition.Volume1.Star3.star_3_35 A B)
    have yElim := comp yX (eliminate q)
    have yQ := comp (join yB yElim) (PM.FirstEdition.Volume1.Star3.star_3_35 B q)
    exact infer yQ (PM.FirstEdition.Volume1.Star3.star_3_3 x p q)
  have xQP : ⊢ₚ (x ⊃ₚ (q ⊃ₚ p)) := by
    let y := x ∧ₚ q
    have yX := PM.FirstEdition.Volume1.Star3.star_3_26 x q
    have yQ := PM.FirstEdition.Volume1.Star3.star_3_27 x q
    have yB := comp yQ (PM.FirstEdition.Volume1.Star2.star_2_2 q r)
    have yEB := comp yX (comp xE (PM.FirstEdition.Volume1.Star3.star_3_27 (A ⊃ₚ B) (B ⊃ₚ A)))
    have yA := comp (join yB yEB) (PM.FirstEdition.Volume1.Star3.star_3_35 B A)
    have yElim := comp yX (eliminate p)
    have yP := comp (join yA yElim) (PM.FirstEdition.Volume1.Star3.star_3_35 A p)
    exact infer yP (PM.FirstEdition.Volume1.Star3.star_3_3 x q p)
  have xP : ⊢ₚ (x ⊃ₚ P) := join xPQ xQP
  have nEP : ⊢ₚ (n ⊃ₚ (E ⊃ₚ P)) := infer xP (PM.FirstEdition.Volume1.Star3.star_3_3 n E P)
  have eNP : ⊢ₚ (E ⊃ₚ (n ⊃ₚ P)) := infer nEP (PM.FirstEdition.Volume1.Star2.star_2_04 n E P)
  have eF : ⊢ₚ (E ⊃ₚ F) := comp eNP (PM.FirstEdition.Volume1.Star2.star_2_54 r P)
  have rE : ⊢ₚ (r ⊃ₚ E) := by
    have ra := comp (PM.FirstEdition.Volume1.Star2.star_2_2 r p) (PM.Derivation.star_1_4 r p)
    have rb := comp (PM.FirstEdition.Volume1.Star2.star_2_2 r q) (PM.Derivation.star_1_4 r q)
    exact comp (join ra rb) (star_5_1 A B)
  have pE : ⊢ₚ (P ⊃ₚ E) := PM.FirstEdition.Volume1.Star4.star_4_37 p q r
  have fE : ⊢ₚ (F ⊃ₚ E) := by
    have pair : ⊢ₚ ((r ⊃ₚ E) ∧ₚ (P ⊃ₚ E)) :=
      infer pE (infer rE (PM.FirstEdition.Volume1.Star3.star_3_2 (r ⊃ₚ E) (P ⊃ₚ E)))
    have eqv := PM.FirstEdition.Volume1.Star4.star_4_77 E r P
    have bridge : ⊢ₚ (((r ⊃ₚ E) ∧ₚ (P ⊃ₚ E)) ⊃ₚ (F ⊃ₚ E)) :=
      infer eqv (PM.FirstEdition.Volume1.Star3.star_3_26
        (((r ⊃ₚ E) ∧ₚ (P ⊃ₚ E)) ⊃ₚ (F ⊃ₚ E))
        ((F ⊃ₚ E) ⊃ₚ ((r ⊃ₚ E) ∧ₚ (P ⊃ₚ E))))
    exact infer pair bridge
  exact infer fE (infer eF (PM.FirstEdition.Volume1.Star3.star_3_2 (E ⊃ₚ F) (F ⊃ₚ E)))

/-- PM I (1910), p. 131, ✱5·74. -/
theorem star_5_74 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ≡ₚ r)) ≡ₚ ((p ⊃ₚ q) ≡ₚ (p ⊃ₚ r))) := by
  let a := p ⊃ₚ (q ≡ₚ r)
  let x := (p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)
  let y := (p ⊃ₚ r) ⊃ₚ (p ⊃ₚ q)
  let u := p ⊃ₚ (q ⊃ₚ r)
  let v := p ⊃ₚ (r ⊃ₚ q)
  let b := x ∧ₚ y
  let c := u ∧ₚ v
  have infer : ∀ {m n : PM.Elementary Γ}, (⊢ₚ m) → (⊢ₚ (m ⊃ₚ n)) → (⊢ₚ n) := by
    intro m n hm hmn; match Γ, m, n, hm, hmn with
    | [], _, _, hm, hmn => exact PM.Derivation.star_1_1 hm hmn
    | (τ :: Δ), _, _, hm, hmn => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hm hmn
  have comp : ∀ {m n o : PM.Elementary Γ}, (⊢ₚ (m ⊃ₚ n)) → (⊢ₚ (n ⊃ₚ o)) → (⊢ₚ (m ⊃ₚ o)) := by
    intro m n o hmn hno; exact infer hmn (infer hno (PM.FirstEdition.Volume1.Star2.star_2_05 m n o))
  have e1 := star_5_41 p q r
  have e2 := star_5_41 p r q
  have pairE : ⊢ₚ ((x ≡ₚ u) ∧ₚ (y ≡ₚ v)) :=
    infer e2 (infer e1 (PM.FirstEdition.Volume1.Star3.star_3_2 (x ≡ₚ u) (y ≡ₚ v)))
  have bc : ⊢ₚ (b ≡ₚ c) := infer pairE (PM.FirstEdition.Volume1.Star4.star_4_38 x y u v)
  have ca : ⊢ₚ (c ≡ₚ a) := PM.FirstEdition.Volume1.Star4.star_4_76 p (q ⊃ₚ r) (r ⊃ₚ q)
  have bToC := infer bc (PM.FirstEdition.Volume1.Star3.star_3_26 (b ⊃ₚ c) (c ⊃ₚ b))
  have cToB := infer bc (PM.FirstEdition.Volume1.Star3.star_3_27 (b ⊃ₚ c) (c ⊃ₚ b))
  have cToA := infer ca (PM.FirstEdition.Volume1.Star3.star_3_26 (c ⊃ₚ a) (a ⊃ₚ c))
  have aToC := infer ca (PM.FirstEdition.Volume1.Star3.star_3_27 (c ⊃ₚ a) (a ⊃ₚ c))
  have aToB := comp aToC cToB
  have bToA := comp bToC cToA
  exact infer bToA (infer aToB (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

end PM.FirstEdition.Volume1.Star5
