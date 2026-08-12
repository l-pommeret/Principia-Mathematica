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
    infer (compose (PM.FirstEdition.Volume1.Star3.star_3_27 p q) (PM.FirstEdition.Volume1.Star2.star_2_02 q p))
      (PM.FirstEdition.Volume1.Star3.star_3_3 p q a)
  have pair := infer forward (infer backward (PM.FirstEdition.Volume1.Star3.star_3_2 (p ⊃ₚ (a ⊃ₚ q)) (p ⊃ₚ (q ⊃ₚ a))))
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
    have pair := infer hp (infer he (PM.FirstEdition.Volume1.Star3.star_3_2 ((p ∧ₚ (p ≡ₚ q)) ⊃ₚ p) ((p ∧ₚ (p ≡ₚ q)) ⊃ₚ (p ⊃ₚ q))))
    have lift := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 (p ∧ₚ (p ≡ₚ q)) (p ∧ₚ (p ≡ₚ q)) p (p ⊃ₚ q))
    have dup := infer (PM.FirstEdition.Volume1.Star3.star_3_2 (p ∧ₚ (p ≡ₚ q)) (p ∧ₚ (p ≡ₚ q))) (PM.FirstEdition.Volume1.Star2.star_2_43 (p ∧ₚ (p ≡ₚ q)) ((p ∧ₚ (p ≡ₚ q)) ∧ₚ (p ∧ₚ (p ≡ₚ q))))
    exact compose (compose dup lift) (PM.FirstEdition.Volume1.Star3.star_3_35 p q)
  have backward := infer backwardBase (PM.FirstEdition.Volume1.Star3.star_3_3 p (p ≡ₚ q) q)
  have pair := infer forward (infer backward (PM.FirstEdition.Volume1.Star3.star_3_2 (p ⊃ₚ (q ⊃ₚ (p ≡ₚ q))) (p ⊃ₚ ((p ≡ₚ q) ⊃ₚ q)))
  have lift := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 p p (q ⊃ₚ (p ≡ₚ q)) ((p ≡ₚ q) ⊃ₚ q))
  have dup := infer (PM.FirstEdition.Volume1.Star3.star_3_2 p p) (PM.FirstEdition.Volume1.Star2.star_2_43 p (p ∧ₚ p))
  exact compose dup lift

end PM.FirstEdition.Volume1.Star5
