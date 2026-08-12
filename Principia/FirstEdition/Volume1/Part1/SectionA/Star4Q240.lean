import Principia.FirstEdition.Volume1.Part1.SectionA.Star4

namespace PM.FirstEdition.Volume1.Star3

open PM
open PM.Elementary

/-- PM I (1910), ✱3·43 (Comp), needed by the printed closure of ✱4·22 and ✱4·39. -/
theorem star_3_43 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ⊃ₚ (p ⊃ₚ (q ∧ₚ r))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  let t1 := infer (star_3_2 q r) (PM.FirstEdition.Volume1.Star2.star_2_05 p q (r ⊃ₚ (q ∧ₚ r)))
  let t2 := PM.FirstEdition.Volume1.Star2.star_2_77 p r (q ∧ₚ r)
  let t12 := infer t2 (infer t1
    (PM.FirstEdition.Volume1.Star2.star_2_06 (p ⊃ₚ q) (p ⊃ₚ (r ⊃ₚ (q ∧ₚ r)))
      ((p ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ∧ₚ r)))))
  exact infer t12 (star_3_31 (p ⊃ₚ q) (p ⊃ₚ r) (p ⊃ₚ (q ∧ₚ r)))

end PM.FirstEdition.Volume1.Star3

namespace PM.FirstEdition.Volume1.Star4

open PM
open PM.Elementary
open PM.FirstEdition.Volume1.Star1 PM.FirstEdition.Volume1.Star2 PM.FirstEdition.Volume1.Star3

/-- PM I (1910), p. 125, ✱4·51.  With conjunction unfolded according to
✱3·01, the target is the reverse of the double-negation equivalence ✱4·13;
✱3·22 exchanges its two implication components. -/
theorem star_4_51 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ (p ∧ₚ q) ≡ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) := by
  let x := (∼ₚ p) ∨ₚ (∼ₚ q)
  exact PM.Derivation.detach (PM.FirstEdition.Volume1.Star4.star_4_13 x)
    (PM.FirstEdition.Volume1.Star3.star_3_22
      (x ⊃ₚ (∼ₚ (∼ₚ x))) ((∼ₚ (∼ₚ x)) ⊃ₚ x))

/-- ✱4·22. `⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ r`.
  [✱3·26 . ✱3·27 . ✱3·2 . ✱3·47 . ✱3·33 . ✱3·22 . ✱2·06 . ✱3·43 . (✱4·01)] -/
theorem star_4_22 (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ≡ₚ q) ∧ₚ (q ≡ₚ r)) ⊃ₚ (p ≡ₚ r)) :=
  let zz := (p ≡ₚ q) ∧ₚ (q ≡ₚ r)
  -- `⊢ : p ≡ q . q ≡ r . ⊃ . p ⊃ q . q ⊃ r`, whence `⊢ : p ≡ q . q ≡ r . ⊃ . p ⊃ r`
  let z1 : ⊢ₚ (zz ⊃ₚ ((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_26 (q ⊃ₚ r) (r ⊃ₚ q)) (PM.Derivation.detach (star_3_26 (p ⊃ₚ q) (q ⊃ₚ p))
        (star_3_2 ((p ≡ₚ q) ⊃ₚ (p ⊃ₚ q)) ((q ≡ₚ r) ⊃ₚ (q ⊃ₚ r)))))
      (star_3_47 (p ≡ₚ q) (q ≡ₚ r) (p ⊃ₚ q) (q ⊃ₚ r))
  let zA : ⊢ₚ (zz ⊃ₚ (p ⊃ₚ r)) :=
    PM.Derivation.detach (star_3_33 p q r) (PM.Derivation.detach z1
      (star_2_06 zz ((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) (p ⊃ₚ r)))
  -- and, by the second halves, `⊢ : p ≡ q . q ≡ r . ⊃ . r ⊃ p`
  let w1 : ⊢ₚ (zz ⊃ₚ ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ q))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_27 (q ⊃ₚ r) (r ⊃ₚ q)) (PM.Derivation.detach (star_3_27 (p ⊃ₚ q) (q ⊃ₚ p))
        (star_3_2 ((p ≡ₚ q) ⊃ₚ (q ⊃ₚ p)) ((q ≡ₚ r) ⊃ₚ (r ⊃ₚ q)))))
      (star_3_47 (p ≡ₚ q) (q ≡ₚ r) (q ⊃ₚ p) (r ⊃ₚ q))
  let w2 : ⊢ₚ (zz ⊃ₚ ((r ⊃ₚ q) ∧ₚ (q ⊃ₚ p))) :=
    PM.Derivation.detach (star_3_22 (q ⊃ₚ p) (r ⊃ₚ q)) (PM.Derivation.detach w1
      (star_2_06 zz ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ q)) ((r ⊃ₚ q) ∧ₚ (q ⊃ₚ p))))
  let zB : ⊢ₚ (zz ⊃ₚ (r ⊃ₚ p)) :=
    PM.Derivation.detach (star_3_33 r q p) (PM.Derivation.detach w2
      (star_2_06 zz ((r ⊃ₚ q) ∧ₚ (q ⊃ₚ p)) (r ⊃ₚ p)))
  PM.Derivation.detach (PM.Derivation.detach zB (PM.Derivation.detach zA (star_3_2 (zz ⊃ₚ (p ⊃ₚ r)) (zz ⊃ₚ (r ⊃ₚ p)))))
    (star_3_43 zz (p ⊃ₚ r) (r ⊃ₚ p))

/-- ✱4·25. `⊢ : p . ≡ . p ∨ p`.  [✱2·07 . ✱1·2 . ✱3·2 . (✱4·01)] -/
theorem star_4_25 (p : PM.Elementary Γ) : ⊢ₚ (p ≡ₚ (p ∨ₚ p)) :=
  PM.Derivation.detach (star_1_2 p) (PM.Derivation.detach (star_2_07 p)
    (star_3_2 (p ⊃ₚ (p ∨ₚ p)) ((p ∨ₚ p) ⊃ₚ p)))

/-- ✱4·31. `⊢ : p ∨ q . ≡ . q ∨ p`.  [✱1·4 . ✱3·2 . (✱4·01)] -/
theorem star_4_31 (p q : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ q) ≡ₚ (q ∨ₚ p)) :=
  PM.Derivation.detach (star_1_4 q p) (PM.Derivation.detach (star_1_4 p q)
    (star_3_2 ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) ((q ∨ₚ p) ⊃ₚ (p ∨ₚ q))))

/-- ✱4·33. `⊢ : (p ∨ q) ∨ r . ≡ . p ∨ (q ∨ r)`.  [✱2·31 . ✱2·32 . ✱3·2 . (✱4·01)] -/
theorem star_4_33 (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ≡ₚ (p ∨ₚ (q ∨ₚ r))) :=
  PM.Derivation.detach (star_2_31 p q r) (PM.Derivation.detach (star_2_32 p q r)
    (star_3_2 (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r))) ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ∨ₚ r))))
/-- ✱4·39. `⊢ :. p ≡ r . q ≡ s . ⊃ : p ∨ q . ≡ . r ∨ s`.
  [✱3·26 . ✱3·27 . ✱3·2 . ✱3·47 . ✱3·48 . ✱2·06 . ✱3·43 . (✱4·01)] -/
theorem star_4_39 (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ≡ₚ r) ∧ₚ (q ≡ₚ s)) ⊃ₚ ((p ∨ₚ q) ≡ₚ (r ∨ₚ s))) :=
  let zz := (p ≡ₚ r) ∧ₚ (q ≡ₚ s)
  let z1 : ⊢ₚ (zz ⊃ₚ ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_26 (q ⊃ₚ s) (s ⊃ₚ q)) (PM.Derivation.detach (star_3_26 (p ⊃ₚ r) (r ⊃ₚ p))
        (star_3_2 ((p ≡ₚ r) ⊃ₚ (p ⊃ₚ r)) ((q ≡ₚ s) ⊃ₚ (q ⊃ₚ s)))))
      (star_3_47 (p ≡ₚ r) (q ≡ₚ s) (p ⊃ₚ r) (q ⊃ₚ s))
  let zA : ⊢ₚ (zz ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))) :=
    PM.Derivation.detach (star_3_48 p q r s) (PM.Derivation.detach z1
      (star_2_06 zz ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))))
  let w1 : ⊢ₚ (zz ⊃ₚ ((r ⊃ₚ p) ∧ₚ (s ⊃ₚ q))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_27 (q ⊃ₚ s) (s ⊃ₚ q)) (PM.Derivation.detach (star_3_27 (p ⊃ₚ r) (r ⊃ₚ p))
        (star_3_2 ((p ≡ₚ r) ⊃ₚ (r ⊃ₚ p)) ((q ≡ₚ s) ⊃ₚ (s ⊃ₚ q)))))
      (star_3_47 (p ≡ₚ r) (q ≡ₚ s) (r ⊃ₚ p) (s ⊃ₚ q))
  let zB : ⊢ₚ (zz ⊃ₚ ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q))) :=
    PM.Derivation.detach (star_3_48 r s p q) (PM.Derivation.detach w1
      (star_2_06 zz ((r ⊃ₚ p) ∧ₚ (s ⊃ₚ q)) ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q))))
  PM.Derivation.detach (PM.Derivation.detach zB (PM.Derivation.detach zA
      (star_3_2 (zz ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))) (zz ⊃ₚ ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q))))))
    (star_3_43 zz ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s)) ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q)))

/-- ✱4·78. `⊢ :. p ⊃ q . ∨ . p ⊃ r : ≡ . p ⊃ q ∨ r`.

Dem.
```
⊢ . ✱4·2 . (✱1·01) . ⊃
⊢ :. p ⊃ q . ∨ . p ⊃ r : ≡ : ∼p ∨ q . ∨ . ∼p ∨ r                      (1)
⊢ . ✱4·33 . ⊃
⊢ :. ∼p ∨ q . ∨ . ∼p ∨ r : ≡ : ∼p ∨ q . ∨ ∼p . ∨ r                   (2)
⊢ . ✱4·31·37 . ⊃
⊢ :. ∼p ∨ q . ∨ ∼p . ∨ r : ≡ : ∼p ∨ (∼p ∨ q) . ∨ r                   (3)
⊢ . ✱4·33 . ⊃
⊢ :. ∼p ∨ (∼p ∨ q) . ∨ r : ≡ : ∼p ∨ ∼p . ∨ . q ∨ r                   (4)
⊢ . ✱4·25·37 . ⊃
⊢ :. ∼p ∨ ∼p . ∨ . q ∨ r : ≡ : ∼p . ∨ . q ∨ r                        (5)
⊢ . ✱4·2 . (✱1·01) . ⊃
⊢ :. ∼p . ∨ . q ∨ r : ≡ . p ⊃ q ∨ r                                  (6)
⊢ . (1) . (2) . (3) . (4) . (5) . (6) . ✱4·22 . ⊃ ⊢ . Prop
```
-/
theorem star_4_78 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ∨ₚ r))) :=
  -- (1) ✱4·2 . (✱1·01)
  let s1 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r))) :=
    star_4_2 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r))
  -- (2) ✱4·33
  let s2 : ⊢ₚ (((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)) :=
    PM.Derivation.detach (star_4_33 (∼ₚp ∨ₚ q) (∼ₚp) r)
      (PM.Derivation.detach (star_4_21 (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r) ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)))
        (star_3_26 _ _))
  -- (3) ✱4·31·37
  let s3 : ⊢ₚ ((((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)) :=
    PM.Derivation.detach (star_4_31 (∼ₚp ∨ₚ q) (∼ₚp))
      (star_4_37 ((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) (∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) r)
  -- (4) ✱4·33, once under ✱4·37 and once at the head
  let s4a : ⊢ₚ (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r)) :=
    PM.Derivation.detach (PM.Derivation.detach (star_4_33 (∼ₚp) (∼ₚp) q)
        (PM.Derivation.detach (star_4_21 ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) (∼ₚp ∨ₚ (∼ₚp ∨ₚ q))) (star_3_26 _ _)))
      (star_4_37 (∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) r)
  let s4b : ⊢ₚ ((((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))) :=
    star_4_33 (∼ₚp ∨ₚ ∼ₚp) q r
  let s4 : ⊢ₚ (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach s4b (PM.Derivation.detach s4a
        (star_3_2 (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r))
          ((((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))))))
      (star_4_22 ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r)
        ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)))
  -- (5) ✱4·25·37
  let s5 : ⊢ₚ (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_4_25 (∼ₚp))
        (PM.Derivation.detach (star_4_21 (∼ₚp) (∼ₚp ∨ₚ ∼ₚp)) (star_3_26 _ _)))
      (star_4_37 (∼ₚp ∨ₚ ∼ₚp) (∼ₚp) (q ∨ₚ r))
  -- (6) ✱4·2 . (✱1·01)
  let s6 : ⊢ₚ ((∼ₚp ∨ₚ (q ∨ₚ r)) ≡ₚ (p ⊃ₚ (q ∨ₚ r))) := star_4_2 (∼ₚp ∨ₚ (q ∨ₚ r))
  -- (1) . (2) . (3) . (4) . (5) . (6) . ✱4·22
  let t12 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)) :=
    PM.Derivation.detach (PM.Derivation.detach s2 (PM.Derivation.detach s1 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)))
        (((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r))
        (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r))
  let t13 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)) :=
    PM.Derivation.detach (PM.Derivation.detach s3 (PM.Derivation.detach t12 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r))
        ((((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)
        ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r))
  let t14 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach s4 (PM.Derivation.detach t13 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r))
        (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)
        ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)))
  let t15 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach s5 (PM.Derivation.detach t14 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)))
        (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r))))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)) (∼ₚp ∨ₚ (q ∨ₚ r)))
  PM.Derivation.detach (PM.Derivation.detach s6 (PM.Derivation.detach t15 (star_3_2
      (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r)))
      ((∼ₚp ∨ₚ (q ∨ₚ r)) ≡ₚ (p ⊃ₚ (q ∨ₚ r))))))
    (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) (∼ₚp ∨ₚ (q ∨ₚ r)) (p ⊃ₚ (q ∨ₚ r)))

/-
Note.  ✱4·78 is a proposition about *propositions*, and its analogue for
classes is false.  Take `p` to be "x is an English person", `q` "x is a man"
and `r` "x is a woman", and read the implications as holding for all values of
`x`, i.e. as inclusions of classes.  Then "all English people are men or women"
is true, while "all English people are men, or all English people are women"
is false, since some English people are men and others are women.  Thus the
equivalence asserted by ✱4·78 fails when `p ⊃ q` is replaced by the inclusion
of the class determined by `q` in the class determined by `p`: the disjunction
of two inclusions is stronger than the single inclusion in the union.  The
same remark applies to ✱4·79.
-/

/-- ✱4·79. `⊢ :. q ⊃ p . ∨ . r ⊃ p : ≡ . q . r . ⊃ p`.

Dem.
```
⊢ . ✱4·1·39 . ⊃
⊢ :. q ⊃ p . ∨ . r ⊃ p : ≡ : ∼p ⊃ ∼q . ∨ . ∼p ⊃ ∼r                   (1)
⊢ . ✱4·78 . ⊃
⊢ :. ∼p ⊃ ∼q . ∨ . ∼p ⊃ ∼r : ≡ : ∼p . ⊃ . ∼q ∨ ∼r                    (2)
⊢ . ✱2·15 . ⊃
⊢ :. ∼p . ⊃ . ∼q ∨ ∼r : ≡ : ∼(∼q ∨ ∼r) . ⊃ p                         (3)
⊢ . ✱4·2 . (✱3·01) . ⊃
⊢ :. ∼(∼q ∨ ∼r) . ⊃ p : ≡ . q . r . ⊃ p                              (4)
⊢ . (1) . (2) . (3) . (4) . ✱4·22 . ⊃ ⊢ . Prop
```
-/
theorem star_4_79 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ ((q ∧ₚ r) ⊃ₚ p)) :=
  -- (1) ✱4·1·39
  let s1 : ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ ((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_4_1 r p) (PM.Derivation.detach (star_4_1 q p)
        (star_3_2 ((q ⊃ₚ p) ≡ₚ (∼ₚp ⊃ₚ ∼ₚq)) ((r ⊃ₚ p) ≡ₚ (∼ₚp ⊃ₚ ∼ₚr)))))
      (star_4_39 (q ⊃ₚ p) (r ⊃ₚ p) (∼ₚp ⊃ₚ ∼ₚq) (∼ₚp ⊃ₚ ∼ₚr))
  -- (2) ✱4·78
  let s2 : ⊢ₚ (((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr))) :=
    star_4_78 (∼ₚp) (∼ₚq) (∼ₚr)
  -- (3) ✱2·15, taken in both directions
  let s3 : ⊢ₚ ((∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)) :=
    PM.Derivation.detach (star_2_15 (∼ₚq ∨ₚ ∼ₚr) p) (PM.Derivation.detach (star_2_15 p (∼ₚq ∨ₚ ∼ₚr))
      (star_3_2 ((∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) ⊃ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p))
        ((∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ⊃ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)))))
  -- (4) ✱4·2 . (✱3·01)
  let s4 : ⊢ₚ ((∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ≡ₚ ((q ∧ₚ r) ⊃ₚ p)) :=
    star_4_2 (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)
  -- (1) . (2) . (3) . (4) . ✱4·22
  let t12 : ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr))) :=
    PM.Derivation.detach (PM.Derivation.detach s2 (PM.Derivation.detach s1 (star_3_2
        (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ ((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr)))
        (((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr))))))
      (star_4_22 ((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr))
        (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)))
  let t13 : ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)) :=
    PM.Derivation.detach (PM.Derivation.detach s3 (PM.Derivation.detach t12 (star_3_2
        (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)))
        ((∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)))))
      (star_4_22 ((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p))
  PM.Derivation.detach (PM.Derivation.detach s4 (PM.Derivation.detach t13 (star_3_2
      (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p))
      ((∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ≡ₚ ((q ∧ₚ r) ⊃ₚ p)))))
    (star_4_22 ((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ((q ∧ₚ r) ⊃ₚ p))

end PM.FirstEdition.Volume1.Star4
