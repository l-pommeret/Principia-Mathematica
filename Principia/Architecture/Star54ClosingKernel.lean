import Principia.Architecture.Star54MiddleKernel

namespace PM.Architecture.Star54ClosingKernel
open PM.Architecture.Star54OpeningKernel PM.Architecture.Star54MiddleKernel

/-! The remaining propositions of ✱54.  `Pair x y` represents `ιʻx ∪ ιʻy`. -/

theorem star_54_443 (x y z w : Object) (hxy : x ≠ y) (hzw : z ≠ w)
    (hz : Pair x y z) (hw : Pair x y w) :
    (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · exact (hzw rfl).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (hzw rfl).elim

theorem star_54_45 (x y : Object) (phi : Object → Object → Prop) :
    (∀ z w, Pair x y z → Pair x y w → phi z w) ↔
      phi x x ∧ phi x y ∧ phi y x ∧ phi y y := by
  constructor
  · intro h
    exact ⟨h x x (Or.inl rfl) (Or.inl rfl), h x y (Or.inl rfl) (Or.inr rfl),
      h y x (Or.inr rfl) (Or.inl rfl), h y y (Or.inr rfl) (Or.inr rfl)⟩
  · rintro ⟨hxx, hxy, hyx, hyy⟩ z w (rfl | rfl) (rfl | rfl) <;> assumption

theorem star_54_451 (x y : Object) (phi : Object → Object → Prop)
    (hxx : phi x x) (hyy : phi y y) (hcross : phi x y ↔ phi y x) :
    (∀ z w, Pair x y z → Pair x y w → phi z w) ↔ phi x y ∨ phi y x := by
  rw [star_54_45]
  constructor
  · exact fun h => Or.inl h.2.1
  · intro h
    have hxy : phi x y := h.elim id hcross.mpr
    exact ⟨hxx, hxy, hcross.mp hxy, hyy⟩

theorem star_54_452 (x y : Object) (phi : Object → Object → Prop)
    (hxx : phi x x) (hyy : phi y y) (hcross : phi x y ↔ phi y x) :
    (∀ z w, Pair x y z → Pair x y w → phi z w) ↔ phi x y := by
  rw [star_54_451 x y phi hxx hyy hcross]
  exact ⟨fun h => h.elim id hcross.mpr, Or.inl⟩

theorem star_54_46 (x y : Object) :
    ∀ z w, Pair x y z → Pair x y w → z ≠ w → x ≠ y := by
  intro z w hz hw hzw hxy
  subst y
  rcases hz with hz | hz <;> rcases hw with hw | hw
  all_goals exact hzw (hz.trans hw.symm)

theorem star_54_5 (a : Class Object) (z w : Object) :
    Two a → (Included a (Pair z w) ↔ a = Pair z w) := by
  rintro ⟨x, y, hxy, rfl⟩
  constructor
  · intro h
    have hx := h x (Or.inl rfl)
    have hy := h y (Or.inr rfl)
    rcases hx with hxz | hxw <;> rcases hy with hyz | hyw
    · exact (hxy (hxz.trans hyz.symm)).elim
    · subst x; subst y; rfl
    · subst x; subst y
      apply class_ext; intro q; exact or_comm
    · exact (hxy (hxw.trans hyw.symm)).elim
  · intro heq q hq
    rw [← heq]
    exact hq

theorem star_54_51 (a b : Class Object) :
    Two a → (One b ∨ Two b) → (Included a b ↔ a = b) := by
  intro ha hb
  constructor
  · intro hab
    rcases hb with ⟨z, rfl⟩ | ⟨z, w, hzw, rfl⟩
    · rcases ha with ⟨x, y, hxy, rfl⟩
      have hx := hab x (Or.inl rfl)
      have hy := hab y (Or.inr rfl)
      exact (hxy (hx.trans hy.symm)).elim
    · exact (star_54_5 a z w ha).mp hab
  · rintro rfl
    exact fun _ => id

theorem star_54_52 (a b : Class Object) : Two a → Two b →
    (Included a b ↔ a = b) ∧ (a = b ↔ Included b a) := by
  intro ha hb
  exact ⟨star_54_51 a b ha (Or.inr hb),
    ⟨fun h => h ▸ fun _ => id, fun h => (star_54_51 b a hb (Or.inr ha)).mp h |>.symm⟩⟩

theorem star_54_53 (a : Class Object) (z y : Object) :
    Two a → a z → a y → z ≠ y → a = Pair z y := by
  intro ha hz hy hzy
  rcases ha with ⟨x, w, hxw, ha⟩
  rw [ha] at hz hy ⊢
  rcases star_54_44 x w z y hzy hz hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · apply class_ext; intro q; exact or_comm

theorem star_54_531 (a : Class Object) :
    Two a → ∀ z y, a z → a y → z ≠ y → a = Pair z y := by
  rintro ⟨x, w, hxw, rfl⟩ z y hz hy hzy
  rcases star_54_44 x w z y hzy hz hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · apply class_ext; intro q; exact or_comm

theorem star_54_54 (a : Class Object) :
    Two a → ∃ x y, a x ∧ a y ∧ x ≠ y ∧ a = Pair x y := by
  rintro ⟨x, y, hxy, rfl⟩
  exact ⟨x, y, Or.inl rfl, Or.inr rfl, hxy, rfl⟩

theorem star_54_55 (a : Class Object) :
    (Zero a ∨ One a ∨ Two a) ↔ Two a ∨ Zero a ∨ One a := by
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · rintro (h | h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem star_54_56 (a : Class Object) :
    ¬ (Zero a ∨ One a ∨ Two a) ↔
      ∃ x y z, a x ∧ a y ∧ a z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  constructor
  · intro h
    have hn0 : ¬ Zero a := fun ha => h (Or.inl ha)
    have hx : ∃ x, a x := by
      apply Classical.byContradiction
      intro hn
      apply hn0
      apply class_ext; intro q
      exact ⟨fun haq => (hn ⟨q, haq⟩).elim, False.elim⟩
    obtain ⟨x, hx⟩ := hx
    have hy : ∃ y, a y ∧ y ≠ x := by
      apply Classical.byContradiction
      intro hn
      apply h (Or.inr (Or.inl ⟨x, ?_⟩))
      apply class_ext; intro q
      constructor
      · intro hq
        have hqx : q = x := Classical.byContradiction (fun hne => hn ⟨q, hq, hne⟩)
        exact hqx
      · intro hqx; exact hqx ▸ hx
    obtain ⟨y, hy, hyx⟩ := hy
    have hz : ∃ z, a z ∧ z ≠ x ∧ z ≠ y := by
      apply Classical.byContradiction
      intro hn
      apply h (Or.inr (Or.inr ⟨x, y, fun e => hyx e.symm, ?_⟩))
      apply class_ext; intro q
      constructor
      · intro hq
        by_cases hqx : q = x
        · exact Or.inl hqx
        · by_cases hqy : q = y
          · exact Or.inr hqy
          · exact (hn ⟨q, hq, hqx, hqy⟩).elim
      · rintro (rfl | rfl) <;> assumption
    obtain ⟨z, hz, hzx, hzy⟩ := hz
    exact ⟨x, y, z, hx, hy, hz, hyx.symm, hzx.symm, hzy.symm⟩
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ (h0 | h1 | h2)
    · rw [h0] at hx; exact hx
    · obtain ⟨q, rfl⟩ := h1
      exact hxy (hx.trans hy.symm)
    · obtain ⟨q, r, hqr, ha⟩ := h2
      rw [ha] at hx hy hz
      rcases star_54_44 q r x y hxy hx hy with ⟨hxq, hyr⟩ | ⟨hxr, hyq⟩
      · rcases hz with hzq | hzr
        · exact hxz (hxq.trans hzq.symm)
        · exact hyz (hyr.trans hzr.symm)
      · rcases hz with hzq | hzr
        · exact hyz (hyq.trans hzq.symm)
        · exact hxz (hxr.trans hzr.symm)

theorem star_54_6 (a b : Class Object) (x y z w : Object)
    (hdis : Inter a b = PM.Architecture.Star54OpeningKernel.Empty)
    (hx : a x) (hy : a y) (hz : b z) (hw : b w) :
    Pair x z = Pair y w ↔ x = y ∧ z = w := by
  constructor
  · intro h
    rcases star_54_22 x z y w h with hstraight | hswap
    · exact hstraight
    · rcases hswap with ⟨hxw, hzy⟩
      subst w; subst y
      have : Inter a b x := ⟨hx, hw⟩
      rw [hdis] at this
      exact this.elim
  · rintro ⟨rfl, rfl⟩
    rfl

end PM.Architecture.Star54ClosingKernel
