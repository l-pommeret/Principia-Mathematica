import Principia.Architecture.Star53SecondKernel

namespace PM.Architecture.Star53FinalKernel

open PM.Architecture.Star53OpeningKernel
open PM.Architecture.Star53SecondKernel

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x; exact propext (h x)

def relImage (r : α → β → Prop) (a : Class α) : Class β :=
  fun y => ∃ x, a x ∧ r x y

def forwardImage (r : α → β → Prop) (x : α) : Class β := fun y => r x y
structure FunctionalAt (r : α → β → Prop) (x : α) : Type _ where
  choose : β
  choose_spec : r x choose
  unique : ∀ y, r x y → y = choose

/-- PM I ✱53·231. -/
theorem star_53_231 (a : Class α) (y : α) :
    (∀ x, a x → x = y) ↔ a = empty ∨ a = singleton y := by
  constructor
  · intro h
    cases Classical.em (a y) with
    | inl hy =>
        right; apply class_ext; intro x
        exact ⟨fun hx => h x hx, fun hxy => hxy ▸ hy⟩
    | inr hy =>
        left; apply class_ext; intro x
        exact ⟨fun hx => hy ((h x hx) ▸ hx), False.elim⟩
  · intro h x hx
    cases h with
    | inl he => rw [he] at hx; exact False.elim hx
    | inr hs => rw [hs] at hx; exact hx

/-- PM I ✱53·24. -/
theorem star_53_24 (k : Class (Class α)) :
    classSum k = empty ↔ k = empty ∨ k = singleton empty := by
  constructor
  · intro hs
    cases Classical.em (k empty) with
    | inl he =>
        right; apply class_ext; intro a
        constructor
        · intro ha
          apply class_ext; intro x
          exact ⟨fun hx => by have z : classSum k x := ⟨a, ha, hx⟩; rw [hs] at z; exact z,
            False.elim⟩
        · intro ha; cases ha; exact he
    | inr he =>
        left; apply class_ext; intro a
        constructor
        · intro ha
          have hae : a = empty := by
            apply class_ext; intro x
            exact ⟨fun hx => by have z : classSum k x := ⟨a, ha, hx⟩; rw [hs] at z; exact z,
              False.elim⟩
          exact he (hae ▸ ha)
        · exact False.elim
  · intro h
    cases h with
    | inl hk => rw [hk]; apply class_ext; intro x; exact ⟨fun z => z.choose_spec.1, False.elim⟩
    | inr hk => rw [hk]; exact star_53_02 empty

/-- PM I ✱53·25. -/
theorem star_53_25 (k l : Class (Class α)) :
    inter (classSum k) (classSum l) = empty →
      inter k l = empty ∨ inter k l = singleton empty := by
  intro h
  apply (star_53_24 (inter k l)).mp
  apply class_ext
  intro x
  constructor
  · rintro ⟨a, ⟨ha, hb⟩, hx⟩
    have z : inter (classSum k) (classSum l) x := ⟨⟨a, ha, hx⟩, ⟨a, hb, hx⟩⟩
    rw [h] at z; exact z
  · exact False.elim

/-- PM I ✱53·3. -/
theorem star_53_3 (r : α → β → Prop) (x : α) :
    Nonempty (FunctionalAt r x) ↔ unitClasses (forwardImage r x) := by
  constructor
  · rintro ⟨⟨y, hy, hu⟩⟩
    refine ⟨y, ?_⟩
    apply class_ext; intro z
    exact ⟨fun hz => hu z hz, fun hzy => hzy ▸ hy⟩
  · rintro ⟨y, hset⟩
    refine ⟨⟨y, ?_, ?_⟩⟩
    · change forwardImage r x y
      rw [hset]
      rfl
    · intro z hz
      change forwardImage r x z at hz
      rw [hset] at hz
      exact hz

/-- PM I ✱53·301. -/
theorem star_53_301 (r : α → β → Prop) (x : α) :
    relImage r (singleton x) = forwardImage r x := by
  apply class_ext; intro y
  constructor
  · rintro ⟨z, hz, h⟩; cases hz; exact h
  · intro h; exact ⟨x, rfl, h⟩

/-- PM I ✱53·302. -/
theorem star_53_302 (r : α → β → Prop) (x y : α) :
    relImage r (union (singleton x) (singleton y)) =
      union (forwardImage r x) (forwardImage r y) := by
  apply class_ext; intro z
  constructor
  · rintro ⟨w, hw, h⟩
    cases hw with
    | inl hx => cases hx; exact Or.inl h
    | inr hy => cases hy; exact Or.inr h
  · intro h
    cases h with
    | inl hx => exact ⟨x, Or.inl rfl, hx⟩
    | inr hy => exact ⟨y, Or.inr rfl, hy⟩

/-- PM I ✱53·31. -/
theorem star_53_31 (r : α → β → Prop) (x : α) (h : FunctionalAt r x) :
    relImage r (singleton x) = singleton h.choose ∧
      singleton h.choose = forwardImage r x := by
  have hf := (star_53_3 r x).mp ⟨h⟩
  rcases hf with ⟨y, hy⟩
  have hry : r x y := by change forwardImage r x y; rw [hy]; rfl
  have heq : y = h.choose := h.unique y hry
  subst y
  exact ⟨(star_53_301 r x).trans hy, hy.symm⟩

/-- PM I ✱53·32. -/
theorem star_53_32 (r : α → β → Prop) (x y : α)
    (hx : FunctionalAt r x) (hy : FunctionalAt r y) :
    relImage r (union (singleton x) (singleton y)) =
      union (singleton hx.choose) (singleton hy.choose) := by
  rw [star_53_302]
  congr 1
  · exact (star_53_31 r x hx).2.symm
  · exact (star_53_31 r y hy).2.symm

def mapImage (f : α → β) (a : Class α) : Class β := fun y => ∃ x, a x ∧ f x = y

/-- PM I ✱53·33. -/
theorem star_53_33 (k : Class (Class α)) :
    mapImage classSum (singleton k) = singleton (classSum k) := by
  apply class_ext; intro a
  constructor
  · rintro ⟨l, hl, h⟩; cases hl; exact h.symm
  · intro h; exact ⟨k, rfl, h.symm⟩

/-- PM I ✱53·34. -/
theorem star_53_34 (k l : Class (Class α)) :
    mapImage classSum (union (singleton k) (singleton l)) =
      union (singleton (classSum k)) (singleton (classSum l)) := by
  apply class_ext; intro a
  constructor
  · rintro ⟨m, hm, h⟩
    cases hm with
    | inl hk => cases hk; exact Or.inl h.symm
    | inr hl => cases hl; exact Or.inr h.symm
  · intro h
    cases h with
    | inl hk => exact ⟨k, Or.inl rfl, hk.symm⟩
    | inr hl => exact ⟨l, Or.inr rfl, hl.symm⟩

/-- PM I ✱53·35. -/
theorem star_53_35 (k l : Class (Class α)) :
    classSum (mapImage classSum (union (singleton k) (singleton l))) =
      union (classSum k) (classSum l) ∧
    union (classSum k) (classSum l) = classSum (union k l) := by
  constructor
  · rw [star_53_34, star_53_11]
  · apply class_ext; intro x
    constructor
    · intro h
      cases h with
      | inl hk => rcases hk with ⟨a, ha, hx⟩; exact ⟨a, Or.inl ha, hx⟩
      | inr hl => rcases hl with ⟨a, ha, hx⟩; exact ⟨a, Or.inr ha, hx⟩
    · rintro ⟨a, ha, hx⟩
      exact ha.elim (fun hk => Or.inl ⟨a, hk, hx⟩) (fun hl => Or.inr ⟨a, hl, hx⟩)

/-- PM I ✱53·4, the four equivalent singleton descriptions of a unique value. -/
theorem star_53_4 (r : α → β → Prop) (x : α) (y : β) (h : FunctionalAt r x) :
    (y = h.choose ↔ unitClasses (forwardImage r x) ∧ forwardImage r x y) ∧
    (unitClasses (forwardImage r x) ∧ forwardImage r x y ↔
      singleton y = forwardImage r x) ∧
    (singleton y = forwardImage r x ↔ y = h.choose) := by
  have hs := (star_53_31 r x h).2
  constructor
  · constructor
    · intro hy; subst y; exact ⟨(star_53_3 r x).mp ⟨h⟩, h.choose_spec⟩
    · intro hy; exact h.unique y hy.2
  constructor
  · constructor
    · intro hy; apply class_ext; intro z
      exact ⟨fun hz => hz ▸ hy.2,
        fun hz => (h.unique z hz).trans (h.unique y hy.2).symm⟩
    · intro he; exact ⟨(star_53_3 r x).mp ⟨h⟩, by rw [← he]; rfl⟩
  · constructor
    · intro he
      have := he.trans hs.symm
      have hz : singleton y h.choose := by rw [this]; rfl
      exact hz.symm
    · intro hy; subst y; exact hs

/-- PM I ✱53·5: existence of a class is equivalent to being a nonempty class. -/
theorem star_53_5 (a : Class α) : (∃ x, a x) ↔ a ≠ empty := by
  constructor
  · rintro ⟨x, hx⟩ he
    rw [he] at hx
    exact hx
  · intro h
    cases Classical.em (∃ x, a x) with
    | inl hx => exact hx
    | inr hn =>
        exact False.elim (h (by
          apply class_ext; intro x
          exact ⟨fun hx => hn ⟨x, hx⟩, False.elim⟩))

end PM.Architecture.Star53FinalKernel
