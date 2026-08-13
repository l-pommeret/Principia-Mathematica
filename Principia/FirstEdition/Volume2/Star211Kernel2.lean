import Principia.FirstEdition.Volume2.Star211Kernel

/-! # PM II, ✱211·181–283 — second kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star211Kernel2
open Star211Source
open PM.FirstEdition.Volume2.Star211Kernel

theorem star_211_181 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∧ t x) := star_211_17 R s t hs ht
theorem star_211_182 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∨ t x) := star_211_18 R s t hs ht

theorem star_211_2 (R : Rel α) (a : α) (ha : Field R a)
    (trans : ∀ x y z, R x y → R y z → R x z) : Section R (Segment R a) := by
  constructor
  · intro x hax; exact Or.inr ⟨a,hax⟩
  · rintro y ⟨x,hax,hxy⟩; exact trans a x y hax hxy

theorem star_211_21 (R : Rel α) (a x : α) : Segment R a x ↔ R a x := Iff.rfl
theorem star_211_22 (R : Rel α) (a : α) : Included (Segment R a) (Field R) :=
  fun x h => Or.inr ⟨a,h⟩
theorem star_211_23 (R : Rel α) (a : α)
    (trans : ∀ x y z, R x y → R y z → R x z) :
    Included (Image R (Segment R a)) (Segment R a) := by
  rintro y ⟨x,hax,hxy⟩; exact trans a x y hax hxy
theorem star_211_24 (R : Rel α) (a : α) (ha : Field R a)
    (trans : ∀ x y z, R x y → R y z → R x z) : Section R (Segment R a) :=
  star_211_2 R a ha trans
theorem star_211_26 (R : Rel α) (a x : α) (h : Segment R a x) : R a x := h
theorem star_211_27 (R : Rel α) (a x : α) (h : R a x) : Segment R a x := h
theorem star_211_271 (R : Rel α) (a : α) : Segment R a = fun x => R a x := rfl
theorem star_211_272 (R : Rel α) (a x : α) : Segment R a x = R a x := rfl

theorem star_211_28 (R : Rel α) (a : α) :
    Included (Segment R a) (Field R) := star_211_22 R a
theorem star_211_281 (R : Rel α) (a : α)
    (trans : ∀ x y z, R x y → R y z → R x z) :
    Included (Image R (Segment R a)) (Segment R a) := star_211_23 R a trans
theorem star_211_282 (R : Rel α) (a : α) (ha : Field R a)
    (trans : ∀ x y z, R x y → R y z → R x z) : Section R (Segment R a) :=
  star_211_2 R a ha trans
theorem star_211_283 (R : Rel α) (a x : α) : Segment R a x ↔ R a x := Iff.rfl

end PM.FirstEdition.Volume2.Star211Kernel2
