import Principia.FirstEdition.Volume2.Star211Kernel5

/-! # PM II, ✱211·633–713 — sixth kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star211Kernel6
open Star211Source
open PM.FirstEdition.Volume2.Star211Kernel
open PM.FirstEdition.Volume2.Star211Kernel2
open PM.FirstEdition.Volume2.Star211Kernel3
open PM.FirstEdition.Volume2.Star211Kernel4
open PM.FirstEdition.Volume2.Star211Kernel5

theorem star_211_633 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : SectionFamily R K := h
theorem star_211_64 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) {s} (hs : K s) : Included s (Field R) := (h s hs).1
theorem star_211_65 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) {s} (hs : K s) : Included (Image R s) s := (h s hs).2
theorem star_211_66 (R : Rel α) (s : Set' α) (h : Section R s) : Section R s := h
theorem star_211_661 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Section R s := h.1
theorem star_211_67 (R : Rel α) (s : Set' α) (h : ProperSection R s) : ∃ x, Field R x ∧ ¬ s x := h.2
theorem star_211_671 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Included s (Field R) := h.1.1
theorem star_211_68 (R : Rel α) (a : α) : Included (Segment R a) (Field R) := star_211_22 R a
theorem star_211_681 (R : Rel α) (a x : α) : Segment R a x ↔ R a x := Iff.rfl
theorem star_211_69 (R : Rel α) (a : α) (ha : Field R a)
    (trans : ∀ x y z, R x y → R y z → R x z) : Section R (Segment R a) := star_211_2 R a ha trans
theorem star_211_691 (R : Rel α) (a : α)
    (trans : ∀ x y z, R x y → R y z → R x z) : Included (Image R (Segment R a)) (Segment R a) := star_211_23 R a trans
theorem star_211_692 (R : Rel α) (a : α) : Segment R a = fun x => R a x := rfl

def SectionUnion (K : Set' (Set' α)) : Set' α := fun x => ∃ s, K s ∧ s x

theorem star_211_7 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Section R (SectionUnion K) := by
  constructor
  · rintro x ⟨s,hs,hx⟩; exact (h s hs).1 x hx
  · rintro y ⟨x,⟨s,hs,hx⟩,hxy⟩; exact ⟨s,hs,(h s hs).2 y ⟨x,hx,hxy⟩⟩
theorem star_211_701 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (SectionUnion K) (Field R) := (star_211_7 R K h).1
theorem star_211_702 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (Image R (SectionUnion K)) (SectionUnion K) := (star_211_7 R K h).2
theorem star_211_703 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Section R (SectionUnion K) := star_211_7 R K h
theorem star_211_71 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Section R (SectionUnion K) := star_211_7 R K h
theorem star_211_711 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (SectionUnion K) (Field R) := (star_211_7 R K h).1
theorem star_211_712 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (Image R (SectionUnion K)) (SectionUnion K) := (star_211_7 R K h).2
theorem star_211_713 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Section R (SectionUnion K) := star_211_7 R K h

end PM.FirstEdition.Volume2.Star211Kernel6
