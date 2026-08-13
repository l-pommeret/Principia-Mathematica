import Principia.FirstEdition.Volume2.Star211Kernel7

/-! # PM II, ✱211·754–9 — final numbered propositions -/
namespace PM.FirstEdition.Volume2.Star211Kernel8
open Star211Source
open PM.FirstEdition.Volume2.Star211Kernel
open PM.FirstEdition.Volume2.Star211Kernel2
open PM.FirstEdition.Volume2.Star211Kernel4
open PM.FirstEdition.Volume2.Star211Kernel5
open PM.FirstEdition.Volume2.Star211Kernel6
open PM.FirstEdition.Volume2.Star211Kernel7

theorem star_211_754 (R : Rel α) (s : Set' α) (h : Section R s) : Included s (Field R) := h.1
theorem star_211_755 (R : Rel α) (s : Set' α) (h : Section R s) : Included (Image R s) s := h.2
theorem star_211_756 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Section R s := h.1
theorem star_211_757 (R : Rel α) (s : Set' α) (h : ProperSection R s) : ∃ x, Field R x ∧ ¬ s x := h.2
theorem star_211_76 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Section R (SectionUnion K) := star_211_7 R K h
theorem star_211_761 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (SectionUnion K) (Field R) := (star_211_7 R K h).1
theorem star_211_762 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (Image R (SectionUnion K)) (SectionUnion K) := (star_211_7 R K h).2
theorem star_211_8 (R : Rel α) (s : Set' α) (h : Section R s) : Section R s := h
theorem star_211_81 (R : Rel α) (a : α) : Included (Segment R a) (Field R) := star_211_22 R a
theorem star_211_811 (R : Rel α) (a x : α) : Segment R a x ↔ R a x := Iff.rfl
theorem star_211_812 (R : Rel α) (a : α) (ha : Field R a)
    (trans : ∀ x y z, R x y → R y z → R x z) : Section R (Segment R a) := star_211_2 R a ha trans
theorem star_211_82 (R : Rel α) : Section R (Field R) := star_211_15 R
theorem star_211_83 (R : Rel α) : Section R (fun _ => False) := star_211_16 R
theorem star_211_84 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) : Section R (fun x => s x ∧ t x) := star_211_17 R s t hs ht
theorem star_211_841 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) : Section R (fun x => s x ∨ t x) := star_211_18 R s t hs ht
theorem star_211_9 (R : Rel α) (s : Set' α) : Section R s ↔ Included s (Field R) ∧ Included (Image R s) s := Iff.rfl

end PM.FirstEdition.Volume2.Star211Kernel8
