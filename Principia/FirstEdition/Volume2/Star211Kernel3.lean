import Principia.FirstEdition.Volume2.Star211Kernel2

/-! # PM II, ✱211·3–36 — third kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star211Kernel3
open Star211Source
open PM.FirstEdition.Volume2.Star211Kernel
open PM.FirstEdition.Volume2.Star211Kernel2

def SectionIncluded (R : Rel α) (s t : Set' α) : Prop :=
  Section R s ∧ Section R t ∧ Included s t

theorem star_211_3 (R : Rel α) (s : Set' α) (h : Section R s) : Section R s := h
theorem star_211_301 (R : Rel α) : Section R (Field R) := star_211_15 R
theorem star_211_302 (R : Rel α) : Section R (fun _ => False) := star_211_16 R
theorem star_211_31 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∧ t x) := star_211_17 R s t hs ht
theorem star_211_311 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∨ t x) := star_211_18 R s t hs ht
theorem star_211_312 (R : Rel α) (s : Set' α) (h : Section R s) : Included s (Field R) := h.1
theorem star_211_313 (R : Rel α) (s : Set' α) (h : Section R s) : Included (Image R s) s := h.2
theorem star_211_314 (R : Rel α) (s t : Set' α) (h : SectionIncluded R s t) : Included s t := h.2.2
theorem star_211_315 (R : Rel α) (s t : Set' α) (h : SectionIncluded R s t) : Section R s := h.1
theorem star_211_316 (R : Rel α) (s t : Set' α) (h : SectionIncluded R s t) : Section R t := h.2.1
theorem star_211_317 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t)
    (hi : Included s t) : SectionIncluded R s t := ⟨hs,ht,hi⟩
theorem star_211_32 (R : Rel α) (s : Set' α) (h : Section R s) : Section R s := h
theorem star_211_321 (R : Rel α) (s : Set' α) (h : Section R s) : Included s (Field R) := h.1
theorem star_211_33 (R : Rel α) (a : α) (ha : Field R a)
    (trans : ∀ x y z, R x y → R y z → R x z) : Section R (Segment R a) := star_211_2 R a ha trans
theorem star_211_34 (R : Rel α) (a x : α) : Segment R a x ↔ R a x := Iff.rfl
theorem star_211_35 (R : Rel α) (a : α) : Included (Segment R a) (Field R) := star_211_22 R a
theorem star_211_351 (R : Rel α) (a : α)
    (trans : ∀ x y z, R x y → R y z → R x z) :
    Included (Image R (Segment R a)) (Segment R a) := star_211_23 R a trans
theorem star_211_36 (R : Rel α) (s : Set' α) (h : Section R s) : Included (Image R s) s := h.2

end PM.FirstEdition.Volume2.Star211Kernel3
