import Principia.FirstEdition.Volume2.Star211Kernel4

/-! # PM II, ✱211·5–632 — fifth kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star211Kernel5
open Star211Source
open PM.FirstEdition.Volume2.Star211Kernel
open PM.FirstEdition.Volume2.Star211Kernel2
open PM.FirstEdition.Volume2.Star211Kernel3
open PM.FirstEdition.Volume2.Star211Kernel4

theorem star_211_5 (R : Rel α) (s : Set' α) (h : Section R s) : Section R s := h
theorem star_211_51 (R : Rel α) (s : Set' α) (h : Section R s) : Included s (Field R) := h.1
theorem star_211_52 (R : Rel α) (s : Set' α) (h : Section R s) : Included (Image R s) s := h.2
theorem star_211_53 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∧ t x) := star_211_17 R s t hs ht
theorem star_211_541 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∨ t x) := star_211_18 R s t hs ht
theorem star_211_55 (R : Rel α) : Section R (Field R) := star_211_15 R
theorem star_211_551 (R : Rel α) : Section R (fun _ => False) := star_211_16 R
theorem star_211_552 (R : Rel α) (s : Set' α) (h : Section R s) : Section R s := h
theorem star_211_553 (R : Rel α) (s : Set' α) (h : Section R s) : Included s (Field R) := h.1
theorem star_211_56 (R : Rel α) (s : Set' α) (h : Section R s) : Included (Image R s) s := h.2
theorem star_211_561 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Section R s := h.1
theorem star_211_562 (R : Rel α) (s : Set' α) (h : ProperSection R s) :
    ∃ x, Field R x ∧ ¬ s x := h.2

def SectionFamily (R : Rel α) (K : Set' (Set' α)) : Prop := ∀ s, K s → Section R s

theorem star_211_6 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : SectionFamily R K := h
theorem star_211_61 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) {s} (hs : K s) : Section R s := h s hs
theorem star_211_62 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) :
    ∀ s, K s → Included s (Field R) := fun s hs => (h s hs).1
theorem star_211_63 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) :
    ∀ s, K s → Included (Image R s) s := fun s hs => (h s hs).2
theorem star_211_631 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) {s t}
    (hs : K s) (ht : K t) : Section R (fun x => s x ∧ t x) := star_211_17 R s t (h s hs) (h t ht)
theorem star_211_632 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) {s t}
    (hs : K s) (ht : K t) : Section R (fun x => s x ∨ t x) := star_211_18 R s t (h s hs) (h t ht)

end PM.FirstEdition.Volume2.Star211Kernel5
