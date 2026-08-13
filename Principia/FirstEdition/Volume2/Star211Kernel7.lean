import Principia.FirstEdition.Volume2.Star211Kernel6

/-! # PM II, ✱211·714–753 — seventh kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star211Kernel7
open Star211Source
open PM.FirstEdition.Volume2.Star211Kernel
open PM.FirstEdition.Volume2.Star211Kernel2
open PM.FirstEdition.Volume2.Star211Kernel3
open PM.FirstEdition.Volume2.Star211Kernel4
open PM.FirstEdition.Volume2.Star211Kernel5
open PM.FirstEdition.Volume2.Star211Kernel6

theorem star_211_714 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Section R (SectionUnion K) := star_211_7 R K h
theorem star_211_715 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (SectionUnion K) (Field R) := (star_211_7 R K h).1

def SectionInter (K : Set' (Set' α)) : Set' α := fun x => ∀ s, K s → s x

theorem star_211_72 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K)
    (hne : ∃ s, K s) : Section R (SectionInter K) := by
  constructor
  · intro x hx; rcases hne with ⟨s,hs⟩; exact (h s hs).1 x (hx s hs)
  · rintro y ⟨x,hx,hxy⟩ s hs; exact (h s hs).2 y ⟨x,hx s hs,hxy⟩
theorem star_211_721 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Included (SectionInter K) (Field R) := (star_211_72 R K h hne).1
theorem star_211_722 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Included (Image R (SectionInter K)) (SectionInter K) := (star_211_72 R K h hne).2
theorem star_211_723 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Section R (SectionInter K) := star_211_72 R K h hne
theorem star_211_724 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Section R (SectionInter K) := star_211_72 R K h hne
theorem star_211_725 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Included (SectionInter K) (Field R) := (star_211_72 R K h hne).1
theorem star_211_726 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Included (Image R (SectionInter K)) (SectionInter K) := (star_211_72 R K h hne).2
theorem star_211_727 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Section R (SectionInter K) := star_211_72 R K h hne
theorem star_211_728 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Section R (SectionInter K) := star_211_72 R K h hne
theorem star_211_729 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) (hne : ∃ s, K s) : Included (SectionInter K) (Field R) := (star_211_72 R K h hne).1
theorem star_211_73 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Section R (SectionUnion K) := star_211_7 R K h
theorem star_211_74 (R : Rel α) (K : Set' (Set' α)) (h : SectionFamily R K) : Included (Image R (SectionUnion K)) (SectionUnion K) := (star_211_7 R K h).2
theorem star_211_75 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) : Section R (fun x => s x ∧ t x) := star_211_17 R s t hs ht
theorem star_211_751 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) : Section R (fun x => s x ∨ t x) := star_211_18 R s t hs ht
theorem star_211_752 (R : Rel α) : Section R (Field R) := star_211_15 R
theorem star_211_753 (R : Rel α) : Section R (fun _ => False) := star_211_16 R

end PM.FirstEdition.Volume2.Star211Kernel7
