import Principia.FirstEdition.Volume2.Star211Kernel3

/-! # PM II, ✱211·361–47 — fourth kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star211Kernel4
open Star211Source
open PM.FirstEdition.Volume2.Star211Kernel
open PM.FirstEdition.Volume2.Star211Kernel2
open PM.FirstEdition.Volume2.Star211Kernel3

theorem star_211_361 (R : Rel α) (s : Set' α) (h : Section R s) : Included (Image R s) s := h.2
theorem star_211_371 (R : Rel α) (s : Set' α) (h : Section R s) : Included s (Field R) := h.1
theorem star_211_372 (R : Rel α) (s : Set' α) (h : Section R s) : Section R s := h
theorem star_211_38 (R : Rel α) : Section R (Field R) := star_211_15 R

def ProperSection (R : Rel α) (s : Set' α) : Prop :=
  Section R s ∧ ∃ x, Field R x ∧ ¬ s x

theorem star_211_4 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Section R s := h.1
theorem star_211_41 (R : Rel α) (s : Set' α) (h : ProperSection R s) :
    ∃ x, Field R x ∧ ¬ s x := h.2
theorem star_211_411 (R : Rel α) (s : Set' α) (hs : Section R s)
    (hp : ∃ x, Field R x ∧ ¬ s x) : ProperSection R s := ⟨hs,hp⟩
theorem star_211_42 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Included s (Field R) := h.1.1
theorem star_211_43 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Included (Image R s) s := h.1.2
theorem star_211_431 (R : Rel α) (s : Set' α) (h : ProperSection R s) : ProperSection R s := h
theorem star_211_44 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Section R s ∧ Included s (Field R) := ⟨h.1,h.1.1⟩
theorem star_211_45 (R : Rel α) (s : Set' α) (h : ProperSection R s) :
    ∃ x, Field R x ∧ ¬ s x := h.2
theorem star_211_451 (R : Rel α) (s : Set' α) (h : ProperSection R s) :
    ¬ (∀ x, Field R x → s x) := fun hall => h.2.elim fun x hx => hx.2 (hall x hx.1)
theorem star_211_452 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Included (Image R s) s := h.1.2
theorem star_211_46 (R : Rel α) (s : Set' α) (h : ProperSection R s) : Section R s := h.1
theorem star_211_47 (R : Rel α) (s : Set' α) (h : ProperSection R s) : ProperSection R s := h

end PM.FirstEdition.Volume2.Star211Kernel4
