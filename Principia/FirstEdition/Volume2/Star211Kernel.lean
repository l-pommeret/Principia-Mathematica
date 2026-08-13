import Principia.FirstEdition.Volume2.Star211Source

/-! # PM II, ✱211·1–14 — first exact kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star211Kernel
open Star211Source

theorem star_211_1 (R : Rel α) (s : Set' α) : Section R s ↔
    Included s (Field R) ∧ Included (Image R s) s := Iff.rfl

theorem star_211_11 (R : Rel α) (s : Set' α) (h : Section R s) : Included s (Field R) := h.1
theorem star_211_12 (R : Rel α) (s : Set' α) (h : Section R s) : Included (Image R s) s := h.2

theorem star_211_13 (R : Rel α) (s : Set' α) (hfield : Included s (Field R))
    (hclosed : Included (Image R s) s) : Section R s := ⟨hfield,hclosed⟩

theorem star_211_131 (R : Rel α) (s : Set' α) (h : Section R s) {x y : α}
    (hx : s x) (hxy : R x y) : s y := h.2 y ⟨x,hx,hxy⟩

theorem star_211_132 (R : Rel α) (s : Set' α) (h : Section R s) {x : α}
    (hx : s x) : Field R x := h.1 x hx

theorem star_211_133 (R : Rel α) (s : Set' α) (h : Section R s) :
    ∀ y, Image R s y → s y := h.2

theorem star_211_134 (R : Rel α) (s : Set' α) :
    Section R s → Included s (Field R) := fun h => h.1

theorem star_211_14 (R : Rel α) (s : Set' α) :
    Section R s → Included (Image R s) s := fun h => h.2

theorem star_211_141 (R : Rel α) (s t : Set' α)
    (hs : Section R s) (ht : Included t s)
    (hfield : Included t (Field R))
    (hclosed : Included (Image R t) t) : Section R t := ⟨hfield,hclosed⟩

theorem star_211_15 (R : Rel α) : Section R (Field R) := by
  refine ⟨fun _ h => h,?_⟩
  rintro y ⟨x,hx,hxy⟩; exact Or.inr ⟨x,hxy⟩

theorem star_211_151 (R : Rel α) : Included (Image R (Field R)) (Field R) :=
  (star_211_15 R).2

theorem star_211_16 (R : Rel α) : Section R (fun _ => False) := by
  exact ⟨fun _ h => False.elim h,fun _ h => h.elim fun _ p => False.elim p.1⟩

theorem star_211_17 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∧ t x) := by
  constructor
  · intro x hx; exact hs.1 x hx.1
  · rintro y ⟨x,⟨hxs,hxt⟩,hxy⟩
    exact ⟨hs.2 y ⟨x,hxs,hxy⟩,ht.2 y ⟨x,hxt,hxy⟩⟩

theorem star_211_18 (R : Rel α) (s t : Set' α) (hs : Section R s) (ht : Section R t) :
    Section R (fun x => s x ∨ t x) := by
  constructor
  · rintro x (hx|hx); exact hs.1 x hx; exact ht.1 x hx
  · rintro y ⟨x,hx,hxy⟩
    rcases hx with hx|hx
    · exact Or.inl (hs.2 y ⟨x,hx,hxy⟩)
    · exact Or.inr (ht.2 y ⟨x,hx,hxy⟩)

end PM.FirstEdition.Volume2.Star211Kernel
