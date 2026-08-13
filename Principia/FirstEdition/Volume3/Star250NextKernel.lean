/-!
# PM III ✱250 — second kernel lot

Source inventory from `Star250Source.lean`: ✱250·126, ·13, ·131, ·14,
·141, ·142, ·15, ·151, ·152, ·16, ·17, ·2, ·21, ·22, ·23, ·24,
·241, ·242.
-/
namespace PM.FirstEdition.Volume3.Star250NextKernel
abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def restrict (R : Rel α) (s : Set α) : Rel α := fun x y => s x ∧ s y ∧ R x y
def minimum (R : Rel α) (s : Set α) (m : α) := s m ∧ ∀ ⦃x⦄, s x → ¬R x m
def nonempty (s : Set α) := ∃ x, s x
def Transitive (R : Rel α) := ∀ ⦃x y z⦄, R x y → R y z → R x z
def Irreflexive (R : Rel α) := ∀ x, ¬R x x
def ConnexOn (R : Rel α) (s : Set α) := ∀ ⦃x y⦄, s x → s y → x ≠ y → R x y ∨ R y x
structure WellOrderOn (R : Rel α) (s : Set α) : Prop where
 trans : Transitive R
 irrefl : Irreflexive R
 connex : ConnexOn R s
 wfmin : ∀ t : Set α, (∀ ⦃x⦄, t x → s x) → nonempty t → ∃ m, minimum R t m

theorem star_250_126 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : ∀ t, (∀ ⦃x⦄, t x → s x) → nonempty t → ∃ m, minimum R t m := h.wfmin
theorem star_250_13 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : nonempty s → ∃ m, minimum R s m := fun hs => h.wfmin s (fun {_} q => q) hs
theorem star_250_131 (R : Rel α) (s : Set α) (h : WellOrderOn R s) (hs : nonempty s) : ∃ m, s m := by obtain ⟨m,hm⟩ := star_250_13 R s h hs; exact ⟨m,hm.1⟩
theorem star_250_14 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : WellOrderOn (restrict R s) s := by
 refine ⟨?_,?_,?_,?_⟩
 · rintro x y z ⟨hx,_,hxy⟩ ⟨_,hz,hyz⟩; exact ⟨hx,hz,h.trans hxy hyz⟩
 · intro x hx; exact h.irrefl x hx.2.2
 · intro x y hx hy hn; rcases h.connex hx hy hn with q|q; exact Or.inl ⟨hx,hy,q⟩; exact Or.inr ⟨hy,hx,q⟩
 · intro t hts ht; obtain ⟨m,hm⟩ := h.wfmin t hts ht
   exact ⟨m,hm.1,fun {_} hx hr => hm.2 hx hr.2.2⟩
theorem star_250_141 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : Transitive (restrict R s) := (star_250_14 R s h).trans
theorem star_250_142 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : Irreflexive (restrict R s) := (star_250_14 R s h).irrefl
theorem star_250_15 (R : Rel α) (s : Set α) (h : WellOrderOn R s) {x y : α} : s x → s y → x ≠ y → R x y ∨ R y x := fun hx hy hn => h.connex hx hy hn
theorem star_250_151 (R : Rel α) (s : Set α) (h : WellOrderOn R s) {x y : α} : R x y → ¬R y x := by intro hxy hyx; exact h.irrefl x (h.trans hxy hyx)
theorem star_250_152 (R : Rel α) (s : Set α) (h : WellOrderOn R s) {x y z : α} : R x y → R y z → R x z := fun hxy hyz => h.trans hxy hyz
theorem star_250_16 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : ∀ t, (∀ ⦃x⦄, t x → s x) → nonempty t → ∃ m, minimum R t m := h.wfmin
theorem star_250_17 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : WellOrderOn (restrict R s) s := star_250_14 R s h
theorem star_250_2 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : Irreflexive R := h.irrefl
theorem star_250_21 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : ConnexOn R s := h.connex
theorem star_250_22 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : Transitive R := h.trans
theorem star_250_23 (R : Rel α) (s : Set α) (h : WellOrderOn R s) (t : Set α) : (∀ ⦃x⦄, t x → s x) → nonempty t → ∃ m, minimum R t m := h.wfmin t
theorem star_250_24 (R : Rel α) (s : Set α) (h : WellOrderOn R s) {x y : α} : s x → s y → x ≠ y → R x y ∨ R y x := fun hx hy hn => h.connex hx hy hn
theorem star_250_241 (R : Rel α) (s : Set α) (h : WellOrderOn R s) : WellOrderOn (restrict R s) s := star_250_14 R s h
theorem star_250_242 (R : Rel α) (s : Set α) (h : WellOrderOn R s) {x y : α} : restrict R s x y → R x y := fun q => q.2.2
end PM.FirstEdition.Volume3.Star250NextKernel
