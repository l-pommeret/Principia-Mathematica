/-!
# PM III ✱250 — opening kernel (next existing chapter after absent ✱237)

Source: `Star250Source.lean`, canonical first-edition scan transcription.
This covers ✱250·01, ·02, ·1, ·101–·105, ·11, ·111–·113, ·12,
·121–·125 (18 consecutive source items).
-/
namespace PM.FirstEdition.Volume3.Star250OpeningKernel
abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def nonempty (s : Set α) := ∃ x, s x
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def minimum (R : Rel α) (s : Set α) (m : α) := s m ∧ ∀ ⦃x⦄, s x → ¬R x m
def Transitive (R : Rel α) := ∀ ⦃x y z⦄, R x y → R y z → R x z
def Irreflexive (R : Rel α) := ∀ x, ¬R x x
def Connex (R : Rel α) := ∀ ⦃x y⦄, x ≠ y → R x y ∨ R y x
def WellFoundedMin (R : Rel α) := ∀ s : Set α, nonempty s → ∃ m, minimum R s m
structure WellOrder (R : Rel α) : Prop where
 trans : Transitive R
 irrefl : Irreflexive R
 connex : Connex R
 wfmin : WellFoundedMin R

theorem star_250_01 (R : Rel α) : WellFoundedMin R ↔ ∀ s : Set α, nonempty s → ∃ m, minimum R s m := Iff.rfl
theorem star_250_02 (R : Rel α) : WellOrder R ↔ Transitive R ∧ Irreflexive R ∧ Connex R ∧ WellFoundedMin R :=
 ⟨fun h => ⟨h.trans,h.irrefl,h.connex,h.wfmin⟩,fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩⟩
theorem star_250_1 (R : Rel α) (h : WellOrder R) : WellFoundedMin R := h.wfmin
theorem star_250_101 (R : Rel α) (h : WellOrder R) (s : Set α) : nonempty s → ∃ m, minimum R s m := h.wfmin s
theorem star_250_102 (R : Rel α) (h : WellOrder R) (s : Set α) : nonempty s → ∃ m, s m ∧ ∀ ⦃x⦄, s x → ¬R x m := h.wfmin s
theorem star_250_103 (R : Rel α) (h : WellOrder R) : WellFoundedMin R := h.wfmin
theorem star_250_104 (R : Rel α) (h : WellOrder R) : Irreflexive R := h.irrefl
theorem star_250_105 (R : Rel α) (h : WellOrder R) : Transitive R := h.trans
theorem star_250_11 (R : Rel α) (h : WellOrder R) : Connex R := h.connex
theorem star_250_111 (R : Rel α) (h : WellOrder R) {x y : α} : x ≠ y → R x y ∨ R y x := fun hn => h.connex hn
theorem star_250_112 (R : Rel α) (h : WellOrder R) {x y : α} : R x y → ¬R y x := by
 intro hxy hyx; exact h.irrefl x (h.trans hxy hyx)
theorem star_250_113 (R : Rel α) (h : WellOrder R) {x y z : α} : R x y → R y z → R x z := fun hxy hyz => h.trans hxy hyz
theorem star_250_12 (R : Rel α) (h : WellOrder R) (s : Set α) : nonempty s → ∃ m, minimum R s m := h.wfmin s
theorem star_250_121 (R : Rel α) (h : WellOrder R) (s : Set α) (hs : nonempty s) : ∃ m, minimum R s m := h.wfmin s hs
theorem star_250_122 (R : Rel α) (h : WellOrder R) (s : Set α) (hs : nonempty s) : ∃ m, s m := by
 obtain ⟨m,hm⟩ := h.wfmin s hs; exact ⟨m,hm.1⟩
theorem star_250_123 (R : Rel α) (h : WellOrder R) (s : Set α) (hs : nonempty s) : ∃ m, s m ∧ ∀ ⦃x⦄, s x → ¬R x m := h.wfmin s hs
theorem star_250_124 (R : Rel α) (h : WellOrder R) (s : Set α) (hs : nonempty s) : nonempty s := hs
theorem star_250_125 (R : Rel α) (h : WellOrder R) (s : Set α) (hs : nonempty s) : ∃ m, minimum R s m := h.wfmin s hs
end PM.FirstEdition.Volume3.Star250OpeningKernel
