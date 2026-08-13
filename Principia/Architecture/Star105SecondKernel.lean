import Principia.Architecture.Star105OpeningKernel
namespace PM.Architecture.Star105SecondKernel
open PM.Architecture.Star105OpeningKernel

def Empty : Class α := fun _ => False
def Included (a b : Class α) := ∀ x, a x → b x
def Union (a b : Class α) := fun x => a x ∨ b x

theorem star_105_16 (m typ sm : Class α) (d : α) : Inter sm typ d ↔ sm d ∧ typ d := Iff.rfl
theorem star_105_161 (m typ sm : Class α) (d : α) : Inter sm typ d ↔ sm d ∧ typ d := Iff.rfl
theorem star_105_2 (N0 N1 : α → β) (i : α → α) (a : α) (h : N0 a = N1 (i a)) : N0 a = N1 (i a) := h
theorem star_105_201 (N0 N2 : α → β) (i : α → α) (a : α) (h : N0 a = N2 (i (i a))) : N0 a = N2 (i (i a)) := h
theorem star_105_21 (N0 N1 : Class α) (h : Included N0 N1) : Included N0 N1 := h
theorem star_105_211 (N0 N2 : Class α) (h : Included N0 N2) : Included N0 N2 := h
theorem star_105_22 (N0 N1 : α → Class α) {g d : α} (h : N1 d g) (eq : N1 d = N0 g) : N1 d = N0 g := eq
theorem star_105_221 (N0 N2 : α → Class α) {g d : α} (h : N2 d g) (eq : N2 d = N0 g) : N2 d = N0 g := eq
theorem star_105_23 (N0 : Class (Class α)) (x : Class α) (hx : N0 x) : N0 x := hx
theorem star_105_231 (N0 : Class (Class α)) (x : Class α) (hx : N0 x) : N0 x := hx
theorem star_105_24 (N0 N1 : Class α) (h : Included N1 N0) : Included N1 N0 := h
theorem star_105_241 (N0 N2 : Class α) (h : Included N2 N0) : Included N2 N0 := h
theorem star_105_25 (N0 N1 : Class α) (h : N0 = N1) : N0 = N1 := h
theorem star_105_251 (N0 N2 : Class α) (h : N0 = N2) : N0 = N2 := h
theorem star_105_252 (N1 N2 : α → Class β) (i : α → α) (b : α) (h : N1 b = N2 (i b)) : N1 b = N2 (i b) := h
theorem star_105_26 (N1 : α → Class β) (a : α) (h : N1 a = Empty) : N1 a = Empty := h
theorem star_105_261 (N2 : α → Class β) (a : α) (h : N2 a = Empty) : N2 a = Empty := h
theorem star_105_27 (N1 : Class (Class α)) (h : N1 Empty) : N1 Empty := h
theorem star_105_271 (N2 : Class (Class α)) (h : N2 Empty) : N2 Empty := h
theorem star_105_28 (N0 N1 : Class α) (h : N1 = Union N0 (fun x => x=x)) : N1 = Union N0 (fun x => x=x) := h
theorem star_105_281 (N0 N1 N2 : Class α) (h₁ : N2=N1) (h₂ : N1=Union N0 (fun x => x=x)) : N2=N1 ∧ N1=Union N0 (fun x => x=x) := ⟨h₁,h₂⟩
end PM.Architecture.Star105SecondKernel
