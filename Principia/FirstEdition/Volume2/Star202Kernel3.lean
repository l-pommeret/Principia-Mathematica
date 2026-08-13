import Principia.FirstEdition.Volume2.Star202Kernel2

/-! # PM II, ✱202·33–504 — third kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star202Kernel3
open Star202Source
open PM.FirstEdition.Volume2.Star202Kernel
open PM.FirstEdition.Volume2.Star202Kernel2

theorem star_202_33 (R : Rel α) (h : Connected R) : Connected R := h
theorem star_202_4 (R : Rel α) (h : Connected R) : Connected R := h
theorem star_202_401 (R : Rel α) (h : Connected R) : Connected (Converse R) := star_202_102 R h
theorem star_202_41 (R : Rel α) (h : Connected R) : Connected R ∧ Connected (Converse R) := ⟨h,star_202_102 R h⟩
theorem star_202_411 (R : Rel α) (h : Connected (Converse R)) : Connected R := (star_202_103 R).mpr h
theorem star_202_412 (R : Rel α) : Connected R ↔ Connected (Converse R) := star_202_103 R
theorem star_202_42 (R : Rel α) (h : Connected R) : Connected (Union R (Converse R)) := star_202_12 R h

def Irreflexive (R : Rel α) : Prop := ∀ x, ¬ R x x
def StrictConnected (R : Rel α) : Prop := Connected R ∧ Irreflexive R

theorem star_202_5 (R : Rel α) (h : StrictConnected R) : Connected R := h.1
theorem star_202_501 (R : Rel α) (h : StrictConnected R) : Irreflexive R := h.2
theorem star_202_502 (R : Rel α) (h : StrictConnected R) {x y : α}
    (hx : Field R x) (hy : Field R y) (hn : x ≠ y) : R x y ∨ R y x := h.1 x hx y hy hn
theorem star_202_503 (R : Rel α) (h : StrictConnected R) {x y : α}
    (hx : Field R x) (hy : Field R y) : Comparable R x y := star_202_104 R h.1 hx hy
theorem star_202_504 (R : Rel α) (h : StrictConnected R) {x y : α}
    (hx : Field R x) (hy : Field R y) (hn : x ≠ y) :
    R x y ∨ R y x := h.1 x hx y hy hn

theorem star_202_505 (R : Rel α) (h : StrictConnected R) : StrictConnected R := h
theorem star_202_51 (R : Rel α) (h : StrictConnected R) : Connected R := h.1
theorem star_202_511 (R : Rel α) (h : StrictConnected R) : Irreflexive R := h.2

end PM.FirstEdition.Volume2.Star202Kernel3
