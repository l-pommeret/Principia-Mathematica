import Principia.FirstEdition.Volume2.Star202Kernel3

/-! # PM II, ✱202·52–62 — fourth kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star202Kernel4
open Star202Source
open PM.FirstEdition.Volume2.Star202Kernel
open PM.FirstEdition.Volume2.Star202Kernel2
open PM.FirstEdition.Volume2.Star202Kernel3

theorem star_202_52 (R : Rel α) (h : Connected R) : Connected R := h
theorem star_202_521 (R : Rel α) (h : Connected R) : Connected (Converse R) := star_202_102 R h
theorem star_202_524 (R : Rel α) (h : Connected R) : Connected (Union R (Converse R)) := star_202_12 R h
theorem star_202_53 (R : Rel α) (h : Connected R) :
    Included R (Union R (Converse R)) := fun _ _ a => Or.inl a
theorem star_202_54 (R : Rel α) (h : Connected R) :
    Included (Converse R) (Union R (Converse R)) := fun _ _ a => Or.inr a
theorem star_202_541 (R : Rel α) (h : Connected R) :
    Connected R ∧ Connected (Converse R) := ⟨h,star_202_102 R h⟩
theorem star_202_55 [DecidableEq α] (R : Rel α) (h : Connected R) {x y : α}
    (hx : Field R x) (hy : Field R y) : Comparable R x y := star_202_104 R h hx hy
theorem star_202_56 (R : Rel α) (h : Connected R) {x y : α}
    (hx : Field R x) (hy : Field R y) (hn : x ≠ y) : R x y ∨ R y x := h x hx y hy hn

def TotalOnField (R : Rel α) : Prop :=
  ∀ x, Field R x → ∀ y, Field R y → R x y ∨ R y x

theorem star_202_6 (R : Rel α) (h : TotalOnField R) : Connected R := by
  intro x hx y hy _; exact h x hx y hy
theorem star_202_61 [DecidableEq α] (R : Rel α) (h : Connected R) (hr : ReflexiveOnField R) : TotalOnField R :=
  fun x hx y hy => star_202_3 R h hr x y hx hy
theorem star_202_611 (R : Rel α) (h : TotalOnField R) : Connected R := star_202_6 R h
theorem star_202_62 (R : Rel α) (h : TotalOnField R) :
    ∀ x y, Field R x → Field R y → R x y ∨ R y x := by
  intro x y hx hy; exact h x hx y hy

end PM.FirstEdition.Volume2.Star202Kernel4
