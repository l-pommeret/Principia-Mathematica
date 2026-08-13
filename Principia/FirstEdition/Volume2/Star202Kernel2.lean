import Principia.FirstEdition.Volume2.Star202Kernel

/-! # PM II, ✱202·15–31 — second kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star202Kernel2
open Star202Source
open PM.FirstEdition.Volume2.Star202Kernel

theorem star_202_15 (R : Rel α) (h : Connected R) : Connected R := h
theorem star_202_16 (R : Rel α) (h : Connected R) : Connected (Converse R) := star_202_102 R h
theorem star_202_161 (R : Rel α) (h : Connected (Converse R)) : Connected R :=
  (star_202_103 R).mpr h
theorem star_202_162 (R : Rel α) : Connected R ↔ Connected (Converse R) := star_202_103 R

theorem star_202_17 (R S : Rel α) (hR : Connected R) (h : Included R S)
    (fields : ∀ x, Field S x → Field R x) : Connected S := by
  intro x hx y hy hn
  rcases hR x (fields x hx) y (fields y hy) hn with a|b
  · exact Or.inl (h x y a)
  · exact Or.inr (h y x b)

theorem star_202_171 (R S : Rel α) (hR : Connected R) (h : Included R S)
    (fields : ∀ x, Field S x → Field R x) : Connected S := star_202_17 R S hR h fields

theorem star_202_172 (R S : Rel α) (hR : Connected R) (h : Included R S)
    (fields : ∀ x, Field S x → Field R x) : Connected (Converse S) :=
  star_202_102 S (star_202_17 R S hR h fields)

theorem star_202_18 (R : Rel α) (h : Connected R) :
    Connected (Union R (Converse R)) := star_202_12 R h
theorem star_202_181 (R : Rel α) (h : Connected R) :
    Included R (Union R (Converse R)) := fun _ _ a => Or.inl a

def Comparable (R : Rel α) (x y : α) : Prop := x = y ∨ R x y ∨ R y x

theorem star_202_21 (R : Rel α) (h : Connected R) {x y : α}
    (hx : Field R x) (hy : Field R y) : Comparable R x y := star_202_104 R h hx hy

theorem star_202_211 (R : Rel α) (h : Connected R) {x y : α}
    (hx : Field R x) (hy : Field R y) (hn : x ≠ y) : R x y ∨ R y x := h x hx y hy hn

theorem star_202_212 (R : Rel α) (h : Connected R) (ha : Asymmetric R) {x y : α}
    (hx : Field R x) (hy : Field R y) (hn : x ≠ y) :
    (R x y ∨ R y x) ∧ ¬ (R x y ∧ R y x) := star_202_131 R h ha hx hy hn

theorem star_202_22 (R : Rel α) (h : Connected R) :
    ∀ x, Field R x → Comparable R x x := fun x _ => Or.inl rfl

def ReflexiveOnField (R : Rel α) : Prop := ∀ x, Field R x → R x x

theorem star_202_3 (R : Rel α) (h : Connected R) (hr : ReflexiveOnField R) :
    ∀ x y, Field R x → Field R y → R x y ∨ R y x := by
  intro x y hx hy
  by_cases e : x = y
  · subst y; exact Or.inl (hr x hx)
  · exact h x hx y hy e

theorem star_202_31 (R : Rel α) (h : Connected R) (hr : ReflexiveOnField R) :
    ∀ x, Field R x → R x x := hr

end PM.FirstEdition.Volume2.Star202Kernel2
