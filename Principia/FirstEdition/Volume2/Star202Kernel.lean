import Principia.FirstEdition.Volume2.Star202Source

/-! # PM II, ✱202·1–14 — first exact kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star202Kernel
open Star202Source

theorem star_202_1 (R : Rel α) : Connected R ↔
    ∀ x, Field R x → ∀ y, Field R y → x ≠ y → R x y ∨ R y x := Iff.rfl

theorem star_202_101 (R : Rel α) (h : Connected R) {x y : α}
    (hx : Field R x) (hy : Field R y) (hne : x ≠ y) : R x y ∨ R y x :=
  h x hx y hy hne

theorem star_202_102 (R : Rel α) (h : Connected R) : Connected (Converse R) := by
  intro x hx y hy hne
  have hxR : Field R x := by
    rcases hx with ⟨z,hzx⟩|⟨z,hxz⟩
    · exact Or.inr ⟨z,hzx⟩
    · exact Or.inl ⟨z,hxz⟩
  have hyR : Field R y := by
    rcases hy with ⟨z,hzy⟩|⟨z,hyz⟩
    · exact Or.inr ⟨z,hzy⟩
    · exact Or.inl ⟨z,hyz⟩
  rcases h x hxR y hyR hne with a|b
  · exact Or.inr a
  · exact Or.inl b

theorem star_202_104 [DecidableEq α] (R : Rel α) (h : Connected R) {x y : α}
    (hx : Field R x) (hy : Field R y) : x = y ∨ R x y ∨ R y x := by
  by_cases e : x = y
  · exact Or.inl e
  · exact Or.inr (h x hx y hy e)

theorem star_202_11 (R : Rel α) (h : Connected R) :
    ∀ x y, Field R x → Field R y → x ≠ y → R x y ∨ R y x := by
  intro x y hx hy hn; exact h x hx y hy hn

theorem star_202_12 (R : Rel α) (h : Connected R) :
    Connected (Union R (Converse R)) := by
  intro x hx y hy hne
  have hxR : Field R x := by
    rcases hx with ⟨z,a|a⟩|⟨z,a|a⟩
    · exact Or.inl ⟨z,a⟩
    · exact Or.inr ⟨z,a⟩
    · exact Or.inr ⟨z,a⟩
    · exact Or.inl ⟨z,a⟩
  have hyR : Field R y := by
    rcases hy with ⟨z,a|a⟩|⟨z,a|a⟩
    · exact Or.inl ⟨z,a⟩
    · exact Or.inr ⟨z,a⟩
    · exact Or.inr ⟨z,a⟩
    · exact Or.inl ⟨z,a⟩
  rcases h x hxR y hyR hne with a|b
  · exact Or.inl (Or.inl a)
  · exact Or.inl (Or.inr b)

theorem star_202_13 (R : Rel α) (h : Connected R) (hs : Symmetric R)
    {x y : α} (hx : Field R x) (hy : Field R y) (hne : x ≠ y) :
    R x y ∧ R y x := by
  rcases h x hx y hy hne with a|b
  · exact ⟨a,hs x y a⟩
  · exact ⟨hs y x b,b⟩

theorem star_202_131 (R : Rel α) (h : Connected R) (ha : Asymmetric R)
    {x y : α} (hx : Field R x) (hy : Field R y) (hne : x ≠ y) :
    (R x y ∨ R y x) ∧ ¬ (R x y ∧ R y x) := by
  exact ⟨h x hx y hy hne, fun p => ha x y p.1 p.2⟩

theorem star_202_132 (R : Rel α) (h : Connected R) {x y : α}
    (hx : Field R x) (hy : Field R y) (hne : x ≠ y) :
    R x y ∨ Converse R x y := h x hx y hy hne

theorem star_202_133 (R : Rel α) (h : Connected R) :
    Included R (Union R (Converse R)) := fun _ _ a => Or.inl a

theorem star_202_134 (R : Rel α) (h : Connected R) :
    Included (Converse R) (Union R (Converse R)) := fun _ _ a => Or.inr a

theorem star_202_135 (R : Rel α) (h : Connected R) :
    Connected R ∧ Connected (Converse R) := ⟨h,star_202_102 R h⟩

theorem star_202_14 (R : Rel α) (h : Connected R) : Connected R := h

end PM.FirstEdition.Volume2.Star202Kernel
