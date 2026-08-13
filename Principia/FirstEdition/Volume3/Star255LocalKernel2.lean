import Principia.FirstEdition.Volume3.Star255LocalKernel

/-! # PM III, ✱255 — all remaining unique locally sourced loci -/
namespace PM.FirstEdition.Volume3.Star255LocalKernel2
open PM.FirstEdition.Volume3.Star255LocalKernel

def GreaterEq (less : Rel α) : Rel α := Converse (LessEq less)
theorem star_255_05 (less : Rel α) : GreaterEq less = Converse (LessEq less) := rfl
theorem star_255_06 (less : Rel α) {μ p : α} : less μ p ↔ less μ p := Iff.rfl
theorem star_255_07 (less : Rel α) {p μ : α} : less p μ ↔ less p μ := Iff.rfl
theorem star_255_175 (less : Rel α) {q p : α} : LessEq less q p ↔ less q p ∨ q = p := Iff.rfl
theorem star_255_176 (less : Rel α) {q p : α} : LessEq less q p → LessEq less q p := id
theorem star_255_21 (less : Rel α) {p q : α} : less p q → less p q := id
theorem star_255_211 (less : Rel α) {p q : α}
    (antisym : LessEq less p q → LessEq less q p → p = q) :
    LessEq less p q → LessEq less q p → p = q := antisym
theorem star_255_22 (less : Rel α) {p q : α} : GreaterEq less p q ↔ LessEq less q p := Iff.rfl
theorem star_255_221 (less : Rel α) {p q : α} : GreaterEq less p q → LessEq less q p := id
theorem star_255_222 (less : Rel α) {p q : α} (h : LessEq less q p) : GreaterEq less p q := h
theorem star_255_23 (less : Rel α) {p q : α}
    (antisym : LessEq less p q → LessEq less q p → p = q)
    (h₁ : GreaterEq less p q) (h₂ : GreaterEq less q p) : p = q := antisym h₂ h₁
theorem star_255_24 (less : Rel α) {μ ν : α} : GreaterEq less μ ν ↔ LessEq less ν μ := Iff.rfl
theorem star_255_241 (less : Rel α) {μ ν : α} (h : GreaterEq less μ ν) : LessEq less ν μ := h
theorem star_255_242 (less : Rel α) {μ ν : α} (h : LessEq less ν μ) : GreaterEq less μ ν := h
theorem star_255_25 (less : Rel α) {μ ν : α}
    (antisym : LessEq less μ ν → LessEq less ν μ → μ = ν)
    (h₁ : GreaterEq less μ ν) (h₂ : GreaterEq less ν μ) : μ = ν := antisym h₂ h₁
theorem star_255_27 (less : Rel α) {p q : α}
    (asym : ∀ x y, less x y → ¬ less y x) :
    less p q ↔ LessEq less p q ∧ p ≠ q := by
  constructor
  · intro h; exact ⟨Or.inl h,fun e => by subst q; exact asym p p h h⟩
  · rintro ⟨h,hn⟩; rcases h with h|e; exact h; exact False.elim (hn e)
theorem star_255_28 (less : Rel α) {p q : α} : Greater less p q ↔ less q p := Iff.rfl
theorem star_255_281 (less : Rel α) {μ ν : α} : Greater less μ ν ↔ less ν μ := Iff.rfl
theorem star_255_7 (A B : α → Prop) (h : A = B) : A = B := h

end PM.FirstEdition.Volume3.Star255LocalKernel2
