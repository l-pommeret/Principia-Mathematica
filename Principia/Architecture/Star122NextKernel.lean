/-! Natural-index kernel for the second macro-lot of PM II ✱122. -/
namespace PM.Architecture.Star122NextKernel
abbrev Set (α : Type u) := α → Prop
def segment (n : Nat) : Set Nat := fun k => k ≤ n
def openSegment (n : Nat) : Set Nat := fun k => k < n
def tail (n : Nat) : Set Nat := fun k => n ≤ k
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def maximum (s : Set Nat) (n : Nat) := s n ∧ ∀ ⦃k⦄, s k → k ≤ n
def minimum (s : Set Nat) (n : Nat) := s n ∧ ∀ ⦃k⦄, s k → n ≤ k

theorem star_122_24 (n : Nat) : segment n n := Nat.le_refl n
theorem star_122_25 (n k : Nat) : segment n k ↔ k ≤ n := Iff.rfl
theorem star_122_26 (n : Nat) : maximum (segment n) n := ⟨Nat.le_refl n, fun {_} h => h⟩
theorem star_122_27 (n : Nat) : ∃ k, maximum (segment n) k ∧ ∀ y, maximum (segment n) y → y = k := by
  refine ⟨n,star_122_26 n,?_⟩
  intro y hy; exact Nat.le_antisymm hy.1 (hy.2 (Nat.le_refl n))
theorem star_122_28 (n : Nat) {k : Nat} (h : segment n k) : k ≤ n := h
theorem star_122_3 (n : Nat) : tail n n := Nat.le_refl n
theorem star_122_31 (n k : Nat) : tail n k ↔ n ≤ k := Iff.rfl
theorem star_122_32 (n : Nat) : minimum (tail n) n := ⟨Nat.le_refl n, fun {_} h => h⟩
theorem star_122_33 (n : Nat) : ∃ k, minimum (tail n) k ∧ ∀ y, minimum (tail n) y → y = k := by
  refine ⟨n,star_122_32 n,?_⟩
  intro y hy; exact Nat.le_antisymm (hy.2 (Nat.le_refl n)) hy.1
theorem star_122_34 (n k : Nat) : openSegment n k ↔ k < n := Iff.rfl
theorem star_122_341 (n : Nat) : subset (openSegment n) (segment n) := fun {_} h => Nat.le_of_lt h
theorem star_122_35 (n k : Nat) (h : k < n) : k + 1 ≤ n := h
theorem star_122_36 (n : Nat) : n < n + 1 := Nat.lt_succ_self n
theorem star_122_37 (n k : Nat) : k ≤ n ∨ n ≤ k := Nat.le_total k n
theorem star_122_38 (n k : Nat) : k < n ∨ k = n ∨ n < k := by
  rcases Nat.lt_trichotomy k n with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
theorem star_122_381 (n k : Nat) : ¬k < n → n ≤ k := Nat.le_of_not_gt
theorem star_122_41 (n : Nat) : maximum (segment n) n := star_122_26 n
theorem star_122_42 (n : Nat) {k : Nat} (h : segment n k) (hm : maximum (segment n) k) : k = n :=
  Nat.le_antisymm h (hm.2 (Nat.le_refl n))
end PM.Architecture.Star122NextKernel
