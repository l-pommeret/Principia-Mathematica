/-! Finite-segment kernel for the final macro-lot of PM II ✱122. -/
namespace PM.Architecture.Star122FinalKernel
abbrev Set (α : Type u) := α → Prop
def segment (n : Nat) : Set Nat := fun k => k ≤ n
def openSegment (n : Nat) : Set Nat := fun k => k < n
def interval (a b : Nat) : Set Nat := fun k => a ≤ k ∧ k ≤ b
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def nonempty (s : Set α) := ∃ x, s x
def maximum (s : Set Nat) (n : Nat) := s n ∧ ∀ ⦃k⦄, s k → k ≤ n
def minimum (s : Set Nat) (n : Nat) := s n ∧ ∀ ⦃k⦄, s k → n ≤ k

theorem star_122_43 (a b : Nat) (h : a ≤ b) : nonempty (interval a b) := ⟨a,Nat.le_refl a,h⟩
theorem star_122_44 (a b : Nat) (h : a ≤ b) : minimum (interval a b) a := ⟨⟨Nat.le_refl a,h⟩,fun {_} hk => hk.1⟩
theorem star_122_441 (a b : Nat) (h : a ≤ b) : maximum (interval a b) b := ⟨⟨h,Nat.le_refl b⟩,fun {_} hk => hk.2⟩
theorem star_122_442 (a b k : Nat) : interval a b k ↔ a ≤ k ∧ k ≤ b := Iff.rfl
theorem star_122_443 (a b : Nat) (h : a ≤ b) : interval a b a ∧ interval a b b := ⟨⟨Nat.le_refl a,h⟩,⟨h,Nat.le_refl b⟩⟩
theorem star_122_444 (a b : Nat) : subset (interval a b) (segment b) := fun {_} h => h.2
theorem star_122_45 (a b k : Nat) (h : interval a b k) : a ≤ k := h.1
theorem star_122_46 (a b k : Nat) (h : interval a b k) : k ≤ b := h.2
theorem star_122_47 (n : Nat) : nonempty (segment n) := ⟨n,Nat.le_refl n⟩
theorem star_122_48 (n : Nat) : subset (openSegment n) (segment n) := fun {_} h => Nat.le_of_lt h
theorem star_122_49 (n : Nat) : maximum (segment n) n := ⟨Nat.le_refl n,fun {_} h => h⟩
theorem star_122_51 (a b : Nat) : a ≤ b ∨ b ≤ a := Nat.le_total a b
theorem star_122_52 (a b : Nat) : a < b ∨ a = b ∨ b < a := by
  rcases Nat.lt_trichotomy a b with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
theorem star_122_53 (a b : Nat) : a ≤ b → ¬b < a := fun h hn => Nat.not_lt_of_ge h hn
theorem star_122_54 (a b : Nat) : a < b → a + 1 ≤ b := fun h => h
theorem star_122_55 (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans
end PM.Architecture.Star122FinalKernel
