/-! Successor/segment kernel for the end of PM II ✱204. -/
namespace PM.Architecture.Star204FinalKernel
abbrev Set (α : Type u) := α → Prop
def initial (n : Nat) : Set Nat := fun k => k < n
def closedInitial (n : Nat) : Set Nat := fun k => k ≤ n
def final (n : Nat) : Set Nat := fun k => n < k
def successor (n m : Nat) : Prop := m = n + 1
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def disjoint (s t : Set α) := ∀ x, s x → t x → False

theorem star_204_581 (n : Nat) : subset (initial n) (closedInitial n) := fun {_} h => Nat.le_of_lt h
theorem star_204_59 (n : Nat) : disjoint (initial n) (final n) := fun k hk hnk => Nat.not_lt_of_ge (Nat.le_of_lt hnk) hk
theorem star_204_6 (n : Nat) : successor n (n + 1) := rfl
theorem star_204_61 (n m : Nat) : successor n m ↔ m = n + 1 := Iff.rfl
theorem star_204_62 (n m : Nat) : successor n m → n < m := by rintro rfl; exact Nat.lt_succ_self n
theorem star_204_63 (n m : Nat) : successor n m → n ≤ m := fun h => Nat.le_of_lt (star_204_62 n m h)
theorem star_204_64 (n m k : Nat) : successor n m → successor n k → m = k := by rintro rfl rfl; rfl
theorem star_204_65 (n m k : Nat) : successor n m → m < k → n < k := fun h hmk => Nat.lt_trans (star_204_62 n m h) hmk
theorem star_204_7 (n : Nat) :
    ∃ m, successor n m ∧ ∀ y, successor n y → y = m :=
  ⟨n+1,rfl,fun y hy => hy⟩
theorem star_204_71 (n m : Nat) : successor n m → initial m = closedInitial n := by
 rintro rfl; funext k; apply propext; exact Nat.lt_succ_iff
theorem star_204_72 (n m : Nat) : successor n m → final n m := star_204_62 n m
end PM.Architecture.Star204FinalKernel
