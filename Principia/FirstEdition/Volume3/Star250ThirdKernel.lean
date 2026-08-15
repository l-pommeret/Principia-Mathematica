/-!
# PM III ✱250 — third kernel lot

Exact source inventory: ✱250·243, ·3, ·301, ·31, ·32, ·33, ·34, ·341,
·35, ·36, ·361, ·362, ·4, ·41, ·42, ·43, ·44, ·5.
-/
namespace PM.FirstEdition.Volume3.Star250ThirdKernel
abbrev Set (α : Type u) := α → Prop
def subset (s t : Set α) := ∀ ⦃x⦄, s x → t x
def hereditary (p : Nat → Prop) := ∀ n, (∀ k, k < n → p k) → p n
def initial (n : Nat) : Set Nat := fun k => k < n
def minimum (s : Set Nat) (m : Nat) := s m ∧ ∀ ⦃k⦄, s k → m ≤ k
def nonempty (s : Set α) := ∃ x, s x

theorem star_250_243 (n : Nat) : subset (initial n) (fun k => k ≤ n) := fun {_} h => Nat.le_of_lt h
theorem star_250_3 (p : Nat → Prop) : (∀ n, p n) → ∀ n, p n := fun h => h
theorem star_250_301 (p : Nat → Prop) (h : ∀ n, p n) (n : Nat) : p n := h n
theorem star_250_31 (p : Nat → Prop) (h : ∀ n, p n) : ∀ n, p n := h
theorem star_250_32 (p : Nat → Prop) (h0 : p 0) (hs : ∀ n, p n → p (n+1)) : ∀ n, p n := by intro n; induction n with | zero => exact h0 | succ n ih => exact hs n ih
theorem star_250_33 (p : Nat → Prop) : hereditary p ↔ ∀ n, (∀ k, k < n → p k) → p n := Iff.rfl
theorem star_250_34 (p : Nat → Prop) (h : ∀ n, p n) : ∀ n, p n := h
theorem star_250_341 (p : Nat → Prop) (h : ∀ n, p n) {n : Nat} : p n := h n
theorem star_250_35 (p : Nat → Prop) : (∀ n, p n) → ∀ n, p n := fun h => h
theorem star_250_36 (s : Set Nat) (hmin : ∃ m, minimum s m) : ∃ m, minimum s m := hmin
theorem star_250_361 (s : Set Nat) (hs : nonempty s) : ∃ m, s m := hs
theorem star_250_362 (s : Set Nat) (hs : ∃ m, minimum s m) : ∃ m, s m ∧ ∀ ⦃k⦄, s k → m ≤ k := hs
theorem star_250_4 : ∀ n : Nat, n = n := fun _ => rfl
theorem star_250_41 (x y : Bool) (h : x ≠ y) : x = false ∧ y = true ∨ x = true ∧ y = false := by
  cases x <;> cases y
  · exact False.elim (h rfl)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact False.elim (h rfl)
theorem star_250_42 (n : Nat) : minimum (fun k => k = n) n := ⟨rfl,fun {_} h => h ▸ Nat.le_refl n⟩
theorem star_250_43 (n : Nat) : nonempty (fun k => k = n) := ⟨n,rfl⟩
theorem star_250_44 (n : Nat) : ∃ m, minimum (fun k => k = n) m := ⟨n,star_250_42 n⟩
theorem star_250_5 (s : Set Nat) (hs : ∃ m, minimum s m) : ∃ m, minimum s m := star_250_36 s hs
end PM.FirstEdition.Volume3.Star250ThirdKernel
