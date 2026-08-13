import Principia.Architecture.Star126CardinalArchitecture
import Principia.FirstEdition.Volume2.Star126Source

namespace PM.Architecture.Star126OpeningKernel
open PM.Architecture.Star126CardinalArchitecture

theorem star_126_01 : NCind n ↔ True := Iff.rfl
theorem star_126_011 : NCind n ↔ NCind n ∧ n ≠ (0:Nat) ∨ n = 0 := by
  simp only [NCind, true_and, true_iff]
  exact Classical.em (n = 0) |>.symm
theorem star_126_12 : NCind n → NCind (successor n) := ncind_successor
theorem star_126_121 (n : Nat) : NCind (n + 1) := trivial
theorem star_126_13 : NCind m → NCind n → NCind (cadd m n) := ncind_add
theorem star_126_14 : NCind m → NCind n → NCind (cmul m n) := ncind_mul
theorem star_126_15 : NCind m → NCind n → NCind (cpow m n) := ncind_pow
theorem star_126_141 : (NonzeroNCind m ∧ NonzeroNCind n) ↔ NonzeroNCind (cmul m n) := by
  simp only [NonzeroNCind, NCind, true_and, cmul]
  constructor
  · rintro ⟨hm,hn⟩
    exact Nat.mul_ne_zero hm hn
  · intro h; constructor
    · intro hm; exact h (hm ▸ Nat.zero_mul n)
    · intro hn; exact h (hn ▸ Nat.mul_zero m)

theorem star_126_31 : NCind (successor n) ↔ NCind n := Iff.rfl
theorem star_126_41 (hp : p ≠ 0) : cmul m p = cmul n p ↔ m = n := by
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_ne_zero hp), congrArg (fun x => cmul x p)⟩
theorem star_126_5 : cadd m p = cadd n p ↔ m = n := by
  exact ⟨Nat.add_right_cancel, congrArg (fun x => cadd x p)⟩
theorem star_126_51 (hp : p ≠ 0) : cmul n p < cmul m p ↔ n < m := by
  exact Nat.mul_lt_mul_right (Nat.zero_lt_of_ne_zero hp)

theorem pow_strictMono_base (hp : p ≠ 0) : m < n → cpow m p < cpow n p := by
  intro h
  exact Nat.pow_lt_pow_left h hp

theorem star_126_52 (hp : p ≠ 0) : cpow m p < cpow n p ↔ m < n := by
  constructor
  · intro h
    apply Nat.lt_of_not_le
    intro hnm
    exact Nat.not_lt_of_ge (Nat.pow_le_pow_left (n := n) (m := m) hnm p) h
  · intro h; exact pow_strictMono_base hp h

theorem star_126_53 (hp : 1 < p) : m < n → cpow p m < cpow p n := by
  intro h
  exact Nat.pow_lt_pow_right hp h

theorem star_126_32 (hm : m ≠ 0) : n < cadd m n := by
  simpa [cadd] using (Nat.lt_add_of_pos_left (n := n) (Nat.zero_lt_of_ne_zero hm))
theorem star_126_4 : cadd m p = cadd n p ↔ m = n := star_126_5
theorem star_126_42 (hp : p ≠ 0) : cpow m p = cpow n p ↔ m = n := by
  constructor
  · intro h
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt; intro hnm; exact (Nat.ne_of_lt (pow_strictMono_base hp hnm)) h.symm
    · apply Nat.le_of_not_gt; intro hmn; exact (Nat.ne_of_lt (pow_strictMono_base hp hmn)) h
  · exact congrArg (fun x => cpow x p)
theorem star_126_43 (hp : 1 < p) : cpow p m = cpow p n ↔ m = n := by
  constructor
  · intro h
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt; intro hnm; exact (Nat.ne_of_lt (star_126_53 hp hnm)) h.symm
    · apply Nat.le_of_not_gt; intro hmn; exact (Nat.ne_of_lt (star_126_53 hp hmn)) h
  · exact congrArg (cpow p)

theorem star_126_33 (m n : Nat) : m < n ∨ m = n ∨ n < m := by
  exact Nat.lt_trichotomy m n

theorem star_126_151 (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hn0 : n ≠ 0) :
    cpow m n ≠ 0 ∧ cpow m n ≠ 1 := by
  constructor
  · intro h; exact hm0 ((Nat.pow_eq_zero.mp h).1)
  · intro h
    rcases Nat.pow_eq_one.mp h with h | h
    · exact hm1 h
    · exact hn0 h

end PM.Architecture.Star126OpeningKernel
