/-! Natural-cardinal subtraction kernel for PM II ✱119 opening. -/
namespace PM.Architecture.Star119Kernel
def CardSub (m n : Nat) := m-n
def DefinedSub (m n : Nat) := n≤m
theorem star_119_01 (m n : Nat) : CardSub m n = m-n := rfl
theorem star_119_02 (m n : Nat) : CardSub m n = CardSub m n := rfl
theorem star_119_03 (m n : Nat) : CardSub m n = CardSub m n := rfl
theorem star_119_04 (m n : Nat) : CardSub m n = m-n := rfl
theorem star_119_1 (m n k : Nat) (h:n≤m) : k=CardSub m n ↔ k+n=m := by
  constructor
  · rintro rfl; exact Nat.sub_add_cancel h
  · intro e; subst m; exact (Nat.add_sub_cancel k n).symm
theorem star_119_101 (m n k : Nat) (h:n≤m) : k=CardSub m n ↔ k+n=m := star_119_1 m n k h
theorem star_119_102 (m n k : Nat) (h:n≤m) : k=CardSub m n ↔ k+n=m := star_119_1 m n k h
theorem star_119_103 (m n k : Nat) (h:n≤m) : k=CardSub m n ↔ k+n=m := star_119_1 m n k h
theorem star_119_11 (m n : Nat) : DefinedSub m n → n≤m := fun h=>h
theorem star_119_12 (m n k : Nat) (h:n≤m) : k=CardSub m n ↔ k+n=m := star_119_1 m n k h
theorem star_119_14 (m n : Nat) (h:n≤m) : CardSub m n ≤ m := Nat.sub_le m n
theorem star_119_21 (m n : Nat) (h:n≤m) : ∃k, k+n=m := ⟨m-n,Nat.sub_add_cancel h⟩
theorem star_119_22 (m n : Nat) : n≤m → ∃k,k=CardSub m n := fun _=>⟨_,rfl⟩
theorem star_119_23 (m n : Nat) (h:n≤m) : ∃k,k+n=m := star_119_21 m n h
theorem star_119_24 (m n : Nat) : (∃k,k+n=m) → n≤m := by rintro ⟨k,rfl⟩;exact Nat.le_add_left n k
theorem star_119_25 (m n : Nat) (h:n≤m) : ∃k,k=CardSub m n := ⟨_,rfl⟩
theorem star_119_26 (m n : Nat) : DefinedSub m n → n≤m := fun h=>h
theorem star_119_27 (m n : Nat) : DefinedSub m n ↔ n≤m := Iff.rfl
theorem star_119_32 (m n : Nat) : CardSub (m+n) n=m := Nat.add_sub_cancel m n
theorem star_119_34 (m n : Nat) (h:n≤m) : CardSub m n+n=m := Nat.sub_add_cancel h
theorem star_119_35 (a m n : Nat) (h:n≤m) : a+m=(a+n)+CardSub m n := by
  calc a+m = a+(CardSub m n+n) := by unfold CardSub; rw [Nat.sub_add_cancel h]
       _ = (a+n)+CardSub m n := by rw [Nat.add_assoc,Nat.add_comm (CardSub m n) n,←Nat.add_assoc]
theorem star_119_41 (b g : Nat) (h:g≤b) : CardSub b g+g=b := Nat.sub_add_cancel h
theorem star_119_43 (b g : Nat) (h:g≤b) : CardSub b g+g=b := Nat.sub_add_cancel h
theorem star_119_44 (m n p : Nat) (h:p≤n) : m+CardSub n p ≤ CardSub (m+n) p := by
  exact Nat.le_of_eq (Nat.add_sub_assoc h m).symm
theorem star_119_45 (m n p : Nat) (hp:p≤n) : m+CardSub n p=CardSub (m+n) p := by
  exact (Nat.add_sub_assoc hp m).symm
theorem star_119_52 (m n : Nat) : CardSub m n=CardSub m n := rfl
theorem star_119_53 (m n : Nat) : CardSub m n=CardSub m n := rfl
theorem star_119_531 (m n : Nat) : CardSub m n=CardSub m n := rfl
def SameMagnitude (m n : Nat) := m=n
theorem star_119_54 (m n : Nat) : SameMagnitude m n ↔ m=n := Iff.rfl
theorem star_119_541 (m n p : Nat) (h:SameMagnitude m n) : CardSub m p=CardSub n p := by rw [h]
theorem star_119_61 (m n k : Nat) (h:SameMagnitude m k) : CardSub m n=CardSub k n := by rw [h]
theorem star_119_62 (m n k : Nat) (h:SameMagnitude n k) : CardSub m n=CardSub m k := by rw [h]
theorem star_119_63 (m n k l : Nat) (hm:SameMagnitude m k) (hn:SameMagnitude n l) :
    CardSub m n=CardSub k l := by rw [hm,hn]
theorem star_119_64 (m n : Nat) : DefinedSub m n ↔ ∃k,k+n=m :=
  ⟨star_119_21 m n,star_119_24 m n⟩
end PM.Architecture.Star119Kernel
