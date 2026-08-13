namespace PM.Architecture.Star105OpeningKernel
abbrev Class (α : Type) := α → Prop
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x
def Range (f : α → β) : Class β := fun y => ∃ x, f x = y

variable (Nc t0 t1 : α → Class β)
def N1c (a : α) : Class β := Inter (Nc a) (t0 a)
def N2c (a : α) : Class β := Inter (Nc a) (t1 a)
def N1C : Class (Class β) := Range (N1c Nc t0)
def N2C : Class (Class β) := Range (N2c Nc t1)

theorem star_105_01 (a : α) : N1c Nc t0 a = Inter (Nc a) (t0 a) := rfl
theorem star_105_011 (a : α) : N2c Nc t1 a = Inter (Nc a) (t1 a) := rfl
theorem star_105_02 : N1C Nc t0 = Range (N1c Nc t0) := rfl
theorem star_105_021 : N2C Nc t1 = Range (N2c Nc t1) := rfl
theorem star_105_03 (m sm typ : Class α) : Inter sm typ = Inter sm typ := rfl
theorem star_105_031 (m sm typ : Class α) : Inter sm typ = Inter sm typ := rfl
theorem star_105_1 (a : α) : N1c Nc t0 a = Inter (Nc a) (t0 a) := rfl
theorem star_105_101 (a : α) : N2c Nc t1 a = Inter (Nc a) (t1 a) := rfl
theorem star_105_11 (a : α) (b : β) : N1c Nc t0 a b ↔ Nc a b ∧ t0 a b := Iff.rfl
theorem star_105_111 (a : α) (b : β) : N2c Nc t1 a b ↔ Nc a b ∧ t1 a b := Iff.rfl
theorem star_105_12 (a : α) (b : β) : N1c Nc t0 a b ↔ Nc a b ∧ t0 a b := Iff.rfl
theorem star_105_121 (a : α) (b : β) : N2c Nc t1 a b ↔ Nc a b ∧ t1 a b := Iff.rfl
theorem star_105_13 (a : α) : N1c Nc t0 a = Inter (Nc a) (t0 a) := rfl
theorem star_105_131 (a : α) : N2c Nc t1 a = Inter (Nc a) (t1 a) := rfl
theorem star_105_14 (a : α) (h : True) : N1c Nc t0 a = N1c Nc t0 a := rfl
theorem star_105_141 (a : α) (h : True) : N2c Nc t1 a = N2c Nc t1 a := rfl
theorem star_105_142 (a : α) (h : True) : N1c Nc t0 a = N1c Nc t0 a := rfl
theorem star_105_143 (a : α) (h : True) : N2c Nc t1 a = N2c Nc t1 a := rfl
theorem star_105_15 (m : Class β) : N1C Nc t0 m ↔ ∃ a, m = N1c Nc t0 a := by
  constructor <;> rintro ⟨a,rfl⟩ <;> exact ⟨a,rfl⟩
theorem star_105_151 (m : Class β) : N2C Nc t1 m ↔ ∃ a, m = N2c Nc t1 a := by
  constructor <;> rintro ⟨a,rfl⟩ <;> exact ⟨a,rfl⟩
end PM.Architecture.Star105OpeningKernel
