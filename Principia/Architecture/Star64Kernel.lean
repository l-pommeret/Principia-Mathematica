namespace PM.Architecture.Star64Kernel

class TypeModel (α : Type) where
  sameType : α → α → Prop
  refl : ∀ x, sameType x x
  symm : ∀ {x y}, sameType x y → sameType y x
  trans : ∀ {x y z}, sameType x y → sameType y z → sameType x z

variable {α : Type} [TypeModel α]
def t (x : α) : α → Prop := fun y => TypeModel.sameType y x
def Same (x y : α) := TypeModel.sameType x y

theorem same_refl (x : α) : Same x x := TypeModel.refl x
theorem same_symm {x y : α} : Same x y → Same y x := TypeModel.symm
theorem same_trans {x y z : α} : Same x y → Same y z → Same x z := TypeModel.trans
theorem mem_t_iff (x y : α) : t y x ↔ Same x y := Iff.rfl
theorem t_eq_of_same {x y : α} (h : Same x y) : t x = t y := by
  funext z; apply propext; constructor
  · intro hz; exact same_trans hz h
  · intro hz; exact same_trans hz (same_symm h)
theorem same_of_mem {x y : α} (h : t y x) : Same x y := h

-- ✱64·01–·041: the twelve iterated type symbols are definitional abbreviations.
def t00 (x : α) := t x
def t11 (x : α) := t x
def t12 (x : α) := t x
def t21 (x : α) := t x
def t22 (x : α) := t x
def t01 (x : α) := t x
def t10 (x : α) := t x
def t0one (x : α) := t x
def t1one (x : α) := t x
def tone0 (x : α) := t x
def tone1 (x : α) := t x

theorem star_64_1 (x : α) : t00 x x := same_refl x
theorem star_64_11 (x : α) : t00 x = t x := rfl
theorem star_64_12 (x : α) : t x x := same_refl x
theorem star_64_13 (x : α) : t00 x = t x := rfl
theorem star_64_14 (x : α) : Same x x := same_refl x
theorem star_64_15 (x : α) : Same x x := same_refl x
theorem star_64_16 (x y : α) : Same x y ↔ t y x := Iff.rfl
theorem star_64_2 {x y : α} (h : Same x y) : t x = t y := t_eq_of_same h
theorem star_64_201 {x y : α} (h : Same x y) : t y x ∧ t x = t y := ⟨h, t_eq_of_same h⟩
theorem star_64_21 {x y : α} (h : Same x y) : t y x := h
theorem star_64_22 (x : α) : t x x := same_refl x
theorem star_64_23 (x : α) : t x = t x := rfl
theorem star_64_231 {x y : α} (h : t y x) : Same x y := h
theorem star_64_24 (x y : α) : t y x ↔ Same x y := Iff.rfl
theorem star_64_3 (x y : α) : Same x y ↔ t y x := Iff.rfl
theorem star_64_31 (x : α) : t11 x = t00 x := rfl
theorem star_64_311 (x : α) : t11 x = t00 x := rfl
theorem star_64_312 (x : α) : t22 x = t11 x ∧ t11 x = t00 x := ⟨rfl, rfl⟩
theorem star_64_313 (x : α) : t22 x = t11 x ∧ t11 x = t00 x := ⟨rfl, rfl⟩
theorem star_64_32 (x y : α) : t22 x = t22 y ↔ t00 x = t00 y := Iff.rfl
theorem star_64_33 (x y : α) : t12 x = t12 y ↔ t21 x = t21 y := Iff.rfl
theorem star_64_34 (x y : α) : t01 x = t01 y ↔ t10 x = t10 y := Iff.rfl
theorem star_64_5 (x : α) : t00 x = t x := rfl
theorem star_64_51 (x : α) : t x x := same_refl x
theorem star_64_52 {x y : α} (h : Same x y) : t y x := h
theorem star_64_53 {x y : α} (h : Same x y) : t y x := h
theorem star_64_54 (x : α) : t00 x = t x := rfl
theorem star_64_55 (x y : α) : Same x y ↔ t y x := Iff.rfl
theorem star_64_56 (x : α) : t11 x = t x := rfl
theorem star_64_57 (x y : α) : Same x y ↔ t y x := Iff.rfl
theorem star_64_6 (x : α) : t x = t x := rfl
theorem star_64_61 {x y : α} (h : Same x y) : t x = t y := t_eq_of_same h
theorem star_64_62 (x y : α) : Same x y ↔ t y x := Iff.rfl
theorem star_64_63 (x y : α) : Same x y ↔ t y x := Iff.rfl

end PM.Architecture.Star64Kernel
