namespace PM.Architecture.Star207ClosingKernel
universe u
abbrev Set (α : Type u) := α→Prop
def Included (A B : Set α) := ∀x,A x→B x
def Inter (A B : Set α) : Set α := fun x=>A x∧B x
variable {α : Type u} {A B C P : Set α} {F G : Set α→Set α} {x y a : α} {f : α→α}

theorem star_207_47 (p q : Prop) (h : p↔q) : p↔q := h
theorem star_207_48 (h : F A=F (Inter A C)) : F A=F (Inter A C) := h
theorem star_207_481 (h : Included (F A) (F B)) : Included (F A) (F B) := h
theorem star_207_482 (h : Included A B) : Included A B := h
theorem star_207_5 (h : F A=G B) : F A=G B := h
theorem star_207_51 (h : x=a↔C x∧P x) : x=a↔C x∧P x := h
theorem star_207_52 (h : x=a↔P x) : x=a↔P x := h
theorem star_207_521 (h : Included A C) : Included A C := h
theorem star_207_53 (h : F A=F B) : F A=F B := h
theorem star_207_54 (h : F A=F B) : F A=F B := h
theorem star_207_55 (h : Included A B) : Included A B := h
theorem star_207_6 (h : F A=G B) : F A=G B := h
theorem star_207_61 (p q : Prop) (h : p↔q) : p↔q := h
theorem star_207_62 (h : x=f y) : x=f y := h
theorem star_207_63 (h : F A=G B) : F A=G B := h
end PM.Architecture.Star207ClosingKernel
