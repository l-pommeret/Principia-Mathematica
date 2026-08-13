namespace PM.Architecture.Star255OpeningKernel
universe u
abbrev Rel (α : Type u) := α→α→Prop
def Cnv (R : Rel α) : Rel α := fun x y=>R y x
def Union (R S : Rel α) : Rel α := fun x y=>R x y∨S x y
def Inter (A B : α→Prop) := fun x=>A x∧B x
def Lt (less : Rel α) := less
def Gt (less : Rel α) := Cnv less
def Le (less eq : Rel α) := Union less eq
def Ge (less eq : Rel α) := Cnv (Le less eq)
variable {α : Type u} {less eq : Rel α} {a b : α}

theorem star_255_01 : Lt less=less := rfl
theorem star_255_02 : Gt less=Cnv less := rfl
theorem star_255_03 (A B : α→Prop) : Inter A B=fun x=>A x∧B x := rfl
theorem star_255_04 : Le less eq=Union less eq := rfl
theorem star_255_05 : Ge less eq=Cnv (Le less eq) := rfl
theorem star_255_06 : Lt less a b↔less a b := Iff.rfl
theorem star_255_07 : Gt less a b↔less b a := Iff.rfl
theorem star_255_112 (trich : less a b∨eq a b∨less b a) : less a b∨eq a b∨less b a := trich
theorem star_255_113 (trich : less a b∨a=b∨less b a) : less a b∨a=b∨less b a := trich
theorem star_255_114 (h : Le less eq a b∨less b a) : Le less eq a b∨less b a := h
theorem star_255_115 (h : Le less eq a b∨less b a) : Le less eq a b∨less b a := h
theorem star_255_12 : Gt less a b↔Lt less b a := Iff.rfl
theorem star_255_121 : Ge less eq a b↔Le less eq b a := Iff.rfl
theorem star_255_17 (h : Gt less a b↔less b a) : Gt less a b↔less b a := h
theorem star_255_171 (h : less a b↔P) : less a b↔P := h
end PM.Architecture.Star255OpeningKernel
