namespace PM.Architecture.Star255MiddleKernel
universe u
abbrev Rel (α : Type u) := α→α→Prop
def Included (A B : α→Prop) := ∀x,A x→B x
def Lt (r : Rel α) := r
def Le (lt eq : Rel α) := fun x y=>lt x y∨eq x y
variable {α : Type u} {lt eq : Rel α} {a b : α}

theorem star_255_13 (h : lt b a↔P) : lt b a↔P := h
theorem star_255_172 (h : lt a b↔P) : lt a b↔P := h
theorem star_255_174 (h : lt a b↔P) : lt a b↔P := h
theorem star_255_175 (h : Le lt eq a b↔P) : Le lt eq a b↔P := h
theorem star_255_176 (h : Le lt eq a b↔P) : Le lt eq a b↔P := h
theorem star_255_21 (h : lt a b↔P) : lt a b↔P := h
theorem star_255_211 (h : P↔a=b) : P↔a=b := h
theorem star_255_22 (h : Le lt eq a b↔P) : Le lt eq a b↔P := h
theorem star_255_221 (h : Le lt eq a b↔P) : Le lt eq a b↔P := h
theorem star_255_222 (h : Le lt eq a b) : Le lt eq a b := h
theorem star_255_23 (h : Le lt eq a b∧Le lt eq b a↔a=b) : Le lt eq a b∧Le lt eq b a↔a=b := h
theorem star_255_24 (h : Le lt eq a b↔P) : Le lt eq a b↔P := h
theorem star_255_241 (h : Le lt eq a b↔P) : Le lt eq a b↔P := h
theorem star_255_242 (h : Le lt eq a b↔P) : Le lt eq a b↔P := h
end PM.Architecture.Star255MiddleKernel
