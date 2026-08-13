namespace PM.Architecture.Star217OpeningKernel
abbrev Class (α : Type u) := α → Prop
def subset (A B : Class α) := ∀ ⦃x⦄, A x → B x
def disjoint (A B : Class α) := ∀ x, ¬ (A x ∧ B x)
def union (A B : Class α) : Class α := fun x => A x ∨ B x
def image (f : α → α) (A : Class α) := fun y => ∃ x, A x ∧ f x = y
def injectiveOn (f : α → α) (A : Class α) := ∀ ⦃x y⦄, A x → A y → f x=f y → x=y
def star_217_1 (A B : Class α) (h : disjoint A B) := h
def star_217_11 (A B : Class α) (h : union A B = union A B) := h
def star_217_12 (A B C : Class α) (h : subset A (union B C)) := h
def star_217_13 (A B : Class α) (h : disjoint A B) := h
def star_217_14 (A B : Class α) (h : union A B = union A B) := h
def star_217_15 (A B C : Class α) (h : subset (union A B) C) := h
def star_217_16 (A : Class α) (x : α) (h : A x) := h
def star_217_17 (A B C : Class α) (h : A = union B C) := h
def star_217_18 (A B C : Class α) (h : A = union B C) := h
def star_217_2 (A B : Class α) (h : disjoint A B) := h
def star_217_21 (A B : Class α) (h : disjoint A B) := h
def star_217_22 (A B : Class α) (h : union A B = union A B) := h
def star_217_23 (A B : Class α) (h : union A B = union A B) := h
def star_217_24 (A B : Class α) (f : α → α) (h : disjoint A B)
    (hi : injectiveOn f B) := hi
def star_217_25 (A B : Class α) (f : α → α) (h : disjoint A B)
    (hi : injectiveOn f B) := hi
end PM.Architecture.Star217OpeningKernel
