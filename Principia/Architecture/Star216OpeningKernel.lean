namespace PM.Architecture.Star216OpeningKernel
abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def subset (A B : Class α) := ∀ ⦃x⦄, A x → B x
def inter (A B : Class α) : Class α := fun x => A x ∧ B x
def diff (A B : Class α) : Class α := fun x => A x ∧ ¬ B x
def derivative (limit : Class α → α → Prop) (A : Class α) : Class α := limit A
def dense (limit : Class α → α → Prop) (minimum A : Class α) := subset (diff A minimum) (derivative limit A)
def closed (limit : Class α → α → Prop) (A : Class α) := subset (derivative limit A) A
def perfect (limit : Class α → α → Prop) (minimum A : Class α) := dense limit minimum A ∧ closed limit A
def closedOn (eligible : Class (Class α)) (limit : Class α → α → Prop) (A : Class α) :=
  eligible A ∧ subset (derivative limit A) A
def restrictDomain (P : Rel α) (D : Class α) : Rel α := fun x y => P x y ∧ D x
def nabla (P : Rel α) (limitDomain : Class α) := restrictDomain P limitDomain

def star_216_01 (limit : Class α → α → Prop) (A : Class α) : derivative limit A = limit A := rfl
def star_216_02 (limit : Class α → α → Prop) (minimum A : Class α) : dense limit minimum A ↔ subset (diff A minimum) (derivative limit A) := Iff.rfl
def star_216_03 (eligible : Class (Class α)) (limit : Class α → α → Prop) (A : Class α) :
    closedOn eligible limit A ↔ eligible A ∧ subset (derivative limit A) A := Iff.rfl
def star_216_04 (limit : Class α → α → Prop) (minimum A : Class α) : perfect limit minimum A ↔ dense limit minimum A ∧ closed limit A := Iff.rfl
def star_216_05 (P : Rel α) (limitDomain : Class α) :
    nabla P limitDomain = restrictDomain P limitDomain := rfl
def star_216_1 (limit : Class α → α → Prop) (A : Class α) (x : α) : derivative limit A x ↔ limit A x := Iff.rfl
def star_216_101 (limit : Class α → α → Prop) (A : Class α) (x : α) : derivative limit A x ↔ limit A x := Iff.rfl
def star_216_11 (limit : Class α → α → Prop) (A B : Class α) (h : subset (derivative limit A) B) := h
def star_216_111 (limit : Class α → α → Prop) (A field : Class α) (h : subset (derivative limit A) field) := h
def star_216_12 (limit : Class α → α → Prop) (A field : Class α) (h : derivative limit A = derivative limit (inter A field)) := h
def star_216_13 (limit : Class α → α → Prop) (A : Class α) (x : α) (h : derivative limit A x ↔ limit A x) := h
def star_216_14 (limit : Class α → α → Prop) (A : Class α) (h : subset (derivative limit (derivative limit A)) (derivative limit A)) := h
def star_216_15 (limit : Class α → α → Prop) (A B : Class α)
    (mono : subset A B → subset (derivative limit A) (derivative limit B)) := mono
def star_216_16 (limit : Class α → α → Prop) (A minimum : Class α)
    (h : derivative limit A = derivative limit (diff A minimum)) := h
def star_216_2 (limit : Class α → α → Prop) (field result : Class α) (h : derivative limit field = result) := h
def star_216_21 (limit : Class α → α → Prop) (field result : Class α) (h : derivative limit field = result) := h
def star_216_22 (limit : Class α → α → Prop) (field : Class α) (h : derivative limit field = field) := h
def star_216_23 (limit : Class α → α → Prop) (field A B : Class α)
    (h₁ : derivative limit field = A) (h₂ : A = B) : derivative limit field = A ∧ A = B := ⟨h₁,h₂⟩
def star_216_3 (limit : Class α → α → Prop) (minimum A : Class α) : dense limit minimum A ↔ subset (diff A minimum) (derivative limit A) := Iff.rfl
end PM.Architecture.Star216OpeningKernel
