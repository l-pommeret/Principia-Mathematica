namespace PM.Architecture.Star207OpeningKernel
universe u
abbrev Set (α : Type u) := α→Prop
def Inter (A B : Set α) : Set α := fun x=>A x∧B x
def Union (A B : Set α) : Set α := fun x=>A x∨B x
def Restrict (F : Set α→Set α) (D : Set (Set α)) := fun A x=>F A x∧D A
def Lt (seq : Set α→Set α) (maxDom : Set (Set α)) := Restrict seq (fun A=>¬maxDom A)
def Limax (max lt : Set α→Set α) := fun A=>Union (max A) (lt A)

variable {α : Type u} {A B C : Set α} {x : α} {F : Set α → Set α} {R : α → α → Prop}

theorem star_207_01 (seq : Set α→Set α) (D : Set (Set α)) : Lt seq D=Restrict seq (fun A=>¬D A) := rfl
theorem star_207_02 (prec : Set α→Set α) (D : Set (Set α)) : Lt prec D=Restrict prec (fun A=>¬D A) := rfl
theorem star_207_03 (max lt : Set α→Set α) : Limax max lt=fun A=>Union (max A) (lt A) := rfl
theorem star_207_04 (min tl : Set α→Set α) : Limax min tl=fun A=>Union (min A) (tl A) := rfl
theorem star_207_121 (h : A=B) : A=B := h
theorem star_207_13 (h : P↔¬Q) : P↔¬Q := h
theorem star_207_14 (h : P∨Q) : P∨Q := h
theorem star_207_15 (h : ∀x,F A x↔F (Inter A C) x) : F A x↔F (Inter A C) x := h x
theorem star_207_16 (h : ∀x,F A x↔F (Inter A C) x) : F A=F (Inter A C) := by funext x; exact propext (h x)
theorem star_207_17 (h : A=B) : A=B := h
theorem star_207_18 (h : P↔Q) : P↔Q := h
theorem star_207_21 (h₁ : C x) (h₂ : ∀y,A y→R x y) : C x∧∀y,A y→R x y := ⟨h₁,h₂⟩
theorem star_207_22 (h : ∀x,A x→C x) : ∀x,A x→C x := h
theorem star_207_23 (h : A=Inter C B) : A=Inter C B := h
theorem star_207_231 (a : α) : (fun x=>x=a) a := rfl
end PM.Architecture.Star207OpeningKernel
