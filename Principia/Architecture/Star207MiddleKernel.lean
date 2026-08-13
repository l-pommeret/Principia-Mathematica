namespace PM.Architecture.Star207MiddleKernel
universe u
abbrev Set (α : Type u) := α→Prop
def Union (A B : Set α) : Set α := fun x=>A x∨B x
def Diff (A B : Set α) : Set α := fun x=>A x∧¬B x
def Included (A B : Set α) := ∀x,A x→B x
def Limax (max lt : Set α) := Union max lt
variable {α : Type u} {A B C D : Set α} {x : α}

theorem star_207_232 (h : x=a↔C x∧D x) : x=a↔C x∧D x := h
theorem star_207_24 (h : ∀x y,A x→A y→x=y) : ∀x y,A x→A y→x=y := h
theorem star_207_25 (h : A=B) : A=B := h
theorem star_207_26 (h : Included A B) : Included A B := h
theorem star_207_262 (h : Included A B) : Included A B := h
theorem star_207_263 (h : Included A B) : Included A B := h
theorem star_207_31 (P : Prop) (h : P) : P := h
theorem star_207_34 (P Q : Prop) (h₁ : P) (h₂ : Q) : P∧Q := ⟨h₁,h₂⟩
theorem star_207_35 (h : A=Diff B C) : A=Diff B C := h
theorem star_207_4 (max lt : Set α) : Limax max lt x↔max x∨lt x := Iff.rfl
theorem star_207_42 (max lt : Set α) (h : ∀x,¬lt x) : Limax max lt=max := by funext x; exact propext ⟨fun hx=>hx.elim id (fun hl=>(h x hl).elim),Or.inl⟩
theorem star_207_43 (max lt seq : Set α) (hm : ∀x,¬max x) (h : lt=seq) : Limax max lt=seq := by funext x; exact propext ⟨fun hx=>hx.elim (fun hm'=>(hm x hm').elim) (fun hl=>h ▸ hl),fun hs=>Or.inr (h.symm ▸ hs)⟩
theorem star_207_44 (h₁ : A=Union B C) (h₂ : Union B C=Union B D) : A=Union B C∧Union B C=Union B D := ⟨h₁,h₂⟩
theorem star_207_45 (max lt : Set α) : Limax max lt=Union max lt := rfl
theorem star_207_46 (max lt : Set α) : Limax max lt x↔max x∨lt x := Iff.rfl
end PM.Architecture.Star207MiddleKernel
