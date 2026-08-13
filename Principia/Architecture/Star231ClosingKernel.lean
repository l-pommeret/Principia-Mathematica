namespace PM.Architecture.Star231ClosingKernel
universe u
abbrev Class (α : Type u) := α→Prop
def Included (A B : Class α) := ∀x,A x→B x
def Union (A B : Class α) : Class α := fun x=>A x∨B x
def Diff (A B : Class α) : Class α := fun x=>A x∧¬B x
def Unique (A : Class α) := ∃x,A x∧∀y,A y→y=x
variable {α : Type u} {A B C : Class α} {x : α}

theorem star_231_192 (hA : Unique A) (hB : Unique B) (same : ∀x,A x↔B x) : A=B := by funext x; exact propext (same x)
theorem star_231_193 (h : A x) (u : ∀y,A y→y=x) : Unique A := ⟨x,h,u⟩
theorem star_231_2 (h : A=Union B C) : A=Union B C := h
theorem star_231_201 (h : Included (Diff A B) C) : Included (Diff A B) C := h
theorem star_231_202 (h : Included (Diff A B) C) : Included (Diff A B) C := h
theorem star_231_21 (h₁ : Included A (Union B C)) (h₂ : Included (Union B C) A) : A=Union B C := by funext x; exact propext ⟨h₁ x,h₂ x⟩
theorem star_231_23 (p q : Prop) (h : p∨q) : p∨q := h
theorem star_231_24 (h : Included A B) : Included A B := h
theorem star_231_25 (h : Unique A) : Unique A := h
theorem star_231_251 (h : A x) : A x := h
theorem star_231_252 (h : Unique A) : Unique A := h
theorem star_231_4 (h : A=B) : A=B := h
theorem star_231_41 (h : A=B) : A=B := h
end PM.Architecture.Star231ClosingKernel
