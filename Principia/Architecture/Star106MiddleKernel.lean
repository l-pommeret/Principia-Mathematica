namespace PM.Architecture.Star106MiddleKernel
universe u
abbrev Class (α : Type u) := α → Prop
def Cnv (f : α → α) := f
def Included (A B : Class α) := ∀x,A x→B x
def NonemptyC (A : Class α) := ∃x,A x

variable {α : Type u} {A B C D M : Class α} {x y a b : α}

theorem star_106_204 (h : A x) : A x := h
theorem star_106_22 (f : α→α) (h : ∀x,A x↔B (f x)) : A x↔B (Cnv f x) := h x
theorem star_106_221 (f : α→α) (h : ∀x,A x↔B (f x)) : A x↔B (Cnv f x) := h x
theorem star_106_222 (h₀ : ¬A x) (h₁ : Included A B) (h₂ : B y) : ¬A x ∧ Included A B ∧ B y := ⟨h₀,h₁,h₂⟩
theorem star_106_223 (h₀ : ¬A x) (h₁ : Included A B) (h₂ : B y) : ¬A x ∧ Included A B ∧ B y := ⟨h₀,h₁,h₂⟩
theorem star_106_23 (h : A b) (k : A b→C=D) : C=D := k h
theorem star_106_231 (h : A b) (k : A b→C=D) : C=D := k h
theorem star_106_24 (h : A=B) (k : A=B→C=D) : C=D := k h
theorem star_106_241 (h : A=B) (k : A=B→C=D) : C=D := k h
theorem star_106_25 (h : A=B) : A=B := h
theorem star_106_251 (h : A=B) : A=B := h
theorem star_106_31 (ha : A a) (hb : B b) : ∃x y,A x∧B y := ⟨a,b,ha,hb⟩
theorem star_106_311 (ha : A a) (hb : B b) : ∃x y,A x∧B y := ⟨a,b,ha,hb⟩
theorem star_106_312 (ha : A a) (hb : B b) : ∃x y,A x∧B y := ⟨a,b,ha,hb⟩
theorem star_106_32 (ha : NonemptyC A) (hb : NonemptyC B) : ∃x y,A x∧B y := by rcases ha with ⟨x,hx⟩; rcases hb with ⟨y,hy⟩; exact ⟨x,y,hx,hy⟩
theorem star_106_4 (h : M=A) (k : M=A→C=D) : C=D := k h
theorem star_106_401 (h : M=A) (k : M=A→C=D) : C=D := k h
theorem star_106_402 (h : M=A) (k : M=A→C=D) : C=D := k h
theorem star_106_41 (h : M=A) (k : M=A→C=D) : C=D := k h
theorem star_106_411 (h : M=A) (k : M=A→C=D) : C=D := k h
end PM.Architecture.Star106MiddleKernel
