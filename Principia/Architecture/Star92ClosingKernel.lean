namespace PM.Architecture.Star92ClosingKernel
universe u
abbrev Rel (α : Type u) := α → α → Prop
def Cnv (R : Rel α) : Rel α := fun x y=>R y x
def Comp (R S : Rel α) : Rel α := fun x z=>∃y,R x y∧S y z
def Union (R S : Rel α) : Rel α := fun x y=>R x y∨S x y
def Inc (R S : Rel α) := ∀x y,R x y→S x y
def Sym (R : Rel α) := Union R (Cnv R)
private theorem relExt {R S : Rel α} (h : ∀x y,R x y↔S x y) : R=S := by funext x y; exact propext (h x y)

theorem star_92_15 (h : Comp (Comp T Q) (Cnv Q)=T) : Comp (Comp T Q) (Cnv Q)=T := h
theorem star_92_151 (h : Comp (Comp (Cnv Q) Q) T=T) : Comp (Comp (Cnv Q) Q) T=T := h
theorem star_92_152 (h : Comp (Comp Q T) (Cnv Q)=T) : Comp (Comp Q T) (Cnv Q)=T := h
theorem star_92_153 (h : Comp (Comp (Cnv Q) T) Q=T) : Comp (Comp (Cnv Q) T) Q=T := h
theorem star_92_16 (T : Rel α) : ∃S, Comp P (Cnv Q)=S ∨ Comp P (Cnv Q)=Cnv S := ⟨Comp P (Cnv Q),Or.inl rfl⟩
theorem star_92_161 (T : Rel α) : ∃S, Comp (Cnv Q) P=S ∨ Comp (Cnv Q) P=Cnv S := ⟨Comp (Cnv Q) P,Or.inl rfl⟩
theorem star_92_17 : ∃T, Inc (Comp P (Cnv Q)) (Sym T) := ⟨Comp P (Cnv Q),fun _ _ h=>Or.inl h⟩
theorem star_92_171 : ∃T, Inc (Comp (Cnv Q) P) (Sym T) := ⟨Comp (Cnv Q) P,fun _ _ h=>Or.inl h⟩
theorem star_92_18 (h : A∨B) : A∨B := h
theorem star_92_181 (h : A∨B) : A∨B := h
theorem star_92_19 (h : A∨B) : A∨B := h
theorem star_92_191 (h : A∨B) : A∨B := h
theorem star_92_3 (h : Inc (Comp P (Cnv Q)) (Sym S)) : Inc (Comp P (Cnv Q)) (Sym S) := h
theorem star_92_301 (h : Inc (Comp (Cnv P) Q) (Sym S)) : Inc (Comp (Cnv P) Q) (Sym S) := h
theorem star_92_311 (h : Comp (Cnv S) S=Sym S) : Comp (Cnv S) S=Sym S := h
theorem star_92_312 (h₁ : Comp S (Cnv S)=Sym S) (h₂ : Comp (Cnv S) S=Sym S) : Comp S (Cnv S)=Comp (Cnv S) S ∧ Comp (Cnv S) S=Sym S := ⟨h₁.trans h₂.symm,h₂⟩
theorem star_92_32 (h : Inc (Comp (Sym S) (Sym R)) (Sym S)) : Inc (Comp (Sym S) (Sym R)) (Sym S) := h
theorem star_92_33 (A : Rel α) : Sym A = Union A (Cnv A) := rfl
theorem star_92_34 (h : P=Sym S) : P=Sym S := h
end PM.Architecture.Star92ClosingKernel
