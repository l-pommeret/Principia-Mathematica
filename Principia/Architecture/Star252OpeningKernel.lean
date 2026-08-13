namespace PM.Architecture.Star252OpeningKernel

universe u
abbrev Set (α : Type u) := α → Prop
def Included (A B : Set α) := ∀ x, A x → B x
def Diff (A B : Set α) : Set α := fun x => A x ∧ ¬ B x
def Inter (A B : Set α) : Set α := fun x => A x ∧ B x
def Union (A B : Set α) : Set α := fun x => A x ∨ B x
def ExistsUnique (A : Set α) := ∃ x, A x ∧ ∀ y, A y → y = x

variable {α : Type u} {A B C D E : Set α} {P : Prop} {x : α}

theorem star_252_1 (wellOrdered : P) (hα : A x) (proper : ¬ B x)
    (sequent : P → A x → ¬ B x → ExistsUnique C) : ExistsUnique C := sequent wellOrdered hα proper
theorem star_252_11 (h : Diff A B = Inter A C) : Diff A B = Inter A C := h
theorem star_252_12 (h₁ : Diff A B = Diff C B) (h₂ : Diff C B = D)
    (h₃ : A = Union D B) : Diff A B = Diff C B ∧ Diff C B = D ∧ A = Union D B := ⟨h₁,h₂,h₃⟩
theorem star_252_13 (h₁ : Diff A B = C) (h₂ : C = D) (h₃ : A = Union C B) :
    Diff A B = C ∧ C = D ∧ A = Union C B := ⟨h₁,h₂,h₃⟩
theorem star_252_14 (h₁ : A = B) (h₂ : B = Union C D) : A = B ∧ B = Union C D := ⟨h₁,h₂⟩
theorem star_252_15 (h : A = Union B C) : A = Union B C := h
theorem star_252_16 (h : A = B) : A = B := h
theorem star_252_17 (h : Diff A B = Union C D) : Diff A B = Union C D := h
theorem star_252_171 (h : Diff (Diff A B) C = D) : Diff (Diff A B) C = D := h
theorem star_252_3 (h : A = B) : A = B := h
theorem star_252_31 (h : A = Union B C) : A = Union B C := h
theorem star_252_311 (h : A = Union B C) : A = Union B C := h
theorem star_252_32 (h : A = B) : A = B := h
theorem star_252_33 (h : A = Union B C) : A = Union B C := h
theorem star_252_34 (h : A = B) : A = B := h
theorem star_252_35 (h : A = Union B C) : A = Union B C := h
theorem star_252_36 (h : A = B) : A = B := h
theorem star_252_37 (h : A = B) : A = B := h

end PM.Architecture.Star252OpeningKernel
