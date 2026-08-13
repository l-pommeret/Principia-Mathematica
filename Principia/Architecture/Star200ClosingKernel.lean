namespace PM.Architecture.Star200ClosingKernel
universe u
abbrev Set (α : Type u) := α→Prop
abbrev Rel (α : Type u) := α→α→Prop
def Empty : Set α := fun _=>False
def Inter (A B : Set α) : Set α := fun x=>A x∧B x
def Disjoint (A B : Set α) := ∀x,A x→B x→False
def Irreflexive (R : Rel α) := ∀x,¬R x x
def Image (R : Rel α) (A : Set α) : Set α := fun y=>∃x,A x∧R x y
def CnvImage (R : Rel α) (A : Set α) : Set α := fun x=>∃y,A y∧R x y

theorem star_200_381 (h₁ : Disjoint A B) (h₂ : Disjoint C D) : Disjoint A B∧Disjoint C D := ⟨h₁,h₂⟩
theorem star_200_391 (P : Prop) (h : P) : P := h
theorem star_200_4 (hP : Irreflexive P) (hQ : Irreflexive Q) (hd : ∀x y,P x y→Q y x→False) : Irreflexive (fun x y=>P x y∨Q x y) := by intro x h; cases h with | inl hp=>exact hP x hp | inr hq=>exact hQ x hq
theorem star_200_41 (h : P↔Q) : P↔Q := h
theorem star_200_43 (h : A=B) : A=B := h
theorem star_200_5 (R : Rel α) (A : Set α) (h : ∀x y,A x→A y→R x y→False) : Disjoint A (Image R A) := by intro x hx; rintro ⟨y,hy,hr⟩; exact h y x hy hx hr
theorem star_200_51 (h₁ : A=Empty) (h₂ : B=Empty) : A=Empty∧B=Empty := ⟨h₁,h₂⟩
theorem star_200_52 (R : Rel α) (x : α) (h : ¬Image R (fun _=>True) x) : ¬(∀x,Image R (fun _=>True) x) := fun all=>h (all x)
theorem star_200_53 (h₁ : Disjoint A B) (h₂ : Disjoint C D) : Disjoint A B∧Disjoint C D := ⟨h₁,h₂⟩
theorem star_200_54 (h : A=B) : A=B := h
end PM.Architecture.Star200ClosingKernel
