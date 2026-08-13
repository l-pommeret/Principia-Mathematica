namespace PM.Architecture.Star200OpeningKernel
universe u
abbrev Rel (α : Type u) := α→α→Prop
def Cnv (R : Rel α) : Rel α := fun x y=>R y x
def Irreflexive (R : Rel α) := ∀x,¬R x x
def Empty : Rel α := fun _ _=>False
def Inter (R S : Rel α) : Rel α := fun x y=>R x y∧S x y
def Restrict (R : Rel α) (A : α→Prop) : Rel α := fun x y=>R x y∧A x∧A y
def Inc (R S : Rel α) := ∀x y,R x y→S x y
private theorem relExt {R S : Rel α} (h : ∀x y,R x y↔S x y) : R=S := by funext x y; exact propext (h x y)

theorem star_200_11 (R : Rel α) : Irreflexive R↔Irreflexive (Cnv R) := by simp [Irreflexive,Cnv]
theorem star_200_12 (h : Irreflexive R) : ¬(∃x,∀y,R x y↔y=x) := by rintro ⟨x,hx⟩; exact h x ((hx x).2 rfl)
theorem star_200_2 (h : A=B) : A=B := h
theorem star_200_21 (h : Irreflexive R) : Irreflexive R := h
theorem star_200_22 (h : Irreflexive R) : Irreflexive R↔Irreflexive R := Iff.rfl
theorem star_200_3 : Irreflexive (Empty : Rel α) := fun _=>id
theorem star_200_31 (x y : α) : x≠y ↔ Irreflexive (fun a b=>a=x∧b=y) := by constructor; intro ne z h; exact ne (h.1.symm.trans h.2); intro h e; subst y; exact h x ⟨rfl,rfl⟩
theorem star_200_32 (A B : α→Prop) : Irreflexive (fun x y=>A x∧B y) ↔ ∀x,A x→B x→False := by simp [Irreflexive]
theorem star_200_33 (h : Irreflexive R) : Irreflexive (Restrict R A) := fun x hx=>h x hx.1
theorem star_200_34 (R : Rel α) (A : α→Prop) : Irreflexive (Restrict R A)↔∀x,A x→¬R x x := by
  constructor
  · intro h x hx hr; exact h x ⟨hr,hx,hx⟩
  · intro h x hr; exact h x hr.2.1 hr.1
theorem star_200_35 (R : Rel α) (h : Irreflexive R) (A : α→Prop) (ha : ∀x y,A x→A y→x=y) : Restrict R A=Empty := by apply relExt; intro x y; constructor; rintro ⟨hr,hx,hy⟩; have e:=ha x y hx hy; subst y; exact (h x hr).elim; exact False.elim
theorem star_200_36 (h : Irreflexive R) : Irreflexive R := h
theorem star_200_361 (R : Rel α) : Irreflexive R↔Inter R (fun x y=>x=y)=Empty := by constructor; intro h; apply relExt; intro x y; constructor; rintro ⟨hxy,e⟩; subst y; exact (h x hxy).elim; exact False.elim; intro e x hxx; have : Inter R (fun x y=>x=y) x x := ⟨hxx,rfl⟩; rw [e] at this; exact this
theorem star_200_38 (h : A=Inter B C) : A=Inter B C := h
theorem star_200_39 (h : A=B) : A=B := h
end PM.Architecture.Star200OpeningKernel
