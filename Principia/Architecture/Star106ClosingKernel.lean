namespace PM.Architecture.Star106ClosingKernel
universe u
abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def Disjoint (A B : Class α) := ∀x, A x → B x → False
def Included (A B : Class α) := ∀x,A x→B x
def Empty : Class α := fun _=>False
def Diff (A B : Class α) : Class α := fun x=>A x∧¬B x
def W (A : Class α) (R : Rel α) : Rel α := fun x y=>A x∧A y∧¬R x y

theorem star_106_43 (hA : A a) (hB : B b) (hd : Disjoint A B) : ∃x y,A x∧B y∧Disjoint A B := ⟨a,b,hA,hB,hd⟩
theorem star_106_44 (hA : A a) (hB : B b) (hd : Disjoint A B) : ∃x y,A x∧B y∧Disjoint A B := ⟨a,b,hA,hB,hd⟩
theorem star_106_5 (A : Class α) (R : Rel α) : ∀x y,W A R x y→A x∧A y := fun _ _ h=>⟨h.1,h.2.1⟩
theorem star_106_51 (h : Included B A) (no : ¬P) : Included B A ∧ ¬P := ⟨h,no⟩
theorem star_106_52 (A B : Class α) (C : Class α → Prop) (h : Included B A) (no : ¬C B) : Included B A → ¬C B := fun _=>no
theorem star_106_53 (h : ∀x,¬A x) : A=Empty := by funext x; exact propext ⟨fun hx=>(h x hx).elim,False.elim⟩
theorem star_106_54 (B : Class α) (x : α) (h : ¬B x) : ¬B x := h
theorem star_106_55 (x : α) (hA : A x) (hB : ¬B x) : ∃y,Diff A B y := ⟨x,hA,hB⟩
end PM.Architecture.Star106ClosingKernel
