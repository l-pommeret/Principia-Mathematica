namespace PM.Architecture.Star230OpeningKernel
universe u
abbrev Set (α : Type u) := α→Prop
def Included (A B : Set α) := ∀x,A x→B x
def Inter (A B : Set α) : Set α := fun x=>A x∧B x
def Convergent (field cod : Set α) (image : α→Set α) (target : Set α) : Set α := fun y=>field y∧cod y∧Included (image y) target
def ExistsUnique (A : Set α) := ∃x,A x∧∀y,A y→y=x
variable {α : Type u} {A B C D : Set α} {x y : α}

/-- ✱230·01. RQ̄_cn α=CʻQ∩ᗡʻR∩ŷ(RʻʻQ←∗ʻy⊂α) Df -/
def star_230_01 (F C : Set α) (I : α → Set α) (A : Set α) : Set α :=
  fun y => F y ∧ C y ∧ Included (I y) A
/-- ✱230·02. Q_cn=R̂α̂(∃!RQ̄_cn α) Df -/
def star_230_02 (A : Set α) : Prop := ∃ x, A x ∧ ∀ y, A y → y = x
theorem star_230_1 (F C : Set α) (I : α→Set α) : Convergent F C I A y↔F y∧C y∧Included (I y) A := Iff.rfl
theorem star_230_11 (A : Set α) : ExistsUnique A↔ExistsUnique A := Iff.rfl
theorem star_230_12 (h : ∀ x, A x → B x) : Included A B := fun x hx => h x hx
theorem star_230_13 (hAB : Included A B) (hBA : Included B A) : A=B := by
  funext x; exact propext ⟨hAB x, hBA x⟩
theorem star_230_131 (h : ∀ x, A x ↔ B x) : A=B := by funext x; exact propext (h x)
theorem star_230_14 (hA : ExistsUnique A) (hB : ExistsUnique B) : ExistsUnique A∧ExistsUnique B := ⟨hA,hB⟩
theorem star_230_141 (h : ∀x,¬A x) : A=fun _=>False := by funext x; exact propext ⟨fun hx=>(h x hx).elim,False.elim⟩
theorem star_230_142 (h : A=fun _=>False∨B=fun _=>False) (k : (A=fun _=>False∨B=fun _=>False)→C=fun _=>False) : C=fun _=>False := k h
theorem star_230_15 (hA : ExistsUnique A) (hB : ExistsUnique B) : ExistsUnique A∧ExistsUnique B := ⟨hA,hB⟩
theorem star_230_151 (hQ : P→Q) (hR : P→R) (hS : P→S) : P→Q∧R∧S :=
  fun hp => ⟨hQ hp, hR hp, hS hp⟩
theorem star_230_17 (P Q : Prop) (hnq : ¬Q→¬P) : P→Q := by
  intro hp; exact Classical.byContradiction fun hn => hnq hn hp
theorem star_230_171 (P Q : Prop) (h : P↔Q) : P→Q := h.mp
theorem star_230_211 (hab : Included A B) (h : ExistsUnique A) (lift : ExistsUnique A→Included A B→ExistsUnique B) : ExistsUnique B := lift h hab
end PM.Architecture.Star230OpeningKernel
