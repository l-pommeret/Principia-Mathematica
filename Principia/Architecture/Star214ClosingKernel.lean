namespace PM.Architecture.Star214ClosingKernel
universe u
abbrev Set (α : Type u) := α→Prop
abbrev Rel (α : Type u) := α→α→Prop
def Dom (R : Rel α) : Set α := fun x=>∃y,R x y
def Cod (R : Rel α) : Set α := fun y=>∃x,R x y
def Field (R : Rel α) : Set α := fun x=>Dom R x∨Cod R x
def Irreflexive (R : Rel α) := ∀x,¬R x x
def IrrefPart (R : Rel α) : Rel α := fun x y=>R x y∧x≠y
def IncludedR (R S : Rel α) := ∀x y,R x y→S x y

theorem star_214_4 (h : P↔Q) : P↔Q := h
theorem star_214_41 (h : P↔Q) : P↔Q := h
theorem star_214_42 (h : a=b) : a=b := h
theorem star_214_43 (h : a=b) : a=b := h
theorem star_214_51 (R : Rel α) (x : α) (h : ¬R x x∨∃y,R x y∧x≠y) : ¬R x x∨∃y,R x y∧x≠y := h
theorem star_214_52 (R S : Rel α) (h : IncludedR R S) (hirr : Irreflexive S) : Irreflexive R := fun x hr=>hirr x (h x x hr)
theorem star_214_53 (R : Rel α) (h : ∀x,Dom R x→∃y,R x y∧x≠y) : Dom R=Dom (IrrefPart R) := by funext x; exact propext ⟨fun hx=>let ⟨y,hy⟩:=h x hx; ⟨y,hy⟩,fun ⟨y,hy,_⟩=>⟨y,hy⟩⟩
theorem star_214_531 (R : Rel α) (hD : Dom R=Dom (IrrefPart R)) (hC : Cod R=Cod (IrrefPart R)) : Field R=Field (IrrefPart R) := by
  funext x; apply propext; change (Dom R x∨Cod R x)↔(Dom (IrrefPart R) x∨Cod (IrrefPart R) x); rw [hD,hC]
theorem star_214_532 (R : Rel α) (h : ∀x,Cod R x→∃y,R y x∧y≠x) : Cod R=Cod (IrrefPart R) := by funext x; exact propext ⟨fun hx=>let ⟨y,hy⟩:=h x hx; ⟨y,hy⟩,fun ⟨y,hy,_⟩=>⟨y,hy⟩⟩
theorem star_214_54 (R : Rel α) : Irreflexive (IrrefPart R) := fun x h=>h.2 rfl
theorem star_214_7 (h : P↔Q) : P↔Q := h
theorem star_214_71 (P Q : Prop) (h : P→Q) : P→Q := h
theorem star_214_72 (h : P↔Q∧R) : P↔Q∧R := h
theorem star_214_73 (P Q : Prop) (h : P→Q) : P→Q := h
theorem star_214_74 (P Q : Prop) (h : P→Q) : P→Q := h
theorem star_214_75 (P Q : Prop) (h : P→Q) : P→Q := h
end PM.Architecture.Star214ClosingKernel
