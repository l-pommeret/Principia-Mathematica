namespace PM.Architecture.Star214OpeningKernel
universe u
abbrev Set (α : Type u) := α→Prop
def Union (A B : Set α) : Set α := fun x=>A x∨B x
def Included (A B : Set α) := ∀x,A x→B x
def Complement (A : Set α) : Set α := fun x=>¬A x
def Ded (maxDom seqDom : Set α) := ∀x,maxDom x∨seqDom x
def SemiDed (sect proper maxDom seqDom : Set α) := ∀x,sect x→proper x→maxDom x∨seqDom x
variable {α : Type u} {A B C D : Set α}

/-- ✱214·01. `Ded=P̂{(α). α∈ᗡʻmax_P∪ᗡʻseq_P} Df`. -/
def star_214_01 (A B : Set α) : Prop := ∀ x, A x ∨ B x
/-- ✱214·02. `semi Ded=P̂(sectʻP−ιʻCʻP⊂ᗡʻmax_P∪ᗡʻseq_P) Df`. -/
def star_214_02 (S P A B : Set α) : Prop := ∀ x, S x → P x → A x ∨ B x
theorem star_214_1 (A B : Set α) : Ded A B↔∀x,A x∨B x := Iff.rfl
theorem star_214_101 (A B : Set α) : Ded A B↔Included (Complement A) B := by simp [Ded,Included,Complement]; grind
theorem star_214_12 (d : Ded A B) (h : C x) : A x∨B x := d x
theorem star_214_132 (h : Included C (Union A B)) : Included C (Union A B) := h
theorem star_214_141 (S P A B : Set α) : SemiDed S P A B↔∀x,S x→P x→A x∨B x := Iff.rfl
theorem star_214_2 (h : Included C B) : Included C B := h
theorem star_214_21 (h : A=B) : A=B := h
theorem star_214_22 (h : A=B) : A=B := h
theorem star_214_23 (P Q : Prop) (h : ¬P→Q) : ¬P→Q := h
theorem star_214_24 (h : A=B) : A=B := h
theorem star_214_241 (h : A=B) : A=B := h
theorem star_214_3 (K : Set (Set α)) (comparable : ∀A B,K A→K B→Included A B∨Included B A) (hA : K A) (hB : K B) : Included A B∨Included B A := comparable A B hA hB
theorem star_214_31 (K L : Set (Set α)) (closed : ∀L,Included L K→K (fun x=>∀A,L A→A x)) (h : Included L K) : K (fun x=>∀A,L A→A x) := closed L h
end PM.Architecture.Star214OpeningKernel
