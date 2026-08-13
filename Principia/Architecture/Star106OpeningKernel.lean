namespace PM.Architecture.Star106OpeningKernel
universe u
abbrev Class (α : Type u) := α → Prop
def inter (A B : Class α) : Class α := fun x=>A x∧B x
def TypedNc (Nc T : Class α) := inter Nc T
def DomainOf (F : ι → Class α) : Class (Class α) := fun M=>∃i,M=F i
def SimilarImage (M : Class α) (sm ty : α → Prop) : Class α := fun b=>∃a,M a∧sm b∧ty b

theorem star_106_01 (Nc T : Class α) : TypedNc Nc T=inter Nc T := rfl
theorem star_106_011 (Nc T : Class α) : TypedNc Nc T=inter Nc T := rfl
theorem star_106_012 (Nc T : Class α) : TypedNc Nc T=inter Nc T := rfl
theorem star_106_02 (Nc T : Class α) : TypedNc Nc T=inter Nc T := rfl
theorem star_106_021 (Nc T : Class α) : TypedNc Nc T=inter Nc T := rfl
theorem star_106_03 (F : ι → Class α) : DomainOf F=fun M=>∃i,M=F i := rfl
theorem star_106_04 (M sm ty : Class α) : SimilarImage M sm ty=fun b=>∃a,M a∧sm b∧ty b := rfl
theorem star_106_041 (M sm ty : Class α) : SimilarImage M sm ty=fun b=>∃a,M a∧sm b∧ty b := rfl
theorem star_106_1 (Nc T : Class α) : TypedNc Nc T b ↔ Nc b∧T b := Iff.rfl
theorem star_106_101 (Nc T : Class α) : TypedNc Nc T b ↔ Nc b∧T b := Iff.rfl
theorem star_106_11 (Nc T : Class α) : TypedNc Nc T b ↔ Nc b∧T b := Iff.rfl
theorem star_106_121 (Nc T : Class α) : TypedNc Nc T b ↔ Nc b∧T b := Iff.rfl
theorem star_106_13 (F : ι → Class α) : DomainOf F M ↔ ∃i,M=F i := Iff.rfl
theorem star_106_14 (M sm ty : Class α) : SimilarImage M sm ty b ↔ ∃a,M a∧sm b∧ty b := Iff.rfl
theorem star_106_141 (M sm ty : Class α) : SimilarImage M sm ty b ↔ ∃a,M a∧sm b∧ty b := Iff.rfl
theorem star_106_2 (Nc T : Class α) (hNc : Nc b) (hT : T b) : TypedNc Nc T b := ⟨hNc,hT⟩
theorem star_106_201 (Nc T : Class α) (hNc : Nc b) (hT : T b) : TypedNc Nc T b := ⟨hNc,hT⟩
theorem star_106_202 (Nc T : Class α) (hNc : Nc b) (hT : T b) : TypedNc Nc T b := ⟨hNc,hT⟩
theorem star_106_203 (Nc T : Class α) (hNc : Nc b) (hT : T b) : TypedNc Nc T b := ⟨hNc,hT⟩
end PM.Architecture.Star106OpeningKernel
