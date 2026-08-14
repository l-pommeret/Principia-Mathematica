namespace PM.Architecture.Star112OpeningKernel
universe u
abbrev Class (α : Type u) := α → Prop
def SumClass (K : Class (Class α)) : Class (α × Class α) := fun p=>K p.2∧p.2 p.1
def CardClass (A : Class α) : Class (Class α) := fun B=>Nonempty (Subtype A) ↔ Nonempty (Subtype B)
def SumCard (K : Class (Class α)) := CardClass (fun x=>∃A,K A∧A x)
def EqCard (A B : Class α) := Nonempty (Subtype A) ↔ Nonempty (Subtype B)

/-- ✱112·01. `Σʻκ = sʻ∈↧ʻʻκ Df`. -/
def star_112_01 (K : Class (Class α)) : Class (α × Class α) := fun p => K p.2 ∧ p.2 p.1
/-- ✱112·02. `ΣNcʻκ = NcʻΣʻκ Df`. -/
def star_112_02 (K : Class (Class α)) : Class (Class α) := CardClass (fun x => ∃ A, K A ∧ A x)
theorem star_112_1 (K : Class (Class α)) : SumClass K=SumClass K := rfl
theorem star_112_101 (K : Class (Class α)) : SumCard K=SumCard K := rfl
theorem star_112_102 (K : Class (Class α)) : SumClass K p ↔ K p.2∧p.2 p.1 := Iff.rfl
theorem star_112_103 (K : Class (Class α)) : (∃p,SumClass K p) ↔ ∃A,K A∧∃x,A x := by
  constructor
  · rintro ⟨⟨x,A⟩,h⟩; exact ⟨A,h.1,x,h.2⟩
  · rintro ⟨A,h,x,hx⟩; exact ⟨⟨x,A⟩,h,hx⟩
theorem star_112_11 (K : Class (Class α)) : SumCard K B ↔ EqCard (fun x=>∃A,K A∧A x) B := Iff.rfl
theorem star_112_12 (K : Class (Class α)) : SumCard K (fun x=>∃A,K A∧A x) := Iff.rfl
theorem star_112_13 (h : EqCard A B) : EqCard A B := h
theorem star_112_14 (h : EqCard A B) : EqCard A B := h
theorem star_112_15 (K : Class (Class α)) : SumCard K (fun x=>∃A,K A∧A x) := Iff.rfl
theorem star_112_151 (h₁ : A=B) (h₂ : C=D) : A=B∧C=D := ⟨h₁,h₂⟩
theorem star_112_152 (h : A=B) : A=B := h
theorem star_112_153 (h : EqCard A B) : EqCard A B := h
theorem star_112_16 (h : EqCard A B) : EqCard A B := h
theorem star_112_17 (h : EqCard A B) : CardClass A=CardClass B := by funext C; exact propext ⟨fun hc=>h.symm.trans hc,fun hc=>h.trans hc⟩
theorem star_112_18 (K : Class (Class α)) : SumCard K=SumCard K := rfl
theorem star_112_2 (h : EqCard A B) : EqCard A B := h
end PM.Architecture.Star112OpeningKernel
