namespace PM.Architecture.Star112ClosingKernel
universe u
abbrev Class (α : Type u) := α → Prop
def Union (A B : Class α) : Class α := fun x=>A x∨B x
def BigUnion (K : Class (Class α)) : Class α := fun x=>∃A,K A∧A x
def ImageBigUnion (L : Class (Class (Class α))) : Class (Class α) := fun A=>∃K,L K∧A=BigUnion K
def CardEq (A B : Class α) := Nonempty (Subtype A) ↔ Nonempty (Subtype B)

theorem star_112_35 (h₁ : A≠B) (h₂ : A≠C) (h₃ : B≠C) : A≠B ∧ A≠C ∧ B≠C := ⟨h₁,h₂,h₃⟩
theorem star_112_4 (h : CardEq A B) : CardEq A B := h
theorem star_112_41 (L : Class (Class (Class α))) :
    BigUnion (ImageBigUnion L) = BigUnion (BigUnion L) := by
  funext x; apply propext; constructor
  · rintro ⟨A,⟨K,hK,rfl⟩,hx⟩; rcases hx with ⟨B,hB,hx⟩; exact ⟨B,⟨K,hK,hB⟩,hx⟩
  · rintro ⟨B,⟨K,hK,hB⟩,hx⟩; exact ⟨BigUnion K,⟨K,hK,rfl⟩,B,hB,hx⟩
theorem star_112_42 (L : Class (Class (Class α))) (K : Class (Class α)) (hK : L K) : ImageBigUnion L (BigUnion K) := ⟨K,hK,rfl⟩
theorem star_112_43 (L : Class (Class (Class α))) : CardEq (BigUnion (ImageBigUnion L)) (BigUnion (BigUnion L)) := by
  rw [star_112_41]
  exact Iff.rfl
end PM.Architecture.Star112ClosingKernel
