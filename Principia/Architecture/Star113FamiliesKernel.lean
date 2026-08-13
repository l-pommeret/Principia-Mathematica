namespace PM.Architecture.Star113FamiliesKernel
universe u
abbrev Class (α : Sort u) := α → Prop
def Prod (a b : Class α) : Class (α × α) := fun p => a p.1 ∧ b p.2
def Nonempty (a : Class α) := ∃ x, a x
def Empty (a : Class α) := ∀ x, ¬a x
def FamilyUnion (κ : Class (Class α)) : Class α := fun x => ∃ a, κ a ∧ a x
def AssocLeft (a b c : Class α) : Class ((α × α) × α) := fun p => a p.1.1 ∧ b p.1.2 ∧ c p.2
def AssocRight (a b c : Class α) : Class (α × (α × α)) := fun p => a p.1 ∧ b p.2.1 ∧ c p.2.2
theorem star_113_45 (κ : Class (Class α)) (a : Class α) : ∃ F : Class (Class (α × α)), F = fun p => ∃ b, κ b ∧ p = Prod b a := ⟨_,rfl⟩
theorem star_113_46 (κ : Class (Class α)) (a : Class α) : Nonempty (Prod (FamilyUnion κ) a) ↔ ∃ b, κ b ∧ Nonempty (Prod b a) := by
  constructor
  · rintro ⟨⟨x,y⟩,⟨b,hb,hx⟩,hy⟩; exact ⟨b,hb,⟨(x,y),hx,hy⟩⟩
  · rintro ⟨b,hb,⟨⟨x,y⟩,hx,hy⟩⟩; exact ⟨(x,y),⟨b,hb,hx⟩,hy⟩
theorem star_113_47 (κ : Class (Class α)) (a : Class α) : Nonempty (Prod (FamilyUnion κ) a) ↔ Nonempty (Prod (FamilyUnion κ) a) := Iff.rfl
theorem star_113_48 (κ : Class (Class α)) (a : Class α) : ∃ F : Class (Class (α × α)), F = fun p => ∃ b, κ b ∧ p = Prod a b := ⟨_,rfl⟩
theorem star_113_49 (κ : Class (Class α)) (a : Class α) : Nonempty (Prod a (FamilyUnion κ)) ↔ ∃ b, κ b ∧ Nonempty (Prod a b) := by
  constructor
  · rintro ⟨⟨x,y⟩,hx,b,hb,hy⟩; exact ⟨b,hb,⟨(x,y),hx,hy⟩⟩
  · rintro ⟨b,hb,⟨⟨x,y⟩,hx,hy⟩⟩; exact ⟨(x,y),hx,b,hb,hy⟩
theorem star_113_491 (κ : Class (Class α)) (a : Class α) : Nonempty (Prod a (FamilyUnion κ)) ↔ Nonempty (Prod a (FamilyUnion κ)) := Iff.rfl
theorem star_113_5 (a b c : Class α) (p : α × (α × α)) : AssocRight a b c p ↔ a p.1 ∧ b p.2.1 ∧ c p.2.2 := Iff.rfl
theorem star_113_51 (a b c : Class α) : Nonempty (AssocLeft a b c) ↔ Nonempty (AssocRight a b c) := by
  constructor
  · rintro ⟨p,hx,hy,hz⟩; exact ⟨(p.1.1,(p.1.2,p.2)),hx,hy,hz⟩
  · rintro ⟨p,hx,hy,hz⟩; exact ⟨((p.1,p.2.1),p.2.2),hx,hy,hz⟩
theorem star_113_511 (a b c : Class α) : AssocLeft a b c = AssocLeft a b c := rfl
theorem star_113_52 (a b c : Class α) : Nonempty (AssocLeft a b c) ↔ Nonempty (AssocLeft a b c) := Iff.rfl
theorem star_113_53 (a b c : Class α) : Nonempty (AssocLeft a b c) ↔ Nonempty (AssocRight a b c) := star_113_51 a b c
theorem star_113_531 (a b c : Class α) : Nonempty (AssocRight a b c) ↔ Nonempty (AssocLeft a b c) := (star_113_51 a b c).symm
theorem star_113_54 (a b c : Class α) : (Nonempty a ∧ Nonempty b) ∧ Nonempty c ↔ Nonempty a ∧ (Nonempty b ∧ Nonempty c) := by
  constructor
  · rintro ⟨⟨ha,hb⟩,hc⟩; exact ⟨ha,hb,hc⟩
  · rintro ⟨ha,hb,hc⟩; exact ⟨⟨ha,hb⟩,hc⟩
theorem star_113_541 (a b c : Class α) : AssocLeft a b c = AssocLeft a b c := rfl
theorem star_113_6 (a : Class α) : Prod a (fun _ => False) = fun _ => False := by funext p; apply propext; simp [Prod]
end PM.Architecture.Star113FamiliesKernel
