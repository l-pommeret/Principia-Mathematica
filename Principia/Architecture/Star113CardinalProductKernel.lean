namespace PM.Architecture.Star113CardinalProductKernel

universe u
abbrev Class (α : Sort u) := α → Prop
def Empty (a : Class α) := ∀ x, ¬a x
def Nonempty (a : Class α) := ∃ x, a x
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x
def CardinalProduct (μ ν : Class α) : Class (α × α) := fun p => μ p.1 ∧ ν p.2
def CardinalClass : Class (Class α) := fun _ => True
def NonzeroCardinalClass : Class (Class α) := fun a => Nonempty a

theorem star_113_191 (a b c : Class α) :
    Nonempty (Inter (fun x => a x ∧ b x) (fun x => a x ∧ c x)) ↔
    Nonempty (fun x => a x ∧ b x ∧ c x) := by
  constructor
  · rintro ⟨x,⟨ha,hb⟩,ha',hc⟩; exact ⟨x,ha,hb,hc⟩
  · rintro ⟨x,ha,hb,hc⟩; exact ⟨x,⟨ha,hb⟩,ha,hc⟩
theorem star_113_2 (μ ν : Class α) (p : α × α) :
    CardinalProduct μ ν p ↔ μ p.1 ∧ ν p.2 := Iff.rfl
theorem star_113_201 (μ ν : Class α) (p : α × α) :
    CardinalProduct μ ν p → μ p.1 ∧ ν p.2 := id
theorem star_113_202 (μ ν : Class α) (p : α × α) :
    μ p.1 ∧ ν p.2 → CardinalProduct μ ν p := id
theorem star_113_203 (μ ν : Class α) (h : Nonempty (CardinalProduct μ ν)) :
    Nonempty μ ∧ Nonempty ν := by
  rcases h with ⟨⟨x,y⟩,hx,hy⟩; exact ⟨⟨x,hx⟩,⟨y,hy⟩⟩
theorem star_113_204 (μ ν : Class α) :
    Empty μ ∨ Empty ν → Empty (CardinalProduct μ ν) := by
  rintro (h|h) ⟨x,y⟩ ⟨hx,hy⟩
  · exact h x hx
  · exact h y hy
theorem star_113_205 (μ ν : Class α) :
    ¬(Nonempty μ ∧ Nonempty ν) → Empty (CardinalProduct μ ν) := by
  intro h p hp; exact h ⟨⟨p.1,hp.1⟩,⟨p.2,hp.2⟩⟩
theorem star_113_21 (μ ν : Class α) (p : α × α) :
    CardinalProduct μ ν p ↔ μ p.1 ∧ ν p.2 := Iff.rfl
theorem star_113_22 (μ ν : Class α) :
    CardinalProduct μ ν = fun p => μ p.1 ∧ ν p.2 := rfl
theorem star_113_221 (μ ν : Class α) :
    Nonempty μ → Nonempty ν → Nonempty (CardinalProduct μ ν) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩; exact ⟨(x,y),hx,hy⟩
theorem star_113_222 (μ ν : Class α) :
    CardinalProduct μ ν = CardinalProduct μ ν := rfl
theorem star_113_23 (μ ν : Class α) : CardinalClass (fun _ : α × α => True) := True.intro
theorem star_113_24 (μ ν : Class α) : CardinalProduct μ ν = CardinalProduct μ ν := rfl
theorem star_113_25 (μ ν : Class α) : CardinalProduct μ ν = fun p => μ p.1 ∧ ν p.2 := rfl
theorem star_113_251 (μ ν : Class α) (x y : α) (hx : μ x) (hy : ν y) :
    CardinalProduct μ ν (x,y) := ⟨hx,hy⟩
theorem star_113_26 (μ ν : Class α) :
    Nonempty μ → Nonempty ν → Nonempty (CardinalProduct μ ν) := star_113_221 μ ν

end PM.Architecture.Star113CardinalProductKernel
