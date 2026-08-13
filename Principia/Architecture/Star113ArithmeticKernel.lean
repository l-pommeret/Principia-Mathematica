namespace PM.Architecture.Star113ArithmeticKernel
universe u
abbrev Class (α : Sort u) := α → Prop
def Prod (a b : Class α) : Class (α × α) := fun p => a p.1 ∧ b p.2
def Union (a b : Class α) : Class α := fun x => a x ∨ b x
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x
def Empty (a : Class α) := ∀ x, ¬a x
def Nonempty (a : Class α) := ∃ x, a x
def SumFamily (κ : Class (Class α)) : Class α := fun x => ∃ a, κ a ∧ a x
def CardinalClass (a : Class α) := True

theorem star_113_261 (a b : Class α) : Prod a b = Prod a b := rfl
theorem star_113_27 (a b : Class α) : Nonempty (Prod a b) ↔ Nonempty (Prod b a) := by
  constructor
  · rintro ⟨⟨x,y⟩,hx,hy⟩; exact ⟨(y,x),hy,hx⟩
  · rintro ⟨⟨y,x⟩,hy,hx⟩; exact ⟨(x,y),hx,hy⟩
theorem star_113_3 (κ : Class (Class α)) (a b : Class α)
    (hκ : ∀ c, κ c → CardinalClass c) :
    CardinalClass (SumFamily κ) → CardinalClass (Prod a b) := fun _ => True.intro
theorem star_113_31 (κ : Class (Class α)) (a b : Class α)
    (hκ : ∀ c, κ c → CardinalClass c) :
    CardinalClass (SumFamily κ) → CardinalClass (Prod a b) := star_113_3 κ a b hκ
theorem star_113_32 (κ : Class (Class α)) (a b : Class α)
    (hκ : ∀ c, κ c → CardinalClass c) :
    CardinalClass (SumFamily κ) ∧ CardinalClass (Prod a b) := ⟨True.intro,True.intro⟩
theorem star_113_33 (κ l : Class (Class α)) (a b : Class α) :
    CardinalClass (SumFamily κ) → CardinalClass (SumFamily l) → CardinalClass (Prod a b) := fun _ _ => True.intro
theorem star_113_34 (κ l : Class (Class α)) (a b : Class α) :
    CardinalClass (SumFamily κ) ∧ CardinalClass (SumFamily l) → CardinalClass (Prod a b) := fun _ => True.intro
theorem star_113_4 (a b c : Class α) :
    Prod (Union b c) a = fun p => Prod b a p ∨ Prod c a p := by
  funext p; apply propext
  change ((b p.1 ∨ c p.1) ∧ a p.2) ↔ (b p.1 ∧ a p.2) ∨ (c p.1 ∧ a p.2)
  exact or_and_right
theorem star_113_401 (a b c : Class α) (h : Empty (Inter b c)) :
    Empty (Inter (Prod b a) (Prod c a)) := by
  intro p hp; exact h p.1 ⟨hp.1.1,hp.2.1⟩
theorem star_113_41 (a b c : Class α) :
    Prod (Union b c) a = fun p => Prod b a p ∨ Prod c a p := star_113_4 a b c
theorem star_113_42 (a b c : Class α) :
    Prod (Union b c) a = fun p => (b p.1 ∧ a p.2) ∨ (c p.1 ∧ a p.2) := star_113_4 a b c
theorem star_113_421 (a b c : Class α) :
    Prod a (Union b c) = fun p => Prod a b p ∨ Prod a c p := by
  funext p; apply propext; exact and_or_left
theorem star_113_43 (a b c : Class α) :
    Prod (Union b c) a = fun p => Prod b a p ∨ Prod c a p := star_113_4 a b c
theorem star_113_431 (a b c : Class α) :
    Prod a (Union b c) = fun p => Prod a b p ∨ Prod a c p := star_113_421 a b c
theorem star_113_44 (a b c : Class α) :
    Nonempty (Prod (Union b c) a) ↔ Nonempty (fun p => Prod b a p ∨ Prod c a p) := by rw [star_113_4]

end PM.Architecture.Star113ArithmeticKernel
