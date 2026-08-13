namespace PM.Architecture.Star121OpeningKernel
abbrev Rel (α : Type) := α → α → Prop
abbrev Class (α : Type) := α → Prop
def OpenInterval (P : Rel α) (x y : α) : Class α := fun z => P x z ∧ P z y
def LeftClosed (Ppo Pstar : Rel α) (x y : α) : Class α := fun z => Ppo x z ∧ Pstar z y
def RightClosed (Ppo Pstar : Rel α) (x y : α) : Class α := fun z => Pstar x z ∧ Ppo z y
def ClosedInterval (P : Rel α) (x y : α) : Class α := fun z => P x z ∧ P z y
def Level (rank : α → α → Nat) (n : Nat) : Rel α := fun x y => rank x y = n+1
def Finid (level : Nat → Rel α) : Rel α → Prop := fun R => ∃ n, R=level n
def Fin (level : Nat → Rel α) : Rel α → Prop := fun R => ∃ n, n>0 ∧ R=level n

theorem star_121_01 (P : Rel α) (x y : α) : OpenInterval P x y = fun z => P x z ∧ P z y := rfl
theorem star_121_011 (Ppo Pstar : Rel α) (x y : α) : LeftClosed Ppo Pstar x y = fun z => Ppo x z ∧ Pstar z y := rfl
theorem star_121_012 (Ppo Pstar : Rel α) (x y : α) : RightClosed Ppo Pstar x y = fun z => Pstar x z ∧ Ppo z y := rfl
theorem star_121_013 (P : Rel α) (x y : α) : ClosedInterval P x y = fun z => P x z ∧ P z y := rfl
theorem star_121_02 (rank : α → α → Nat) (n : Nat) : Level rank n = fun x y => rank x y=n+1 := rfl
theorem star_121_03 (level : Nat → Rel α) : Finid level = fun R => ∃ n, R=level n := rfl
theorem star_121_031 (level : Nat → Rel α) : Fin level = fun R => ∃ n, n>0 ∧ R=level n := rfl
theorem star_121_04 (P : α → β) (x : α) : P x=P x := rfl
theorem star_121_1 (P : Rel α) (x y z : α) : OpenInterval P x y z ↔ P x z ∧ P z y := Iff.rfl
theorem star_121_101 (Ppo Pstar : Rel α) (x y z : α) : LeftClosed Ppo Pstar x y z ↔ Ppo x z ∧ Pstar z y := Iff.rfl
theorem star_121_102 (Ppo Pstar : Rel α) (x y z : α) : RightClosed Ppo Pstar x y z ↔ Pstar x z ∧ Ppo z y := Iff.rfl
theorem star_121_103 (P : Rel α) (x y z : α) : ClosedInterval P x y z ↔ P x z ∧ P z y := Iff.rfl
theorem star_121_11 (rank : α → α → Nat) (n : Nat) (x y : α) : Level rank n x y ↔ rank x y=n+1 := Iff.rfl
theorem star_121_12 (level : Nat → Rel α) (R : Rel α) : Finid level R ↔ ∃ n, R=level n := Iff.rfl
theorem star_121_121 (level : Nat → Rel α) (R : Rel α) : Fin level R ↔ ∃ n, n>0 ∧ R=level n := Iff.rfl
end PM.Architecture.Star121OpeningKernel
