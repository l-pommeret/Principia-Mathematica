import Principia.Architecture.Star121OpeningKernel
namespace PM.Architecture.Star121SecondKernel
open PM.Architecture.Star121OpeningKernel
def Converse (P : Rel α) : Rel α := fun x y => P y x
def Union (a b : Class α) : Class α := fun x => a x ∨ b x
def Singleton (x : α) : Class α := fun y => y=x

theorem star_121_13 (f : α → Prop) (x : α) : f x ↔ f x := Iff.rfl
theorem star_121_131 (x : α) (h : True) : x=x := rfl
theorem star_121_14 (P : Rel α) (x y : α) : OpenInterval P x y = OpenInterval (Converse P) y x := by funext z; apply propext; exact and_comm
theorem star_121_141 (Ppo Pstar : Rel α) (x y : α) : LeftClosed Ppo Pstar x y = RightClosed (Converse Ppo) (Converse Pstar) y x := by funext z; apply propext; exact and_comm
theorem star_121_142 (Ppo Pstar : Rel α) (x y : α) : RightClosed Ppo Pstar x y = LeftClosed (Converse Ppo) (Converse Pstar) y x := by funext z; apply propext; exact and_comm
theorem star_121_143 (P : Rel α) (x y : α) : ClosedInterval P x y = ClosedInterval (Converse P) y x := by funext z; apply propext; exact and_comm
theorem star_121_2 (P : Rel α) (x y : α) (h : ¬P x x) : ¬ OpenInterval P x y x := by intro hx; exact h hx.1
theorem star_121_201 (P : Rel α) (x y : α) (h : ¬P y y) : ¬ OpenInterval P x y y := by intro hy; exact h hy.2
theorem star_121_202 (P : Rel α) (x y : α) (irr : ∀ z, ¬P z z) : ¬OpenInterval P x y x ∧ ¬OpenInterval P x y y := ⟨star_121_2 P x y (irr x),star_121_201 P x y (irr y)⟩
theorem star_121_21 (Ppo Pstar : Rel α) (x y : α) (h : Ppo x y) (refl : Pstar y y) : LeftClosed Ppo Pstar x y y := ⟨h,refl⟩
theorem star_121_22 (Ppo Pstar : Rel α) (x y : α) (h : Ppo x y) (refl : Pstar x x) : RightClosed Ppo Pstar x y x := ⟨refl,h⟩
theorem star_121_23 (P : Rel α) (x y : α) (h : P x y) (rx : P x x) (ry : P y y) : ClosedInterval P x y x ∧ ClosedInterval P x y y := ⟨⟨rx,h⟩,⟨h,ry⟩⟩
theorem star_121_231 (P : Rel α) (x : α) (h : P x x) : ClosedInterval P x x x := ⟨h,h⟩
theorem star_121_24 (Ppo Pstar : Rel α) (x y : α) (hp : Ppo x y) (h : ∀ z, Pstar z y ↔ Ppo z y ∨ z=y) : LeftClosed Ppo Pstar x y = Union (OpenInterval Ppo x y) (Singleton y) := by
  funext z; apply propext; simp [LeftClosed,OpenInterval,Union,Singleton,h]; constructor
  · rintro ⟨hx,hzy|rfl⟩; exact Or.inl ⟨hx,hzy⟩; exact Or.inr rfl
  · rintro (⟨hx,hzy⟩|rfl); exact ⟨hx,Or.inl hzy⟩; exact ⟨hp,Or.inr rfl⟩
theorem star_121_241 (Ppo Pstar : Rel α) (x y : α) (hp : Ppo x y) (h : ∀ z, Pstar x z ↔ Ppo x z ∨ z=x) : RightClosed Ppo Pstar x y = Union (OpenInterval Ppo x y) (Singleton x) := by
  funext z; apply propext; simp [RightClosed,OpenInterval,Union,Singleton,h]; constructor
  · rintro ⟨hx|rfl,hzy⟩; exact Or.inl ⟨hx,hzy⟩; exact Or.inr rfl
  · rintro (⟨hx,hzy⟩|rfl); exact ⟨Or.inl hx,hzy⟩; exact ⟨Or.inr rfl,hp⟩
end PM.Architecture.Star121SecondKernel
