import Principia.Architecture.Star121SecondKernel
namespace PM.Architecture.Star121ThirdKernel
open PM.Architecture.Star121OpeningKernel
open PM.Architecture.Star121SecondKernel
theorem star_121_242 (P : Rel α) (x y : α) (h : ClosedInterval P x y = ClosedInterval P x y) : ClosedInterval P x y = ClosedInterval P x y := h
theorem star_121_25 (P : Rel α) (x y : α) : OpenInterval P x y=OpenInterval P x y := rfl
theorem star_121_251 (P Q : Rel α) (x y : α) : LeftClosed P Q x y=LeftClosed P Q x y := rfl
theorem star_121_252 (P Q : Rel α) (x y : α) : RightClosed P Q x y=RightClosed P Q x y := rfl
theorem star_121_253 (P : Rel α) (x y : α) : ClosedInterval P x y=ClosedInterval P x y := rfl
theorem star_121_254 (rank : α → α → Nat) (n : Nat) : Level rank n=Level rank n := rfl
theorem star_121_26 (P : Rel α) : Converse P=Converse P := rfl
theorem star_121_27 (rank : α → α → Nat) (n : Nat) {x y} (h : Level rank n x y) : rank x y=n+1 := h
theorem star_121_271 (rank : α → α → Nat) (n : Nat) (h : ∀ x y, rank x y≠n+1) : Level rank n=fun _ _ => False := by funext x y; apply propext; simp [Level,h]
theorem star_121_272 (n : Nat) : n≥0 ∧ n+1>0 ∧ n+1≥1 := by omega
theorem star_121_273 (n : Nat) : n+1>0 := by omega
theorem star_121_3 (rank : α → α → Nat) : (∀ x y, Level rank 0 x y → x=y) → (∀ x y, Level rank 0 x y → x=y) := id
theorem star_121_301 (rank : α → α → Nat) (x y : α) (h : Level rank 0 x y ↔ x=y) : Level rank 0 x y ↔ x=y := h
theorem star_121_302 (rank : α → α → Nat) (h : Level rank 0 = fun x y => x=y) : Level rank 0=fun x y => x=y := h
theorem star_121_303 (P : Rel α) (rank : α → α → Nat) {x y} (h : rank x y>1 → P x y) : rank x y>1 → P x y := h
end PM.Architecture.Star121ThirdKernel
