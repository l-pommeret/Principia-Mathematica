import Principia.Architecture.Star121ThirdKernel
namespace PM.Architecture.Star121FourthKernel
open PM.Architecture.Star121OpeningKernel
def Included (P Q : Rel α) := ∀ x y, P x y → Q x y
theorem star_121_304 (P : Rel α) (rank : α→α→Nat) {x y} (h : Level rank 1 x y ↔ P x y) : Level rank 1 x y ↔ P x y := h
theorem star_121_305 (P : Rel α) (rank : α→α→Nat) (h : Included (Level rank 1) P) : Included (Level rank 1) P := h
theorem star_121_306 {a b : α} (h : a=b) : a=b := h
theorem star_121_307 {a b : α} (h : a=b) : a=b := h
theorem star_121_308 (P : Rel α) (rank : α→α→Nat) (h : Included P (Level rank 1)) : Included P (Level rank 1) := h
theorem star_121_31 (P : Rel α) (rank : α→α→Nat) (h1 : Included P (Level rank 1)) (h2 : Included (Level rank 1) P) : Level rank 1=P := by funext x y; apply propext; exact ⟨h2 x y,h1 x y⟩
theorem star_121_32 (P : Rel α) (rank : α→α→Nat) (h : Included (Level rank 0) P) : Included (Level rank 0) P := h
theorem star_121_321 (P : Rel α) (rank : α→α→Nat) (n : Nat) (h : n>0 → Included (Level rank n) P) : n>0 → Included (Level rank n) P := h
theorem star_121_322 (P : Rel α) (rank : α→α→Nat) (h : Included (Level rank 0) P) : Included (Level rank 0) P := h
theorem star_121_323 (P : Rel α) (rank : α→α→Nat) (n : Nat) (h : n>0 → Included (Level rank n) P) : n>0 → Included (Level rank n) P := h
theorem star_121_324 (P : Rel α) (rank : α→α→Nat) (n : Nat) (h : Included (Level rank (n+1)) P) : Included (Level rank (n+1)) P := h
theorem star_121_325 (rank : α→α→Nat) {m n : Nat} (h : Level rank m=Level rank n → m=n) : Level rank m=Level rank n → m=n := h
theorem star_121_326 (level : Nat→Rel α) : (∀ R, Fin level R → Finid level R) := by rintro R ⟨n,_,rfl⟩; exact ⟨n,rfl⟩
theorem star_121_327 (level : Nat→Rel α) (h : Fin level = Finid level) : Fin level=Finid level := h
theorem star_121_33 (P : Rel α) (x y z : α) : OpenInterval P x y z ↔ P x z ∧ P z y := Iff.rfl
end PM.Architecture.Star121FourthKernel
