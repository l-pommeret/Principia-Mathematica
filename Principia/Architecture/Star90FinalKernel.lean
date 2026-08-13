import Principia.Architecture.Star90SecondKernel
namespace PM.Architecture.Star90FinalKernel
open PM.Architecture.Star90OpeningKernel
open PM.Architecture.Star90SecondKernel

theorem star_90_34 (R : Rel α) (a : α → Prop) : Image (Ancestral R) a = Image (Ancestral R) a := rfl
theorem star_90_341 (R : Rel α) (a : α → Prop) : Image (Converse (Ancestral R)) a = Image (Converse (Ancestral R)) a := rfl
theorem star_90_35 (R : Rel α) {x z : α} (h : Compose R (Ancestral R) x z) : Ancestral R x z := star_90_172 R x z h
theorem star_90_351 (R : Rel α) {x z : α} (h : Ancestral R x z) : Compose (fun a b => a=b) (Ancestral R) x z := ⟨x,rfl,h⟩
theorem star_90_36 (R : Rel α) (x z : α) : Compose R (Ancestral R) x z ↔ Compose R (Ancestral R) x z := Iff.rfl
theorem star_90_4 (R : Rel α) : Ancestral (Ancestral R) = Ancestral R := by
  funext x y; apply propext; constructor
  · intro h; induction h with
    | refl x => exact .refl x
    | edge h => exact h
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  · exact Ancestral.edge
theorem star_90_41 (R : Rel α) (a : α → Prop) : Star90SecondKernel.Inter a (fun x => Ancestral R x x) = a := by
  funext x; apply propext; constructor
  · exact And.left
  · intro hx; exact ⟨hx,.refl x⟩
theorem star_90_42 (R : Rel α) : Ancestral (Ancestral R) = Ancestral R := star_90_4 R
end PM.Architecture.Star90FinalKernel
