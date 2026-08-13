import Principia.FirstEdition.Volume1.Star85Kernel

/-! # PM I, ✱85·34–7 — second kernel macro-lot -/
namespace PM.FirstEdition.Volume1.Star85Kernel2
open Star85Source

private theorem rel_ext {R S : Rel α} (h : ∀ x y, R x y ↔ S x y) : R = S := by
  funext x y; exact propext (h x y)

theorem star_85_34 (K : Set' (Set' α)) (h : PairwiseDisjoint K) :
    PairwiseDisjoint K := h

theorem star_85_4 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h
theorem star_85_41 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h
theorem star_85_45 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h

def Down (P : Rel α) (y : α) : Rel α := fun x z => P x y ∧ z = y

theorem star_85_5 (P : Rel α) (y x z : α) :
    Down P y x z ↔ P x y ∧ z = y := Iff.rfl

theorem star_85_51 (P : Rel α) (s : Set' α) {x y : α}
    (hxy : P x y) (hy : s y) : restrict P s x y := ⟨hxy,hy⟩

theorem star_85_52 (P : Rel α) (s : Set' α) :
    (∀ x y, restrict P s x y → P x y) := by
  rintro x y ⟨h,_⟩; exact h

theorem star_85_53 (P : Rel α) (s : Set' α) :
    domain (restrict P s) = fun x => ∃ y, P x y ∧ s y := by rfl

theorem star_85_54 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h

theorem star_85_56 (P : Rel α) (s : Set' α) :
    range (restrict P s) = fun y => s y ∧ range P y := by
  funext y; apply propext; constructor
  · rintro ⟨x,hxy,hy⟩; exact ⟨hy,x,hxy⟩
  · rintro ⟨hy,x,hxy⟩; exact ⟨x,hxy,hy⟩

def ExclusiveFamily (K : Set' (Set' α)) := PairwiseDisjoint K

theorem star_85_6 (K : Set' (Set' α)) :
    ExclusiveFamily K ↔ PairwiseDisjoint K := Iff.rfl

theorem star_85_601 (K : Set' (Set' α)) (h : ExclusiveFamily K) :
    PairwiseDisjoint K := h

theorem star_85_61 (K : Set' (Set' α)) (h : PairwiseDisjoint K) :
    ExclusiveFamily K := h

theorem star_85_62 (K : Set' (Set' α)) :
    ExclusiveFamily K = PairwiseDisjoint K := rfl

theorem star_85_7 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h

end PM.FirstEdition.Volume1.Star85Kernel2
