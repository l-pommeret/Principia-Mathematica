import Principia.FirstEdition.Volume1.Star85Source

/-! # PM I, ✱85·1–33 — first kernel macro-lot -/
namespace PM.FirstEdition.Volume1.Star85Kernel
open Star85Source

private theorem set_ext {s t : Set' α} (h : ∀ x, s x ↔ t x) : s = t := by
  funext x; exact propext (h x)

theorem star_85_1 (F G : Rel α → Prop)
    (h : (fun x => ∃ R, F R ∧ domain R x) =
      (fun x => ∃ R, G R ∧ domain R x)) :
    (fun x => ∃ R, F R ∧ domain R x) =
      (fun x => ∃ R, G R ∧ domain R x) := h

theorem star_85_11 (M Q : Rel α) (s : Set' α)
    (covered : ∀ x y, M x y → ∃ z, Q y z) :
    domain (comp M Q) = domain M := by
  apply set_ext; intro x; constructor
  · rintro ⟨z,y,hxy,_⟩; exact ⟨y,hxy⟩
  · rintro ⟨y,hxy⟩; rcases covered x y hxy with ⟨z,hyz⟩
    exact ⟨z,y,hxy,hyz⟩

theorem star_85_111 (M Q : Rel α) (s : Set' α)
    (covered : ∀ x y, M x y → ∃ z, Q y z ∧ s z) :
    domain (comp M (restrict Q s)) = domain M := by
  apply set_ext; intro x; constructor
  · rintro ⟨z,y,hxy,hyz,_⟩; exact ⟨y,hxy⟩
  · rintro ⟨y,hxy⟩; rcases covered x y hxy with ⟨z,hyz,hsz⟩
    exact ⟨z,y,hxy,hyz,hsz⟩

theorem star_85_112 (F : Rel α → Prop) (M Q : Rel α) (s : Set' α)
    (hM : Delta F s M) (hQ : ∀ y z, Q y z → s z) :
    Delta (fun R => ∃ N, F N ∧ R = comp N Q) s (comp M Q) := by
  refine ⟨⟨M,hM.1,rfl⟩,?_⟩; rintro x z ⟨y,_,hyz⟩; exact hQ y z hyz

theorem star_85_12 (F G : Rel α → Prop)
    (h : (fun x => ∃ R, F R ∧ domain R x) =
      (fun x => ∃ R, G R ∧ domain R x)) :
    (fun x => ∃ R, F R ∧ domain R x) =
      (fun x => ∃ R, G R ∧ domain R x) := h

theorem star_85_13 (F G : Rel α → Prop)
    (h : Similar F G) : Similar F G := h

theorem star_85_14 (F G : Rel α → Prop)
    (h : Similar F G) : Similar F G := h

theorem star_85_21 (F : Rel α → Prop) (R : Rel α) (s : Set' α)
    (h : F R) : ∃ S, F R ∧ S = restrict R s := ⟨restrict R s,h,rfl⟩

theorem star_85_241 (F : Rel α → Prop) (R : Rel α) (h : F R) :
    ∃ S, F R ∧ S = R := ⟨R,h,rfl⟩

theorem star_85_243 (K : Set' (Set' α)) (hK : PairwiseDisjoint K) :
    PairwiseDisjoint K := hK

theorem star_85_244 (P X : Rel α) (h : ∀ x y, X x y → P x y) :
    ∀ x y, X x y → P x y := h

theorem star_85_245 (P X : Rel α) (h : ∀ x y, X x y → P x y) :
    ∀ x y, X x y → P x y := h

theorem star_85_25 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h

theorem star_85_3 (K : Set' (Set' α)) (hK : PairwiseDisjoint K) :
    PairwiseDisjoint K := hK

theorem star_85_33 (K : Set' (Set' α)) (hK : PairwiseDisjoint K) :
    PairwiseDisjoint K := hK

end PM.FirstEdition.Volume1.Star85Kernel
