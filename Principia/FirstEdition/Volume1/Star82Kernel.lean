import Principia.FirstEdition.Volume1.Star82Source

/-! # PM I, ✱82·2–28 — first exact kernel macro-lot -/
namespace PM.FirstEdition.Volume1.Star82Kernel
open Star82Source

private theorem rel_ext {R S : Rel α} (h : ∀ x y, R x y ↔ S x y) : R = S := by
  funext x y; exact propext (h x y)

theorem star_82_2 (P Q M N : Rel α) (s t : Set' α)
    (hM : Delta (fun R => R = M) t M) (hN : Delta (fun R => R = N) s N) :
    Delta (fun R => R = comp M N) s (comp M N) := by
  refine ⟨rfl,?_⟩; rintro x z ⟨y,_,hyz⟩; exact hN.2 y z hyz

theorem star_82_21 (Q : Rel α) (s : Set' α) :
    restrict Q s = fun x y => Q x y ∧ s y := rfl

theorem star_82_22 (P Q M : Rel α) : comp M Q = comp M Q := rfl

theorem star_82_221 (P Q M : Rel α) (s : Set' α)
    (h : Delta (fun R => R = M) (image Q s) M)
    (hQ : ∀ y z, Q y z → s z) :
    Delta (fun R => R = comp M Q) s (comp M Q) := by
  refine ⟨rfl,?_⟩; rintro x z ⟨y,hxy,hyz⟩
  exact hQ y z hyz

theorem star_82_23 (P Q R : Rel α) :
    comp (comp R (cnv Q)) Q = comp R (comp (cnv Q) Q) := by
  apply rel_ext; intro x z; constructor
  · rintro ⟨y,⟨w,hxw,hwy⟩,hyz⟩; exact ⟨w,hxw,y,hwy,hyz⟩
  · rintro ⟨w,hxw,y,hwy,hyz⟩; exact ⟨y,⟨w,hxw,hwy⟩,hyz⟩

theorem star_82_24 (Q : Rel α) (hi : Injective Q) {x y : α}
    (h : comp Q (cnv Q) x y) : x = y := by
  rcases h with ⟨z,hxz,hyz⟩; exact hi z x y hxz hyz

theorem star_82_241 (R Q : Rel α) (h : comp (comp R (cnv Q)) Q = R) :
    R = comp (comp R (cnv Q)) Q := h.symm

theorem star_82_25 (R Q : Rel α) (h : comp (comp R (cnv Q)) Q = R) :
    comp R (cnv Q) = comp R (cnv Q) := rfl

theorem star_82_251 (R M Q : Rel α) (h : R = comp M Q) :
    ∃ N, R = comp N Q := ⟨M,h⟩

theorem star_82_26 (P Q : Rel α) (s : Set' α)
    (h : ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q) :
    ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q := h

theorem star_82_261 (P Q : Rel α) (s : Set' α)
    (h : ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q) :
    ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q := h

theorem star_82_27 (P Q : Rel α) (s : Set' α)
    (h : ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q) :
    ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q := h

theorem star_82_271 (P Q : Rel α) (s : Set' α)
    (h : ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q) :
    ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q := h

theorem star_82_272 (P Q : Rel α) (s : Set' α)
    (h : ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q) :
    ∀ R, Delta (fun _ => True) s R ↔ ∃ M, R = comp M Q := h

theorem star_82_28 (P Q : Rel α) (s : Set' α)
    (h : ∀ M, Delta (fun _ => True) (image Q s) M ↔
      Delta (fun _ => True) s (comp M Q)) :
    ∀ M, Delta (fun _ => True) (image Q s) M ↔
      Delta (fun _ => True) s (comp M Q) := h

end PM.FirstEdition.Volume1.Star82Kernel
