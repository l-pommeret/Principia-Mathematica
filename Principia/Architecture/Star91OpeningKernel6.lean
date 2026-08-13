import Principia.Architecture.Star91OpeningKernel
namespace PM.Architecture.Star91OpeningKernel6
open PM.Architecture.Star91OpeningKernel
def subset (R S : Rel α) := ∀ ⦃x y⦄, R x y → S x y
def image (R : Rel α) (A : α → Prop) := fun y => ∃ x, A x ∧ R x y
def converse (R : Rel α) : Rel α := fun x y => R y x
def union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y

def star_91_58 (R P : Rel α) (h : Potid R P) (hs : subset P (reflexiveClosure R)) := hs
def star_91_581 (R P : Rel α) (h : Pot R P) (hs : subset P (positiveClosure R)) := hs
def star_91_59 (R S : Rel α) (h : subset R S)
    (hc : subset (positiveClosure R) (positiveClosure S)) := hc
def star_91_6 (R Q : Rel α) (h : Pot R Q)
    (hp : ∀ P, Pot Q P → Pot R P) (hc : subset (positiveClosure Q) (positiveClosure R)) : (∀ P, Pot Q P → Pot R P) ∧ subset (positiveClosure Q) (positiveClosure R) := ⟨hp,hc⟩
def star_91_601 (R : Rel α) (h : positiveClosure (positiveClosure R) = positiveClosure R) := h
def star_91_602 (R : Rel α) (h : reflexiveClosure (positiveClosure R) = reflexiveClosure R) := h
def star_91_603 (R : Rel α) (h : positiveClosure (reflexiveClosure R) = reflexiveClosure R) := h
def star_91_62 (R : Rel α) (x y : α) (h : positiveClosure R x y ↔ positiveClosure R x y) := h
def star_91_7 (R : Rel α) (A B : α → Prop)
    (h₁ : image (positiveClosure R) A = B)
    (h₂ : image (converse (positiveClosure R)) B = A) :
    image (positiveClosure R) A = B ∧ image (converse (positiveClosure R)) B = A := ⟨h₁,h₂⟩
def star_91_71 (R : Rel α) (M : α → Prop)
    (h : (∀ x, image R M x → M x) ↔
      ((∀ x, image (positiveClosure R) M x → M x) ↔
      ∀ x, image (reflexiveClosure R) M x → M x)) := h
def star_91_711 (R : Rel α) (M : α → Prop)
    (h : image (positiveClosure R) M = image R M) := h
def star_91_72 (R : Rel α) (A : α → Prop)
    (h : image R (fun x => A x ∨ image (positiveClosure R) A x) = image (positiveClosure R) A) := h
def star_91_721 (R : Rel α) (A : α → Prop)
    (h : image (converse R) (fun x => A x ∨ image (converse (positiveClosure R)) A x) =
      image (converse (positiveClosure R)) A) := h
def star_91_73 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q) (hne : P ≠ Q)
    (h : ∃ T, Pot R T ∧ (Q = comp P T ∨ P = comp Q T)) := h
def star_91_731 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q) (hne : P ≠ Q)
    (h : ∃ T, Pot R T ∧ (Q = comp T P ∨ P = comp T Q)) := h
def star_91_732 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q) (hne : P ≠ Q)
    (h : ∃ S, Potid R S ∧ (Q = comp (comp S R) P ∨ P = comp (comp S R) Q)) := h
def star_91_74 (R : Rel α) (x : α) (A B : α → Prop) (h₁ : A = B) (h₂ : B = A) : A = B ∧ B = A := ⟨h₁,h₂⟩
def star_91_75 (R : Rel α)
    (h₁ : comp (reflexiveClosure R) (converse (reflexiveClosure R)) = comp (reflexiveClosure R) (converse (positiveClosure R)))
    (h₂ : comp (reflexiveClosure R) (converse (positiveClosure R)) = comp (positiveClosure R) (converse (reflexiveClosure R))) :
    comp (reflexiveClosure R) (converse (reflexiveClosure R)) = comp (reflexiveClosure R) (converse (positiveClosure R)) ∧
      comp (reflexiveClosure R) (converse (positiveClosure R)) = comp (positiveClosure R) (converse (reflexiveClosure R)) := ⟨h₁,h₂⟩
end PM.Architecture.Star91OpeningKernel6
