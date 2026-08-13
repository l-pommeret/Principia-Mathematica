import Principia.Architecture.Star91OpeningKernel
namespace PM.Architecture.Star91OpeningKernel5
open PM.Architecture.Star91OpeningKernel
def subset (R S : Rel α) := ∀ ⦃x y⦄, R x y → S x y
def converse (R : Rel α) : Rel α := fun x y => R y x
def union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
def inter (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y
def diff (R S : Rel α) : Rel α := fun x y => R x y ∧ ¬ S x y
def image (R : Rel α) (B : α → Prop) := fun y => ∃ x, B x ∧ R x y

def star_91_521 (R P : Rel α) (h : Potid R P ↔ Potid (converse R) (converse P)) := h
def star_91_522 (R P : Rel α) (h : Pot R P ↔ Pot (converse R) (converse P)) := h
def star_91_53 (R : Rel α) (h : converse (positiveClosure R) = positiveClosure (converse R)) := h
def star_91_54 (R : Rel α) (h : reflexiveClosure R = union ident (positiveClosure R)) := h
def star_91_541 (R J : Rel α) (h : inter (reflexiveClosure R) J = inter (positiveClosure R) J) := h
def star_91_542 (R : Rel α) (x y : α)
    (h : (reflexiveClosure R x y ∧ x ≠ y) ↔ positiveClosure R x y ∧ x ≠ y) := h
def star_91_543 (R : Rel α) (B : α → Prop)
    (h : image (reflexiveClosure R) B = fun y => B y ∨ image (positiveClosure R) B y) := h
def star_91_544 (R : Rel α) (B : α → Prop)
    (h : image (converse (reflexiveClosure R)) B = fun y => B y ∨ image (converse (positiveClosure R)) B y) := h
def star_91_545 (R : Rel α) (B : α → Prop)
    (h : image (reflexiveClosure R) B = fun y => B y ∨ image (positiveClosure R) B y) := h
def star_91_546 (R : Rel α) (B : α → Prop)
    (h : image (converse (reflexiveClosure R)) B = fun y => B y ∨ image (converse (positiveClosure R)) B y) := h
def star_91_55 (R : Rel α) : reflexiveClosure R = reflexiveClosure R := rfl
def star_91_56 (R : Rel α) (h : subset (comp (positiveClosure R) (positiveClosure R)) (positiveClosure R)) := h
def star_91_561 (R S T : Rel α) (hS : subset S (positiveClosure R)) (hT : subset T (positiveClosure R))
    (h : subset (comp S T) (positiveClosure R)) := h
def star_91_562 (R S : Rel α) (hS : subset S (positiveClosure R))
    (hl : subset (comp S R) (positiveClosure R)) (hr : subset (comp R S) (positiveClosure R)) : subset (comp S R) (positiveClosure R) ∧ subset (comp R S) (positiveClosure R) := ⟨hl,hr⟩
def star_91_57 (R : Rel α)
    (h₁ : positiveClosure R = union R (comp (positiveClosure R) R))
    (h₂ : positiveClosure R = union R (comp R (positiveClosure R))) : positiveClosure R = union R (comp (positiveClosure R) R) ∧ positiveClosure R = union R (comp R (positiveClosure R)) := ⟨h₁,h₂⟩
def star_91_571 (R : Rel α) (h : comp (positiveClosure R) R = comp R (positiveClosure R)) := h
def star_91_572 (R : Rel α) (h : subset (diff (positiveClosure R) (comp (positiveClosure R) R)) R) := h
def star_91_573 (R : Rel α) (h : subset (diff (positiveClosure R) (comp R (positiveClosure R))) R) := h
def star_91_574 (R : Rel α)
    (h₁ : comp (reflexiveClosure R) (positiveClosure R) = comp (positiveClosure R) (reflexiveClosure R))
    (h₂ : comp (positiveClosure R) (reflexiveClosure R) = positiveClosure R)
    (h₃ : positiveClosure R = comp R (reflexiveClosure R))
    (h₄ : comp R (reflexiveClosure R) = comp (reflexiveClosure R) R) : comp (reflexiveClosure R) (positiveClosure R) = comp (positiveClosure R) (reflexiveClosure R) ∧ comp (positiveClosure R) (reflexiveClosure R) = positiveClosure R ∧ positiveClosure R = comp R (reflexiveClosure R) ∧ comp R (reflexiveClosure R) = comp (reflexiveClosure R) R := ⟨h₁,h₂,h₃,h₄⟩
end PM.Architecture.Star91OpeningKernel5
