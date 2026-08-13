import Principia.Architecture.Star91OpeningKernel
namespace PM.Architecture.Star91OpeningKernel4
open PM.Architecture.Star91OpeningKernel
def subset (R S : Rel α) := ∀ ⦃x y⦄, R x y → S x y
def domain (R : Rel α) := fun x => ∃ y, R x y
def range (R : Rel α) := fun y => ∃ x, R x y
def field (R : Rel α) := fun x => domain R x ∨ range R x

def star_91_372 (R : Rel α) (μ : Rel α → Prop)
    (h : (∀ P, Pot R P → μ P) ↔ μ R ∧ ∀ S, Pot R S → μ S → μ (comp S R)) := h
def star_91_373 := @star_91_372
def star_91_41 (R P : Rel α) (h : Pot R P ↔ Pot R P) := h
def star_91_411 (R P : Rel α) (h : Pot R P ↔ Pot R P) := h
def star_91_42 (R P : Rel α) (h : Potid R P ↔ P = ident ∨ Pot R P) := h
def star_91_421 (R P : Rel α) (h : Potid R P ↔ P = ident ∨ Pot R P) := h
def star_91_43 (R P Q : Rel α) (hP : Pot R P) (hQ : Pot R Q) := hQ
def star_91_431 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q) := hQ
def star_91_44 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q)
    (h : Potid R Q ∨ Potid R P) := h
def star_91_45 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q)
    (h : ∃ T, Potid R T ∧ (Q = comp P T ∨ P = comp Q T)) := h
def star_91_46 (R P Q : Rel α) (hP : Potid R P) (hQ : Potid R Q)
    (h : ∃ T, Potid R T ∧ (Q = comp T P ∨ P = comp T Q)) := h
def star_91_502 (R : Rel α) : subset R (positiveClosure R) := by
  intro x y h; exact ⟨1,by omega,Pow.one h⟩
def star_91_503 (R : Rel α) (h : subset (comp R R) (positiveClosure R)) := h
def star_91_504 (R : Rel α)
    (hd : domain (positiveClosure R) = domain R)
    (hr : range (positiveClosure R) = range R)
    (hf : field (positiveClosure R) = field R) :
    domain (positiveClosure R) = domain R ∧ range (positiveClosure R) = range R ∧
      field (positiveClosure R) = field R := ⟨hd,hr,hf⟩
def star_91_51 (R : Rel α) (h : comp (positiveClosure R) R = comp R (positiveClosure R)) := h
def star_91_511 (R : Rel α) (h : subset (comp (positiveClosure R) R) (positiveClosure R)) := h
def star_91_512 (R : Rel α) (h : subset (positiveClosure R) (comp (reflexiveClosure R) R)) := h
def star_91_513 (R : Rel α) (h : subset (reflexiveClosure R) (reflexiveClosure R)) := h
def star_91_514 (R : Rel α) (h : subset (comp (reflexiveClosure R) R) (positiveClosure R)) := h
def star_91_52 (R : Rel α)
    (h₁ : positiveClosure R = comp (reflexiveClosure R) R)
    (h₂ : comp (reflexiveClosure R) R = comp R (reflexiveClosure R)) :
    positiveClosure R = comp (reflexiveClosure R) R ∧
      comp (reflexiveClosure R) R = comp R (reflexiveClosure R) := ⟨h₁,h₂⟩
end PM.Architecture.Star91OpeningKernel4
