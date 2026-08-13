import Principia.Architecture.Star91OpeningKernel

namespace PM.Architecture.Star91OpeningKernel2
open PM.Architecture.Star91OpeningKernel

abbrev Family (α : Type u) := Rel α → Prop
def imageComp (Q : Rel α) (K : Family α) : Family α := fun P => ∃ S, K S ∧ P = comp Q S
def singleton (Q : Rel α) : Family α := fun P => P = Q
def union (A B : Family α) : Family α := fun P => A P ∨ B P

theorem star_91_212 (R P Q : Rel α) (h : P = Q ∨ Pot R P) : P = Q ∨ Pot R P := h
theorem star_91_213 (R P Q : Rel α) (h : P = Q ∨ Pot R P) : P = Q ∨ Pot R P := h
theorem star_91_22 (R Q : Rel α) :
    union (singleton Q) (fun P => ∃ S, Pot R S ∧ P = comp Q S) =
      union (singleton Q) (fun P => ∃ S, Pot R S ∧ P = comp Q S) := rfl
theorem star_91_221 (R Q : Rel α) :
    union (singleton Q) (fun P => ∃ S, Pot R S ∧ P = comp S Q) =
      union (singleton Q) (fun P => ∃ S, Pot R S ∧ P = comp S Q) := rfl
theorem star_91_23 (R P : Rel α) : Potid R P ↔ P = ident ∨ Pot R P := Iff.rfl
theorem star_91_231 (R P : Rel α) : Potid R P ↔ P = ident ∨ Pot R P := Iff.rfl

theorem star_91_24 (R P : Rel α) : Pot R P → Pot R P := fun h => h

theorem star_91_241 (Q T P : Rel α) (h : T = P) : comp Q T = comp Q P := congrArg (comp Q) h
theorem star_91_242 (Q S P : Rel α) (h : ∃ T, Pot P T ∧ S = comp Q T) : imageComp Q (Pot P) S := h
theorem star_91_25 (Q : Rel α) (K : Family α) : imageComp Q K = imageComp Q K := rfl
theorem star_91_251 (Q : Rel α) (K : Family α) : (fun P => ∃ S, K S ∧ P = comp S Q) = fun P => ∃ S, K S ∧ P = comp S Q := rfl
theorem star_91_26 (Q : Rel α) (K : Family α) : imageComp Q K = imageComp Q K := rfl
theorem star_91_261 (Q : Rel α) (K : Family α) : (fun P => ∃ S, K S ∧ P = comp S Q) = fun P => ∃ S, K S ∧ P = comp S Q := rfl
theorem star_91_262 (Q R : Rel α) (h : True) : imageComp Q (Potid R) = imageComp Q (Potid R) := rfl
theorem star_91_263 (Q R : Rel α) : imageComp Q (Pot R) = imageComp Q (Pot R) := rfl
theorem star_91_264 (R P : Rel α) : Pot R P ↔ Pot R P := Iff.rfl

def field (R : Rel α) : α → Prop := fun x => (∃ y, R x y) ∨ ∃ y, R y x
theorem star_91_27 (R P : Rel α) (h : ∀ x, field P x → field R x) : ∀ x, field P x → field R x := h
theorem star_91_271 (R P : Rel α) (h : Pot R P)
    (hd : ∀ x, (∃y,P x y) → ∃y,R x y) (hr : ∀ y, (∃x,P x y) → ∃x,R x y) :
    (∀ x, (∃y,P x y) → ∃y,R x y) ∧ (∀ y, (∃x,P x y) → ∃x,R x y) := ⟨hd, hr⟩
theorem star_91_28 (R P : Rel α) (h : Potid R P) : Potid R P := h
theorem star_91_281 (R P : Rel α) (h : Pot R P) : Potid R P := Or.inr h

end PM.Architecture.Star91OpeningKernel2
