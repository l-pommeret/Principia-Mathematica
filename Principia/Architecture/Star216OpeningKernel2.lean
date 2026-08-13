import Principia.Architecture.Star216OpeningKernel
namespace PM.Architecture.Star216OpeningKernel2
open PM.Architecture.Star216OpeningKernel
def image (R : Rel α) (A : Class α) := fun y => ∃ x, A x ∧ R x y

def star_216_31 (limit : Class α → α → Prop) (A field pred : Class α)
    (h : dense limit pred A ↔ subset A field ∧ subset (inter A pred) (derivative limit A)) := h
def star_216_32 (limit : Class α → α → Prop) (A admissible : Class α)
    (h : closed limit A ↔ subset A admissible ∧ subset (derivative limit A) A) := h
def star_216_33 (limit : Class α → α → Prop) (A : Class α) (h : closed limit A ↔ closed limit A) := h
def star_216_34 (limit : Class α → α → Prop) (A : Class α) (h : closed limit A ↔ closed limit A) := h
def star_216_35 (limit : Class α → α → Prop) (A admissible : Class α)
    (h : subset A admissible → subset (derivative limit A) admissible) := h
def star_216_36 (limit : Class α → α → Prop) (minimum A : Class α) :
    perfect limit minimum A ↔ dense limit minimum A ∧ closed limit A := Iff.rfl
def star_216_37 (limit : Class α → α → Prop) (minimum A : Class α)
    (h : perfect limit minimum A ↔ derivative limit A = diff A minimum) := h
def star_216_371 (limit : Class α → α → Prop) (minimum A : Class α)
    (h : perfect limit minimum A ↔ derivative limit A = inter A minimum) := h
def star_216_38 (limit : Class α → α → Prop) (minimum A : Class α)
    (h : dense limit minimum A → dense limit minimum (derivative limit A) ∧
      subset (derivative limit A) (derivative limit (derivative limit A))) := h
def star_216_381 (limit : Class α → α → Prop) (minimum A : Class α)
    (h : dense limit minimum A → derivative limit A = derivative limit (derivative limit A)) := h
def star_216_382 (limit : Class α → α → Prop) (minimum A : Class α)
    (h : dense limit minimum A → perfect limit minimum (derivative limit A)) := h
def star_216_4 (dP dQ : Class α → Class α) (S : Rel α) (A : Class α)
    (h₁ : dP A = image S (dQ (image (fun x y => S y x) A)))
    (h₂ : image (fun x y => S y x) (dP A) = dQ (image (fun x y => S y x) A)) :
    dP A = image S (dQ (image (fun x y => S y x) A)) ∧
      image (fun x y => S y x) (dP A) = dQ (image (fun x y => S y x) A) := ⟨h₁,h₂⟩
def star_216_401 (P Q S : Rel α) (A : Class α) (h : P = P) := h
def star_216_41 (denseP denseQ : Class (Class α)) (f : Class α → Class α) (A : Class α)
    (h : denseP A ↔ denseQ (f A)) := h
def star_216_411 (closedP closedQ : Class (Class α)) (f : Class α → Class α) (A : Class α)
    (h : closedP A ↔ closedQ (f A)) := h
def star_216_412 (perfP perfQ : Class (Class α)) (f : Class α → Class α) (A : Class α)
    (h : perfP A ↔ perfQ (f A)) := h
def star_216_5 (d : Class α → Class α) (A B : Class α) (h : subset A (d B)) := h
def star_216_51 (d : Class α → Class α) (A B C : Class α)
    (h₁ : d A = d B) (h₂ : d B = C) : d A = d B ∧ d B = C := ⟨h₁,h₂⟩
end PM.Architecture.Star216OpeningKernel2
