/-! # Principia Mathematica I, ✱85 — source vocabulary -/
namespace PM.FirstEdition.Volume1.Star85Source

abbrev Set' (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z
def domain (R : Rel α) : Set' α := fun x => ∃ y, R x y
def range (R : Rel α) : Set' α := fun y => ∃ x, R x y
def restrict (R : Rel α) (s : Set' α) : Rel α := fun x y => R x y ∧ s y
def Delta (F : Rel α → Prop) (s : Set' α) (R : Rel α) : Prop :=
  F R ∧ ∀ x y, R x y → s y
def Similar (F G : Rel α → Prop) : Prop :=
  ∃ f : Rel α → Rel α, (∀ R, F R → G (f R)) ∧
    ∀ S, G S → ∃ R, F R ∧ f R = S
def PairwiseDisjoint (K : Set' (Set' α)) : Prop :=
  ∀ s, K s → ∀ t, K t → s ≠ t → ∀ x, ¬ (s x ∧ t x)

end PM.FirstEdition.Volume1.Star85Source
