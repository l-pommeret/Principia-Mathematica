/-! # Principia Mathematica I, ✱82 — source vocabulary -/
namespace PM.FirstEdition.Volume1.Star82Source

abbrev Rel (α : Sort u) := α → α → Prop
abbrev Set' (α : Sort u) := α → Prop
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z
def cnv (R : Rel α) : Rel α := fun x y => R y x
def domain (R : Rel α) : Set' α := fun x => ∃ y, R x y
def image (R : Rel α) (s : Set' α) : Set' α := fun y => ∃ x, s x ∧ R x y
def restrict (R : Rel α) (s : Set' α) : Rel α := fun x y => R x y ∧ s y
def Functional (R : Rel α) : Prop := ∀ x y z, R x y → R x z → y = z
def Injective (R : Rel α) : Prop := Functional (cnv R)
def Delta (F : Rel α → Prop) (s : Set' α) (R : Rel α) : Prop :=
  F R ∧ ∀ x y, R x y → s y

end PM.FirstEdition.Volume1.Star82Source
