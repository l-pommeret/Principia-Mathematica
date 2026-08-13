/-! # Principia Mathematica II, ✱202 — connected relations -/
namespace PM.FirstEdition.Volume2.Star202Source

abbrev Rel (α : Sort u) := α → α → Prop
def Field (R : Rel α) (x : α) : Prop := (∃ y, R x y) ∨ (∃ y, R y x)
def Connected (R : Rel α) : Prop :=
  ∀ x, Field R x → ∀ y, Field R y → x ≠ y → R x y ∨ R y x
def Symmetric (R : Rel α) : Prop := ∀ x y, R x y → R y x
def Asymmetric (R : Rel α) : Prop := ∀ x y, R x y → ¬ R y x
def Converse (R : Rel α) : Rel α := fun x y => R y x
def Union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
def Included (R S : Rel α) : Prop := ∀ x y, R x y → S x y

end PM.FirstEdition.Volume2.Star202Source
