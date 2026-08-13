/-! # Principia Mathematica II, ✱211 — sections and segments -/
namespace PM.FirstEdition.Volume2.Star211Source

abbrev Set' (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
def Included (s t : Set' α) : Prop := ∀ x, s x → t x
def Image (R : Rel α) (s : Set' α) : Set' α := fun y => ∃ x, s x ∧ R x y
def ConverseImage (R : Rel α) (s : Set' α) : Set' α := fun x => ∃ y, s y ∧ R x y
def Field (R : Rel α) : Set' α := fun x => (∃ y, R x y) ∨ (∃ y, R y x)

/-- ✱211·01. A section is a field-subclass closed under predecessors. -/
def Section (R : Rel α) (s : Set' α) : Prop :=
  Included s (Field R) ∧ Included (Image R s) s

def Segment (R : Rel α) (a : α) : Set' α := fun x => R a x

end PM.FirstEdition.Volume2.Star211Source
