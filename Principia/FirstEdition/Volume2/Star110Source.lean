/-! # Principia Mathematica II, ✱110 — arithmetical sums -/
namespace PM.FirstEdition.Volume2.Star110Source

abbrev Set' (α : Type u) := α → Prop

structure Bijection (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

/-- ✱110·01. The disjoint (arithmetical) sum of two classes. -/
def SumClass (s : Set' α) (t : Set' β) : Set' (Sum α β)
  | .inl x => s x
  | .inr y => t y

/-- ✱110·02. Cardinal equivalence of classes. -/
def Equip (s : Set' α) (t : Set' β) : Prop :=
  Nonempty (Bijection {x // s x} {y // t y})

/-- ✱110·03. The cardinal represented by a class. -/
def Cardinal (s : Set' α) : (Type u) → Prop := fun γ => Nonempty (Bijection {x // s x} γ)

/-- ✱110·04. Cardinal addition, represented by disjoint sum. -/
def CardinalAdd (s : Set' α) (t : Set' β) := Cardinal (SumClass s t)

end PM.FirstEdition.Volume2.Star110Source
