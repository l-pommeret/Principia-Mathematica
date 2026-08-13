/-! # Principia Mathematica II, ✱103 — homogeneous-cardinal source model -/
namespace PM.FirstEdition.Volume2.Star103Source

abbrev Set' (α : Sort u) := α → Prop

def Equinumerous (s t : Set' α) : Prop :=
  ∃ f g : α → α,
    (∀ x, s x → t (f x)) ∧ (∀ y, t y → s (g y)) ∧
    (∀ x, s x → g (f x) = x) ∧ (∀ y, t y → f (g y) = y)

/-- ✱103·01. A homogeneous cardinal class. -/
def Homogeneous (K : Set' (Set' α)) : Prop :=
  ∀ s, K s → ∀ t, K t → Equinumerous s t

/-- ✱103·02. The cardinal class represented by a set. -/
def CardinalClass (s : Set' α) : Set' (Set' α) := fun t => Equinumerous s t

end PM.FirstEdition.Volume2.Star103Source
