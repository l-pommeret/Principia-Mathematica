import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star22Q354Kernel

open PM.Architecture.Star22Q341Definitions

/-- PM I ✱22·65. -/
theorem star_22_65 (alpha beta gamma : Class Object) :
    Included alpha beta ∨ Included alpha gamma →
      Included alpha (Union beta gamma) := by
  rintro (hab | hag) x hx
  · exact Or.inl (hab x hx)
  · exact Or.inr (hag x hx)

/-- PM I ✱22·66. Union is monotone in its first operand. -/
theorem star_22_66 (alpha beta gamma : Class Object) :
    Included alpha beta → Included (Union alpha gamma) (Union beta gamma) := by
  intro hab x hx
  cases hx with
  | inl ha => exact Or.inl (hab x ha)
  | inr hg => exact Or.inr hg

/-- PM I ✱22·68, distribution of intersection over union. -/
theorem star_22_68 (alpha beta gamma : Class Object) :
    Union (Intersection alpha beta) (Intersection alpha gamma) =
      Intersection alpha (Union beta gamma) := by
  funext x
  apply propext
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hg⟩)
    · exact ⟨ha, Or.inl hb⟩
    · exact ⟨ha, Or.inr hg⟩
  · rintro ⟨ha, hb | hg⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hg⟩

/-- PM I ✱22·69, distribution of union over intersection. -/
theorem star_22_69 (alpha beta gamma : Class Object) :
    Intersection (Union alpha beta) (Union alpha gamma) =
      Union alpha (Intersection beta gamma) := by
  funext x
  apply propext
  constructor
  · rintro ⟨ha | hb, ha' | hg⟩
    · exact Or.inl ha
    · exact Or.inl ha
    · exact Or.inl ha'
    · exact Or.inr ⟨hb, hg⟩
  · rintro (ha | ⟨hb, hg⟩)
    · exact ⟨Or.inl ha, Or.inl ha⟩
    · exact ⟨Or.inr hb, Or.inr hg⟩

/-- PM I ✱22·7, associativity of union. -/
theorem star_22_7 (alpha beta gamma : Class Object) :
    Union (Union alpha beta) gamma = Union alpha (Union beta gamma) := by
  funext x
  apply propext
  constructor
  · rintro ((ha | hb) | hg)
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hg)
  · rintro (ha | hb | hg)
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr hb)
    · exact Or.inr hg

end PM.Architecture.Star22Q354Kernel
