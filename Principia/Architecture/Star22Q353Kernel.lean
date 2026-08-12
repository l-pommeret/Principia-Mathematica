import Principia.Architecture.Star22Q341Definitions

/-!
# PM I ✱22·63–✱22·64

Exact extensional class proofs for the five absorption and inclusion
propositions printed on first-edition page 222.  The carrier remains an
arbitrary assigned object sort; no choice, decidability, or classical logic is
used.
-/

namespace PM.Architecture.Star22Q353Kernel

open PM.Architecture.Star22Q341Definitions

/-- PM I ✱22·63: union absorbs an intersection with its left operand. -/
theorem star_22_63 (alpha beta : Class Object) :
    Union alpha (Intersection alpha beta) = alpha := by
  funext x
  apply propext
  constructor
  · rintro (ha | ⟨ha, _⟩) <;> exact ha
  · intro ha
    exact Or.inl ha

/-- PM I ✱22·631: intersection absorbs a union with its left operand. -/
theorem star_22_631 (alpha beta : Class Object) :
    Intersection alpha (Union alpha beta) = alpha := by
  funext x
  apply propext
  constructor
  · rintro ⟨ha, _⟩
    exact ha
  · intro ha
    exact ⟨ha, Or.inl ha⟩

/-- PM I ✱22·632: equal classes give the displayed intersection identity. -/
theorem star_22_632 (alpha beta : Class Object) :
    alpha = beta → alpha = Intersection alpha beta := by
  intro hab
  subst beta
  funext x
  apply propext
  constructor
  · intro ha
    exact ⟨ha, ha⟩
  · rintro ⟨ha, _⟩
    exact ha

/-- PM I ✱22·633: replace an included left class by its intersection with
the including class, underneath the displayed union with `gamma`. -/
theorem star_22_633 (alpha beta gamma : Class Object) :
    Included alpha beta →
      Union alpha gamma = Union (Intersection alpha beta) gamma := by
  intro hab
  funext x
  apply propext
  constructor
  · rintro (ha | hg)
    · exact Or.inl ⟨ha, hab x ha⟩
    · exact Or.inr hg
  · rintro (⟨ha, _⟩ | hg)
    · exact Or.inl ha
    · exact Or.inr hg

/-- PM I ✱22·64: either displayed inclusion suffices to place the
intersection in `gamma`. -/
theorem star_22_64 (alpha beta gamma : Class Object) :
    Included alpha gamma ∨ Included beta gamma →
      Included (Intersection alpha beta) gamma := by
  rintro (hag | hbg) x ⟨ha, hb⟩
  · exact hag x ha
  · exact hbg x hb

end PM.Architecture.Star22Q353Kernel
