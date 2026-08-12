import Principia.Architecture.Star14Q299Kernel

namespace PM.Architecture.Star14Q303Kernel

open PM.Architecture.Star14Q299Kernel

/-- The binary characterization displayed at ✱14·123–124. -/
def CharacterizesPair (φ : α → β → Prop) (x : α) (y : β) : Prop :=
  ∀ z w, φ z w ↔ z = x ∧ w = y

/-- The complete right member of ✱14·124: existence of a value-pair together
with uniqueness of both coordinates. -/
def ExistsUniquePair (φ : α → β → Prop) : Prop :=
  (∃ x y, φ x y) ∧
    ∀ z w u v, φ z w → φ u v → z = u ∧ w = v

/-- PM I ✱14·124. A binary function has a characterizing ordered pair iff
it is inhabited and any two satisfying pairs agree coordinatewise. -/
theorem star_14_124 (φ : α → β → Prop) :
    (∃ x y, CharacterizesPair φ x y) ↔ ExistsUniquePair φ := by
  constructor
  · rintro ⟨x, y, characterizes⟩
    have hxy : φ x y := (characterizes x y).2 ⟨rfl, rfl⟩
    refine ⟨⟨x, y, hxy⟩, ?_⟩
    intro z w u v hzw huv
    have zw := (characterizes z w).1 hzw
    have uv := (characterizes u v).1 huv
    exact ⟨zw.1.trans uv.1.symm, zw.2.trans uv.2.symm⟩
  · rintro ⟨⟨x, y, hxy⟩, unique⟩
    refine ⟨x, y, ?_⟩
    intro z w
    constructor
    · intro hzw
      exact unique z w x y hzw hxy
    · rintro ⟨rfl, rfl⟩
      exact hxy

/-- Contextual reading of equality between two descriptions. Neither
description is made into a term: both candidates remain locally bound by
their unique-characterization witnesses. -/
def DescriptionIdentity (φ ψ : α → Prop) : Prop :=
  ∃ b c, Characterizes φ b ∧ Characterizes ψ c ∧ b = c

/-- PM I ✱14·131, symmetry of contextual-description identity. -/
theorem star_14_131 (φ ψ : α → Prop) :
    DescriptionIdentity φ ψ ↔ DescriptionIdentity ψ φ := by
  constructor <;>
    rintro ⟨b, c, hb, hc, equality⟩
  · exact ⟨c, b, hc, hb, equality.symm⟩
  · exact ⟨c, b, hc, hb, equality.symm⟩

end PM.Architecture.Star14Q303Kernel
