import Principia.Architecture.Star21Q328Definitions

namespace PM.Architecture.Star21Q334Kernel

open PM.Architecture.Star21Q328Definitions

/-- PM I ✱21·2: reflexivity of a typed binary relation extension. -/
theorem star_21_2 (φ : RelationExtension α β) : φ = φ :=
  rfl

/-- PM I ✱21·21: symmetry of identity between typed relation extensions. -/
theorem star_21_21 (φ ψ : RelationExtension α β) :
    φ = ψ ↔ ψ = φ := by
  exact ⟨Eq.symm, Eq.symm⟩

/-- PM I ✱21·22: transitivity of identity between relation extensions. -/
theorem star_21_22 (φ ψ χ : RelationExtension α β) :
    φ = ψ → ψ = χ → φ = χ := by
  intro hφψ hψχ
  exact hφψ.trans hψχ

/-- PM I ✱21·23: two relations identical with the same left-hand relation
are identical with one another. -/
theorem star_21_23 (φ ψ χ : RelationExtension α β) :
    φ = ψ → φ = χ → ψ = χ := by
  intro hφψ hφχ
  exact hφψ.symm.trans hφχ

/-- PM I ✱21·24: two relations identical with the same right-hand relation
are identical with one another. -/
theorem star_21_24 (φ ψ χ : RelationExtension α β) :
    ψ = φ → χ = φ → ψ = χ := by
  intro hψφ hχφ
  exact hψφ.trans hχφ.symm

end PM.Architecture.Star21Q334Kernel
