import Principia.Architecture.Star14Q299Kernel

namespace PM.Architecture.Star14Q309Kernel

open PM.Architecture.Star14Q299Kernel

/-- Pointwise equivalent describing functions characterize exactly the same
candidate. This is local to the ✱14·272 proof and creates no description
term or choice operation. -/
private theorem characterizes_congr (φ ψ : α → Prop) (b : α)
    (extensional : ∀ x, φ x ↔ ψ x) :
    Characterizes φ b ↔ Characterizes ψ b := by
  constructor
  · intro characterizes x
    constructor
    · intro hψ
      exact (characterizes x).1 ((extensional x).2 hψ)
    · intro equality
      exact (extensional x).1 ((characterizes x).2 equality)
  · intro characterizes x
    constructor
    · intro hφ
      exact (characterizes x).1 ((extensional x).1 hφ)
    · intro equality
      exact (extensional x).2 ((characterizes x).2 equality)

/-- PM I ✱14·272. Pointwise equivalent describing functions give equivalent
contextual applications of the same continuation `χ`. Both description
candidates remain existentially scoped inside `DescriptionScope`. -/
theorem star_14_272 (φ ψ χ : α → Prop)
    (extensional : ∀ x, φ x ↔ ψ x) :
    DescriptionScope φ χ ↔ DescriptionScope ψ χ := by
  constructor
  · rintro ⟨b, characterizes, hχ⟩
    exact ⟨b, (characterizes_congr φ ψ b extensional).1 characterizes, hχ⟩
  · rintro ⟨b, characterizes, hχ⟩
    exact ⟨b, (characterizes_congr φ ψ b extensional).2 characterizes, hχ⟩

end PM.Architecture.Star14Q309Kernel
