import Principia.FirstEdition.Volume1.Star14Source

namespace PM.Architecture.Star14Q297Kernel

/-- PM ✱14·02 read extensionally: the contextual description exists exactly
when the describing function has one value `b`, expressed in the printed
`φx ≡ₓ x = b` form. -/
def DescriptionExists (φ : α → Prop) : Prop :=
  ∃ b, ∀ x, φ x ↔ x = b

/-- PM ✱14·01 read extensionally: an assertion `ψ(℩x)(φx)` is the assertion
that some unique `b` satisfies the describing matrix and that `ψ b` holds.
The description is therefore never introduced as a total term. -/
def DescriptionApplies (φ ψ : α → Prop) : Prop :=
  ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b

/-- Exact semantic target of PM I ✱14·18:
`E!(℩x)(φx) ⊃ ((x)ψx ⊃ ψ(℩x)(φx))`. -/
theorem star_14_18 (φ ψ : α → Prop) :
    DescriptionExists φ → (∀ x, ψ x) → DescriptionApplies φ ψ := by
  rintro ⟨b, unique⟩ universal
  exact ⟨b, unique, universal b⟩

/-- Exact semantic target of PM I ✱14·21:
`ψ(℩x)(φx) ⊃ E!(℩x)(φx)`. -/
theorem star_14_21 (φ ψ : α → Prop) :
    DescriptionApplies φ ψ → DescriptionExists φ := by
  rintro ⟨b, unique, _⟩
  exact ⟨b, unique⟩

/-- The ✱14·18 result exposes precisely the unique witness used by the
contextual reduction, not a choice-created description term. -/
theorem star_14_18_witness (φ ψ : α → Prop)
    (existsDescription : DescriptionExists φ) (universal : ∀ x, ψ x) :
    ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b :=
  star_14_18 φ ψ existsDescription universal

/-- The reverse projection at ✱14·21 discards only the contextual predicate
proof and preserves the complete `φx ≡ₓ x = b` witness. -/
theorem star_14_21_witness (φ ψ : α → Prop)
    (application : DescriptionApplies φ ψ) :
    ∃ b, ∀ x, φ x ↔ x = b :=
  star_14_21 φ ψ application

end PM.Architecture.Star14Q297Kernel
