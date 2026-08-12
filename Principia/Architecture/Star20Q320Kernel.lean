import Principia.Architecture.Star20Q314Definitions

namespace PM.Architecture.Star20Q320Kernel

open PM.Architecture.Star20Q314Definitions

/-- Equality of class extensions, kept eliminative as pointwise formal
equivalence of their defining matrices. No class-valued term is introduced. -/
def ClassEquivalent (φ ψ : Matrix α) : Prop :=
  ∀ x, φ.apply x ↔ ψ.apply x

/-- Membership in an arbitrary class extension is its defining matrix value,
the eliminative reading licensed by ✱20·01–02. -/
def Member (x : α) (ψ : Matrix α) : Prop :=
  ψ.apply x

private theorem classEquivalent_refl (φ : Matrix α) : ClassEquivalent φ φ :=
  fun _ => Iff.rfl

private theorem classEquivalent_symm {φ ψ : Matrix α} :
    ClassEquivalent φ ψ → ClassEquivalent ψ φ :=
  fun equivalence x => (equivalence x).symm

private theorem classEquivalent_trans {φ ψ χ : Matrix α} :
    ClassEquivalent φ ψ → ClassEquivalent ψ χ → ClassEquivalent φ χ :=
  fun left right x => (left x).trans (right x)

/-- PM I ✱20·23. -/
theorem star_20_23 (φ ψ χ : Matrix α) :
    ClassEquivalent φ ψ → ClassEquivalent φ χ → ClassEquivalent ψ χ := by
  intro hφψ hφχ
  exact classEquivalent_trans (classEquivalent_symm hφψ) hφχ

/-- PM I ✱20·24. -/
theorem star_20_24 (φ ψ χ : Matrix α) :
    ClassEquivalent ψ φ → ClassEquivalent χ φ → ClassEquivalent ψ χ := by
  intro hψφ hχφ
  exact classEquivalent_trans hψφ (classEquivalent_symm hχφ)

/-- PM I ✱20·25. Quantifying the comparison against every class extension
characterizes equality of the two displayed extensions. -/
theorem star_20_25 (φ ψ : Matrix α) :
    (∀ a : Matrix α, ClassEquivalent a φ ↔ ClassEquivalent a ψ) ↔
      ClassEquivalent φ ψ := by
  constructor
  · intro universal
    exact (universal φ).1 (classEquivalent_refl φ)
  · intro hφψ a
    constructor
    · intro haφ
      exact classEquivalent_trans haφ hφψ
    · intro haψ
      exact classEquivalent_trans haψ (classEquivalent_symm hφψ)

/-- PM I ✱20·3, the membership reduction for an arbitrary class extension. -/
theorem star_20_3 (x : α) (ψ : Matrix α) :
    Member x ψ ↔ ψ.apply x := by
  rfl

/-- PM I ✱20·31, extensional class identity expressed through membership. -/
theorem star_20_31 (ψ χ : Matrix α) :
    ClassEquivalent ψ χ ↔ ∀ x, Member x ψ ↔ Member x χ := by
  rfl

end PM.Architecture.Star20Q320Kernel
