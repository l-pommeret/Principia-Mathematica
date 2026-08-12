import Principia.Architecture.Star14Q299Kernel

/-!
# PM I ✱14·15, ✱14·16, and ✱14·17

Description occurrences remain contextual: no total choice term is created.
The exact substitution principles are proved through the Russellian scope
introduced at ✱14·01.
-/

namespace PM.Architecture.Star14Q305Kernel

open Star14Q299Kernel

/-- Contextual identity of a description with an ordinary term. -/
abbrev DescriptionEquals (φ : α → Prop) (b : α) : Prop :=
  Characterizes φ b

/-- Contextual identity of two descriptions: the same object is uniquely
characterized by both matrices. -/
def DescriptionsEqual (φ ψ : α → Prop) : Prop :=
  ∃ b, Characterizes φ b ∧ Characterizes ψ b

/-- ✱14·15. Under the displayed description identity, substitution in an
arbitrary contextual matrix preserves and reflects truth. -/
theorem star_14_15 (φ ψ : α → Prop) (b : α) :
    DescriptionEquals φ b → (DescriptionScope φ ψ ↔ ψ b) := by
  intro hφ
  constructor
  · rintro ⟨a, ha, hψ⟩
    have hab : a = b := by
      have hba : b = a := (ha b).mp ((hφ b).mpr rfl)
      exact hba.symm
    simpa [hab] using hψ
  · intro hψ
    exact ⟨b, hφ, hψ⟩

/-- ✱14·16. Equal descriptions are interchangeable in every contextual
matrix, without turning either description into a total term. -/
theorem star_14_16 (φ ψ χ : α → Prop) :
    DescriptionsEqual φ ψ →
      (DescriptionScope φ χ ↔ DescriptionScope ψ χ) := by
  rintro ⟨b, hφ, hψ⟩
  exact (star_14_15 φ χ b hφ).trans (star_14_15 ψ χ b hψ).symm

/-- ✱14·17. Description identity is equivalent to formal equivalence under
every predicative one-place value-range context. -/
theorem star_14_17 (φ : α → Prop) (b : α) :
    DescriptionEquals φ b ↔
      ∀ ψ : α → Prop, DescriptionScope φ ψ ↔ ψ b := by
  constructor
  · intro hφ ψ
    exact star_14_15 φ ψ b hφ
  · intro h
    have hscope : DescriptionScope φ (fun x => x = b) :=
      (h (fun x => x = b)).mpr rfl
    rcases hscope with ⟨a, ha, hab⟩
    subst a
    exact ha

end PM.Architecture.Star14Q305Kernel
