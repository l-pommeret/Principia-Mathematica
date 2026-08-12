import Principia.Architecture.Star14Q297Kernel

namespace PM.Architecture.Star14Q307Kernel

open PM.Architecture.Star14Q297Kernel

/-- Exact contextual reading of PM I ✱14·22:
`E!(℩x)(φx) ≡ φ(℩x)(φx)`. -/
theorem star_14_22 (φ : α → Prop) :
    DescriptionExists φ ↔ DescriptionApplies φ φ := by
  constructor
  · rintro ⟨b, unique⟩
    exact ⟨b, unique, (unique b).mpr rfl⟩
  · rintro ⟨b, unique, _⟩
    exact ⟨b, unique⟩

/-- Exact contextual reading of PM I ✱14·23.  The description belongs to
the complete matrix `φx ∧ ψx`, while its displayed evaluation is `φ` at the
same unique witness. -/
theorem star_14_23 (φ ψ : α → Prop) :
    DescriptionExists (fun x => φ x ∧ ψ x) ↔
      DescriptionApplies (fun x => φ x ∧ ψ x) φ := by
  constructor
  · rintro ⟨b, unique⟩
    exact ⟨b, unique, ((unique b).mpr rfl).1⟩
  · rintro ⟨b, unique, _⟩
    exact ⟨b, unique⟩

/-- Exact wide-scope reading of PM I ✱14·24.  The right side retains the
description scope around the whole formal equivalence in `y`. -/
theorem star_14_24 (φ : α → Prop) :
    DescriptionExists φ ↔
      DescriptionApplies φ (fun b => ∀ y, φ y ↔ y = b) := by
  constructor
  · rintro ⟨b, unique⟩
    exact ⟨b, unique, unique⟩
  · rintro ⟨b, unique, _⟩
    exact ⟨b, unique⟩

/-- Exact narrow-scope consequence at PM I ✱14·241.  The implication keeps
the witness inside `DescriptionApplies`; it does not select a global term. -/
theorem star_14_241 (φ : α → Prop) :
    DescriptionExists φ →
      DescriptionApplies φ (fun b => ∀ y, φ y ↔ y = b) := by
  rintro ⟨b, unique⟩
  exact ⟨b, unique, unique⟩

end PM.Architecture.Star14Q307Kernel
