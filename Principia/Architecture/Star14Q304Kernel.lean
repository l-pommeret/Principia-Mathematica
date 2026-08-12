import Principia.Architecture.Star14Q299Kernel

namespace PM.Architecture.Star14Q304Kernel

open PM.Architecture.Star14Q299Kernel

/-- The contextual proposition `a = (℩x)(φx)`, expanded without making the
description into a term. -/
def EqualDescription (a : α) (φ : α → Prop) : Prop :=
  DescriptionScope φ (fun b => a = b)

/-- The contextual proposition `(℩x)(φx) = (℩x)(ψx)`, with both description
scopes expanded and neither description reified as a term. -/
def DescriptionsEqual (φ ψ : α → Prop) : Prop :=
  DescriptionScopePair φ ψ (fun b c => b = c)

/-- PM I ✱14·14: ordinary identity composes with contextual-description
identity. -/
theorem star_14_14 (a b : α) (φ : α → Prop) :
    a = b → EqualDescription b φ → EqualDescription a φ := by
  rintro hab ⟨c, hc, hbc⟩
  exact ⟨c, hc, hab.trans hbc⟩

/-- PM I ✱14·142: identity from an object to one description composes with
identity between two descriptions. -/
theorem star_14_142 (a : α) (φ ψ : α → Prop) :
    EqualDescription a φ → DescriptionsEqual φ ψ → EqualDescription a ψ := by
  rintro ⟨b, hφ, hab⟩ ⟨b', c, hφ', hψ, hbc⟩
  have hbb' : b = b' := (hφ' b).mp ((hφ b).mpr rfl)
  exact ⟨c, hψ, hab.trans (hbb'.trans hbc)⟩

/-- PM I ✱14·144: contextual identity of descriptions is transitive. -/
theorem star_14_144 (φ ψ χ : α → Prop) :
    DescriptionsEqual φ ψ → DescriptionsEqual ψ χ → DescriptionsEqual φ χ := by
  rintro ⟨a, b, hφ, hψ, hab⟩ ⟨b', c, hψ', hχ, hbc⟩
  have hbb' : b = b' := (hψ' b).mp ((hψ b).mpr rfl)
  exact ⟨a, c, hφ, hχ, hab.trans (hbb'.trans hbc)⟩

/-- PM I ✱14·145: two descriptions identical with the same object are
identical with one another. -/
theorem star_14_145 (a : α) (φ ψ : α → Prop) :
    EqualDescription a φ → EqualDescription a ψ → DescriptionsEqual φ ψ := by
  rintro ⟨b, hφ, hab⟩ ⟨c, hψ, hac⟩
  exact ⟨b, c, hφ, hψ, hab.symm.trans hac⟩

end PM.Architecture.Star14Q304Kernel
