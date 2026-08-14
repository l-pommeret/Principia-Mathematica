import Principia.Architecture.Star122Kernel

/-!
# PM II ✱123 — exact typed opening kernel

The three declarations below preserve the source quantifiers and definitions.
✱123·02 and ·11 are deliberately absent: the current typed architecture does
not yet represent all operations needed for exact statements of those loci.
-/

namespace PM.Architecture.Star123OpeningKernel

abbrev Set (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop

abbrev Progression (R : Rel α) : Prop :=
  PM.Architecture.Star122Kernel.Progression R
abbrev domain (R : Rel α) : Set α :=
  PM.Architecture.Star122Kernel.domain R

def DomainsOfProgressions (A : Set α) : Prop :=
  ∃ R : Rel α, Progression R ∧ A = domain R

def AlephZero : Set (Set α) := DomainsOfProgressions

/-- ✱123·01. `ℵ₀ = DʻʻProg` Df. -/
def star_123_01 : Set (Set α) := DomainsOfProgressions

/-- PM ✱123·1: membership in `ℵ₀` is being the domain of a progression. -/
theorem star_123_1 (A : Set α) :
    AlephZero A ↔ ∃ R : Rel α, Progression R ∧ A = domain R := Iff.rfl

/-- PM ✱123·101: every progression's domain belongs to `ℵ₀`. -/
theorem star_123_101 (R : Rel α) (hR : Progression R) :
    AlephZero (domain R) := ⟨R, hR, rfl⟩

end PM.Architecture.Star123OpeningKernel
