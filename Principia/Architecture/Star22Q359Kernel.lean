import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star22Q359Kernel

open PM.Architecture.Star22Q341Definitions

private theorem complement_involutive (a : Class α) :
    Star22Q341Definitions.Complement
      (Star22Q341Definitions.Complement a) = a := by
  funext x
  exact propext Classical.not_not

/-- PM I ✱22·94: universal class quantification is invariant under replacing
every typed class by its complement. -/
theorem star_22_94 (f : Class α → Prop) :
    (∀ a, f a) ↔ ∀ a, f (Star22Q341Definitions.Complement a) := by
  constructor
  · intro h a
    exact h (Star22Q341Definitions.Complement a)
  · intro h a
    simpa [complement_involutive a] using
      h (Star22Q341Definitions.Complement a)

/-- PM I ✱22·95: existential class quantification is invariant under the
same involutive complement transformation. -/
theorem star_22_95 (f : Class α → Prop) :
    (∃ a, f a) ↔ ∃ a, f (Star22Q341Definitions.Complement a) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Star22Q341Definitions.Complement a,
      by simpa [complement_involutive a]⟩
  · rintro ⟨a, ha⟩
    exact ⟨Star22Q341Definitions.Complement a, ha⟩

end PM.Architecture.Star22Q359Kernel
