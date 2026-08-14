import Principia.Architecture.Star20Q317Definitions

/-!
# PM I, ✱20·59–61

The class carrier is the explicitly typed extension introduced for ✱20·07–08.
The incomplete class description in ✱20·59 is retained contextually; ✱20·6
and ✱20·61 are the complete logical class-quantifier theorems.
-/

namespace PM.Architecture.Star20Q323Kernel

open PM.Architecture.Star20Q317Definitions

/-- Secondary semantic target for ✱20·59. This `Prop` is deliberately not the
v1 formalization: unlike the object formulas and `PM.Derivation` judgments in
`Star2.lean`, it cannot express PM's class abstraction or contextual class
description as object syntax. It remains useful only as a statement-design
record while the primary object/judgment layer is blocked. `(ια)(fα)` is
eliminated by the existing scope and never made into a freely denoting term. -/
def star_20_59_target (φ : Class Object) (f : Class Object → Prop) : Prop :=
  ClassDescriptionScope f (fun described => φ = described ↔ described = φ)

/-- PM I ✱20·6: existential class quantification is equivalent to the
negation of universal negation. -/
theorem star_20_6 (f : Class Object → Prop) :
    (∃ α : Class Object, f α) ↔ ¬ (∀ α : Class Object, ¬ f α) := by
  constructor
  · rintro ⟨α, hα⟩ universal
    exact universal α hα
  · intro notUniversal
    exact Classical.byContradiction fun noWitness =>
      notUniversal (fun α hα => noWitness ⟨α, hα⟩)

/-- PM I ✱20·61: universal class instantiation. -/
theorem star_20_61 (f : Class Object → Prop) (β : Class Object) :
    (∀ α : Class Object, f α) → f β := by
  intro universal
  exact universal β

end PM.Architecture.Star20Q323Kernel
