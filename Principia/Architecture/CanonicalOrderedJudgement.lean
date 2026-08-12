import Principia.Architecture.CanonicalNormalization

namespace PM.Architecture.CanonicalOrderedJudgement

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.FirstOrderPrerequisites

/-- Conservative image of the indexed assertion judgement in canonical Raw
syntax.  It has no constructors beyond an existing `OrderedAssertion`. -/
def CanonicalOrderedAssertion (raw : Raw Γ) : Prop :=
  ∃ (order : Nat) (formula : OrderedFormula Γ order),
    OrderedAssertion formula ∧ ofOrdered formula = raw

/-- A Raw formula reified by one exact indexed carrier. -/
structure Reified (raw : Raw Γ) where
  order : Nat
  formula : OrderedFormula Γ order
  roundTrip : ofOrdered formula = raw

theorem image_of_ordered {formula : OrderedFormula Γ order}
    (proof : OrderedAssertion formula) :
    CanonicalOrderedAssertion (ofOrdered formula) :=
  ⟨order, formula, proof, rfl⟩

def reified_of_ordered (formula : OrderedFormula Γ order) :
    Reified (ofOrdered formula) :=
  ⟨order, formula, rfl⟩

theorem image_convert {p q : Raw Γ} (equality : p = q) :
    CanonicalOrderedAssertion p → CanonicalOrderedAssertion q := by
  intro proof
  cases equality
  exact proof

end PM.Architecture.CanonicalOrderedJudgement
