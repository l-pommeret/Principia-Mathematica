import Principia.Architecture.CanonicalNormalization

namespace PM.Architecture.CanonicalOrderedJudgement

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalNormalization

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

/-- Conservative canonical assertion after a source-labelled scope
normalization.  Its sole proof payload remains an indexed `OrderedAssertion`;
the second field records how its Raw embedding reaches the displayed target. -/
def NormalizedCanonicalAssertion (raw : Raw Γ) : Prop :=
  ∃ (order : Nat) (formula : OrderedFormula Γ order),
    OrderedAssertion formula ∧ NormalizesScoped (ofOrdered formula) raw

def normalize {source target : Raw Γ}
    (certificate : NormalizesScoped source target)
    (assertion : CanonicalOrderedAssertion source) :
    NormalizedCanonicalAssertion target := by
  rcases assertion with ⟨order, formula, proof, equation⟩
  subst source
  exact ⟨order, formula, proof, certificate⟩

end PM.Architecture.CanonicalOrderedJudgement
