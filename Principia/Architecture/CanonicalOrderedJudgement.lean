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

/-- A Raw substitution whose elementary images have each been reified by an
existing indexed assertion.  This makes explicit the evidence missing from
an arbitrary syntax substitution. -/
structure ReifiedSubstitution (σ : Substitution Γ Ξ) where
  order : Elementary Γ → Nat
  formula : ∀ proposition : Elementary Γ, OrderedFormula Ξ (order proposition)
  proof : ∀ proposition : Elementary Γ, OrderedAssertion (formula proposition)
  roundTrip : ∀ proposition : Elementary Γ,
    ofOrdered (formula proposition) = σ proposition

/-- A theorem schema is deliberately outside `OrderedAssertion`.  Its
instantiation action is supplied as a derivational builder over *reified*
substitutions, so Raw syntax alone cannot manufacture a new judgement. -/
structure CanonicalTheoremSchema (template : Raw Γ) where
  derivation : NormalizedCanonicalAssertion template
  instantiate : ∀ {Ξ} (σ : Substitution Γ Ξ),
    ReifiedSubstitution σ → NormalizedCanonicalAssertion (substitute σ template)

def CanonicalTheoremSchema.instantiateAt
    {Γ Ξ : RealContext} {template : Raw Γ}
    (schema : CanonicalTheoremSchema template) (σ : Substitution Γ Ξ)
    (reified : ReifiedSubstitution σ) :
    NormalizedCanonicalAssertion (substitute σ template) :=
  schema.instantiate σ reified

def normalize {source target : Raw Γ}
    (certificate : NormalizesScoped source target)
    (assertion : CanonicalOrderedAssertion source) :
    NormalizedCanonicalAssertion target := by
  rcases assertion with ⟨order, formula, proof, equation⟩
  subst source
  exact ⟨order, formula, proof, certificate⟩

/-- The explicitly weakened ✱9·06 redex is present beneath the two retained
binders of line (4); this is the source-labelled line-(4)→line-(5)
normalization of ✱9·21. -/
theorem star_9_21_line4_line5_certificate
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScoped (star_9_21_line4_raw φ ψ) (star_9_21_line5_raw φ ψ) := by
  rw [star_9_21_line4_raw_named]
  apply NormalizesScoped.alwaysCongr
  apply NormalizesScoped.sometimesCongr
  let antecedent := rawImp (star_9_21_phi_x_closed_raw φ)
    (star_9_21_psi_x_closed_raw ψ)
  let consequent := rawImp (star_9_21_phi_y_closed_raw φ)
    (star_9_21_psi_z_closed_raw ψ)
  have unused : UnusedBoundAt 0 antecedent := by
    exact ⟨star_9_21_phi_x_closed_unused_zero φ,
      star_9_21_psi_x_closed_unused_zero ψ⟩
  change NormalizesScoped (.quantified .sometimes (.disj (.neg antecedent) consequent))
    (.disj (.neg (dropUnusedBound antecedent)) (.quantified .sometimes consequent))
  have reduction := NormalizesScoped.star_9_06_imp
    (dropUnusedBound antecedent) consequent
  have reinsert : weakenBound (dropUnusedBound antecedent) = antecedent :=
    weakenBound_dropUnusedBound antecedent unused
  rw [reinsert] at reduction
  exact reduction

theorem star_9_21_line4_line7_certificate
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizesScoped (star_9_21_line4_raw φ ψ) (star_9_21_line7_raw φ ψ) := by
  apply NormalizesScoped.trans (star_9_21_line4_line5_certificate φ ψ)
  apply NormalizesScoped.trans (NormalizesScoped.star_9_21_line5_line6 φ ψ)
  exact NormalizesScoped.refl _

/-- The existing line-(4) derivation, with the full audited normalization
certificate through the displayed line (7).  Its proof payload is unchanged:
only its canonical Raw presentation is normalized. -/
def derive_star_9_21_line7_normalized
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizedCanonicalAssertion (star_9_21_line7_raw φ ψ) := by
  apply normalize (star_9_21_line4_line7_certificate φ ψ)
  exact image_of_ordered (derive_star_9_21_line4 φ ψ)

end PM.Architecture.CanonicalOrderedJudgement
