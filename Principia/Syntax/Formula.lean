namespace PM

/-- Types of real variables recognized by the reconstructed PM syntax.

Only elementary propositions are available in ✱1. Further constructors must be
introduced from their first audited source passages. -/
inductive RealType where
  | elementaryProposition : RealType
  deriving DecidableEq, Repr

/-- A context of *real variables* in the terminology of PM.

This is not a context of logical hypotheses. -/
abbrev RealContext := List RealType

/-- Well-typed de Bruijn variables in a real-variable context. -/
inductive RealVar : (Γ : RealContext) → RealType → Type where
  | zero : RealVar (τ :: Γ) τ
  | succ : RealVar Γ τ → RealVar (σ :: Γ) τ
  deriving DecidableEq, Repr

/-- Elementary propositions and elementary propositional functions.

An expression in the empty context is a definite elementary proposition. An
expression in a nonempty context is an elementary propositional function whose
undetermined constituents are real variables. -/
inductive Elementary : RealContext → Type where
  | constant : String → Elementary Γ
  | var : RealVar Γ .elementaryProposition → Elementary Γ
  | neg : Elementary Γ → Elementary Γ
  | disj : Elementary Γ → Elementary Γ → Elementary Γ
  deriving DecidableEq, Repr

namespace Elementary

prefix:max "∼ₚ" => neg
/-- PM's unbracketed iterated disjunction, introduced at ✱2·33, associates
to the left: `p ∨ q ∨ r` abbreviates `(p ∨ q) ∨ r`.  Formulae printed
before ✱2·33 retain their explicit brackets in the edition. -/
infixl:55 " ∨ₚ " => disj

/-- ✱1·01: `p ⊃ q .=. ∼p ∨ q  Df.`

Implication is an abbreviation, not a primitive constructor and not a theorem
asserting an object-language equivalence. -/
def imp (p q : Elementary Γ) : Elementary Γ := disj (neg p) q

infixr:54 " ⊃ₚ " => imp

end Elementary
end PM
