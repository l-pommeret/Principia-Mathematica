import Principia.Syntax.Formula

namespace PM

/-!
# Apparent variables

This file is the capture-safe syntactic foundation required before ✱9. It
adds apparent-variable binding without changing `Elementary` and without
postulating any rules of deduction. The existential binder and the
order-sensitive operations described at ✱9 are deliberately not anticipated
here: they enter only at their audited printed loci.
-/

/-- A context of typed apparent variables, not a context of assumptions. -/
abbrev BoundContext := List RealType

/-- Intrinsically scoped, typed de Bruijn apparent variables. -/
inductive BoundVar : (Δ : BoundContext) → RealType → Type where
  | zero : BoundVar (τ :: Δ) τ
  | succ : BoundVar Δ τ → BoundVar (σ :: Δ) τ
  deriving DecidableEq, Repr

/-- Formulae in which variables from `Δ` may occur apparently.

The connectives record an elementary matrix. `all` is only the binding form
needed to state the first primitive idea at ✱9; this datatype gives it no
deductive force. -/
inductive Apparent (Γ : RealContext) : BoundContext → Type where
  | constant : String → Apparent Γ Δ
  | real : RealVar Γ .elementaryProposition → Apparent Γ Δ
  | bound : BoundVar Δ .elementaryProposition → Apparent Γ Δ
  | neg : Apparent Γ Δ → Apparent Γ Δ
  | disj : Apparent Γ Δ → Apparent Γ Δ → Apparent Γ Δ
  | all (τ : RealType) : Apparent Γ (τ :: Δ) → Apparent Γ Δ
  deriving DecidableEq, Repr

namespace Apparent

prefix:max "∼ₐ" => neg
infixl:55 " ∨ₐ " => disj

/-- Regard a variable of the currently available PM real type as an atomic
formula. This match is intentionally exhaustive over `RealType`: adding a new
argument type later will force an audited account of its atomic formulae. -/
def boundFormula (variable : BoundVar Δ τ) : Apparent Γ Δ :=
  match τ, variable with
  | .elementaryProposition, proposition => .bound proposition

/-- The conservative inclusion of the pre-✱9 elementary syntax. -/
def ofElementary : Elementary Γ → Apparent Γ Δ
  | .constant name => .constant name
  | .var variable => .real variable
  | .neg proposition => .neg (ofElementary proposition)
  | .disj left right => .disj (ofElementary left) (ofElementary right)

/-- Partial erasure to elementary syntax; binders and bound variables fail. -/
def toElementary? : Apparent Γ Δ → Option (Elementary Γ)
  | .constant name => some (.constant name)
  | .real variable => some (.var variable)
  | .bound _ => none
  | .neg proposition => (toElementary? proposition).map .neg
  | .disj left right => do
      let p ← toElementary? left
      let q ← toElementary? right
      pure (.disj p q)
  | .all _ _ => none

/-- Capture-free renamings of apparent variables. -/
abbrev Renaming (Δ Ξ : BoundContext) :=
  {τ : RealType} → BoundVar Δ τ → BoundVar Ξ τ

/-- Lift a renaming through one binder. -/
def liftRenaming (ρ : Renaming Δ Ξ) : Renaming (τ :: Δ) (τ :: Ξ)
  | _, .zero => .zero
  | _, .succ variable => .succ (ρ variable)

/-- Simultaneous, capture-free renaming of apparent variables. -/
def rename (ρ : Renaming Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real variable => .real variable
  | .bound variable => .bound (ρ variable)
  | .neg proposition => .neg (rename ρ proposition)
  | .disj left right => .disj (rename ρ left) (rename ρ right)
  | .all τ body => .all τ (rename (liftRenaming ρ) body)

/-- Weakening by a freshly bound apparent variable. -/
def weaken (proposition : Apparent Γ Δ) : Apparent Γ (τ :: Δ) :=
  rename (fun variable => .succ variable) proposition

/-- Capture-free simultaneous substitutions for apparent variables. -/
abbrev Substitution (Γ : RealContext) (Δ Ξ : BoundContext) :=
  {τ : RealType} → BoundVar Δ τ → Apparent Γ Ξ

/-- Lift a substitution through one binder. -/
def liftSubstitution (σ : Substitution Γ Δ Ξ) :
    Substitution Γ (τ :: Δ) (τ :: Ξ)
  | _, .zero => boundFormula .zero
  | _, .succ variable => weaken (σ variable)

/-- Simultaneous, capture-free substitution of apparent variables. -/
def substitute (σ : Substitution Γ Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real variable => .real variable
  | .bound variable => σ variable
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)
  | .all τ body => .all τ (substitute (liftSubstitution σ) body)

/-- Instantiate the nearest apparent-variable binder. -/
def instantiate (body : Apparent Γ (τ :: Δ)) (argument : Apparent Γ Δ) :
    Apparent Γ Δ :=
  substitute (fun
    | _, .zero => argument
    | _, .succ variable => boundFormula variable) body

/-- Decidable structural occurrence of a free apparent variable. -/
def significant (variable : BoundVar Δ τ) : Apparent Γ Δ → Bool
  | .constant _ => false
  | .real _ => false
  | .bound candidate =>
      match τ, variable, candidate with
      | .elementaryProposition, x, y => x == y
  | .neg proposition => significant variable proposition
  | .disj left right => significant variable left || significant variable right
  | .all _ body => significant (.succ variable) body

/-- Proposition-valued, auditable form of syntactic significance. -/
def Significant (variable : BoundVar Δ τ) (proposition : Apparent Γ Δ) : Prop :=
  significant variable proposition = true

@[simp] theorem rename_bound (ρ : Renaming Δ Ξ) (variable : BoundVar Δ τ) :
    rename ρ (.bound variable : Apparent Γ Δ) = .bound (ρ variable) := rfl

@[simp] theorem substitute_bound (σ : Substitution Γ Δ Ξ)
    (variable : BoundVar Δ τ) :
    substitute σ (.bound variable : Apparent Γ Δ) = σ variable := rfl

@[simp] theorem instantiate_zero (argument : Apparent Γ Δ) :
    instantiate
        (.bound (.zero : BoundVar (.elementaryProposition :: Δ)
          .elementaryProposition)) argument = argument := rfl

@[simp] theorem toElementary_ofElementary (proposition : Elementary Γ) :
    toElementary? (ofElementary proposition : Apparent Γ Δ) = some proposition := by
  induction proposition with
  | constant name => rfl
  | var variable => rfl
  | neg proposition ih => simp [ofElementary, toElementary?, ih]
  | disj left right ihLeft ihRight =>
      simp [ofElementary, toElementary?, ihLeft, ihRight]

end Apparent
end PM
