import Principia.Syntax.Formula

namespace PM

/-!
# Apparent variables

This file is the capture-safe syntactic foundation required at ✱9. It does
not change `Elementary` and postulates no rules of deduction. `Apparent` is a
matrix with free apparent variables; `Quantified` performs one explicit step
to the next proposition order. Thus higher orders can be constructed one at a
time without a universe ranging over every order.
-/

/-- A context of typed apparent variables, not a context of assumptions. -/
abbrev BoundContext := List RealType

/-- Intrinsically scoped, typed de Bruijn apparent variables. -/
inductive BoundVar : (Δ : BoundContext) → RealType → Type where
  | zero : BoundVar (τ :: Δ) τ
  | succ : BoundVar Δ τ → BoundVar (σ :: Δ) τ
  deriving DecidableEq, Repr

/-- Elementary matrices in which variables from `Δ` may occur apparently. -/
inductive Apparent (Γ : RealContext) : BoundContext → Type where
  | constant : String → Apparent Γ Δ
  | real : RealVar Γ .elementaryProposition → Apparent Γ Δ
  | bound : BoundVar Δ .elementaryProposition → Apparent Γ Δ
  | neg : Apparent Γ Δ → Apparent Γ Δ
  | disj : Apparent Γ Δ → Apparent Γ Δ → Apparent Γ Δ
  deriving DecidableEq, Repr

namespace Apparent

prefix:max "∼ₐ" => neg
infixl:55 " ∨ₐ " => disj

/-- Regard a variable of the currently available PM real type as an atomic
formula. This match is intentionally exhaustive over `RealType`: adding a new
argument type later will force an audited account of its atomic formulae. -/
def boundFormula (v : BoundVar Δ .elementaryProposition) : Apparent Γ Δ :=
  .bound v

/-- The conservative inclusion of the pre-✱9 elementary syntax. -/
def ofElementary : Elementary Γ → Apparent Γ Δ
  | .constant name => .constant name
  | .var v => .real v
  | .neg proposition => .neg (ofElementary proposition)
  | .disj left right => .disj (ofElementary left) (ofElementary right)

/-- Partial erasure to elementary syntax; binders and bound variables fail. -/
def toElementary? : Apparent Γ Δ → Option (Elementary Γ)
  | .constant name => some (.constant name)
  | .real v => some (.var v)
  | .bound _ => none
  | .neg proposition => (toElementary? proposition).map .neg
  | .disj left right => do
      let p ← toElementary? left
      let q ← toElementary? right
      pure (.disj p q)

/-- Capture-free renamings of apparent variables. -/
abbrev Renaming (Δ Ξ : BoundContext) :=
  BoundVar Δ .elementaryProposition → BoundVar Ξ .elementaryProposition

/-- Lift a renaming through one binder. -/
def liftRenaming (ρ : Renaming Δ Ξ) :
    Renaming (.elementaryProposition :: Δ) (.elementaryProposition :: Ξ)
  | .zero => .zero
  | .succ v => .succ (ρ v)

/-- Simultaneous, capture-free renaming of apparent variables. -/
def rename (ρ : Renaming Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real v => .real v
  | .bound v => .bound (ρ v)
  | .neg proposition => .neg (rename ρ proposition)
  | .disj left right => .disj (rename ρ left) (rename ρ right)

/-- Weakening by a freshly bound apparent variable. -/
def weaken (proposition : Apparent Γ Δ) : Apparent Γ (τ :: Δ) :=
  rename (fun v => .succ v) proposition

/-- Capture-free simultaneous substitutions for apparent variables. -/
abbrev Substitution (Γ : RealContext) (Δ Ξ : BoundContext) :=
  BoundVar Δ .elementaryProposition → Apparent Γ Ξ

/-- Lift a substitution through one binder. -/
def liftSubstitution (σ : Substitution Γ Δ Ξ) :
    Substitution Γ (.elementaryProposition :: Δ)
      (.elementaryProposition :: Ξ)
  | .zero => boundFormula .zero
  | .succ v => weaken (σ v)

/-- Simultaneous, capture-free substitution of apparent variables. -/
def substitute (σ : Substitution Γ Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real v => .real v
  | .bound v => σ v
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

/-- The substitution which replaces the nearest binder and lowers the rest. -/
def instantiateSubstitution (argument : Apparent Γ Δ) :
    Substitution Γ (.elementaryProposition :: Δ) Δ
  | .zero => argument
  | .succ predecessor => .bound predecessor

/-- Instantiate the nearest apparent-variable binder. -/
def instantiate (body : Apparent Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : Apparent Γ Δ :=
  substitute (instantiateSubstitution argument) body

/-- Decidable structural occurrence of a free apparent variable. -/
def significant (v : BoundVar Δ .elementaryProposition) : Apparent Γ Δ → Bool
  | .constant _ => false
  | .real _ => false
  | .bound candidate =>
      v == candidate
  | .neg proposition => significant v proposition
  | .disj left right => significant v left || significant v right

/-- Proposition-valued, auditable form of syntactic significance. -/
def Significant (v : BoundVar Δ .elementaryProposition)
    (proposition : Apparent Γ Δ) : Prop :=
  significant v proposition = true

@[simp] theorem rename_bound (ρ : Renaming Δ Ξ)
    (v : BoundVar Δ .elementaryProposition) :
    rename ρ (.bound v : Apparent Γ Δ) = .bound (ρ v) := rfl

@[simp] theorem substitute_bound (σ : Substitution Γ Δ Ξ)
    (v : BoundVar Δ .elementaryProposition) :
    substitute σ (.bound v : Apparent Γ Δ) = σ v := rfl

@[simp] theorem instantiate_zero (argument : Apparent Γ Δ) :
    instantiate
        (.bound (.zero : BoundVar (.elementaryProposition :: Δ)
          .elementaryProposition)) argument = argument := rfl

@[simp] theorem toElementary_ofElementary (proposition : Elementary Γ) :
    toElementary? (ofElementary proposition : Apparent Γ Δ) = some proposition := by
  induction proposition with
  | constant name => rfl
  | var v => rfl
  | neg proposition ih => simp [ofElementary, toElementary?, ih]
  | disj left right ihLeft ihRight =>
      simp [ofElementary, toElementary?, ihLeft, ihRight]

end Apparent

/-- One fixed step from matrices to quantified propositions.

The two constructors are PM's two primitive binding ideas, kept injectively
distinct. The parameter `Matrix` permits repetition for any *assigned* next
order; it is not a quantification over all proposition orders. -/
inductive Quantified (Matrix : BoundContext → Type) (Δ : BoundContext) where
  | always : Matrix (.elementaryProposition :: Δ) → Quantified Matrix Δ
  | sometimes : Matrix (.elementaryProposition :: Δ) → Quantified Matrix Δ

namespace Quantified

/-- Negation at one quantified order, given negation for its fixed matrix
order. Its two equations are the definitional reductions printed at ✱9·01
and ✱9·02. -/
def neg (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ) :
    Quantified Matrix Δ → Quantified Matrix Δ
  | .always body => .sometimes (matrixNeg body)
  | .sometimes body => .always (matrixNeg body)

@[simp] theorem neg_always
    (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ)
    (body : Matrix (.elementaryProposition :: Δ)) :
    neg matrixNeg (.always body) = .sometimes (matrixNeg body) := rfl

@[simp] theorem neg_sometimes
    (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ)
    (body : Matrix (.elementaryProposition :: Δ)) :
    neg matrixNeg (.sometimes body) = .always (matrixNeg body) := rfl

end Quantified

/-- First-order propositions: one quantified step over elementary matrices. -/
abbrev FirstOrder (Γ : RealContext) : BoundContext → Type :=
  Quantified (Apparent Γ)

namespace FirstOrder

/-- PM's primitive idea `(x).φx`. -/
abbrev always (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := .always body

/-- PM's primitive idea `(∃x).φx`. -/
abbrev sometimes (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := .sometimes body

/-- Capture-free renaming beneath either primitive binder. -/
def rename (ρ : Apparent.Renaming Δ Ξ) : FirstOrder Γ Δ → FirstOrder Γ Ξ
  | .always body => .always (Apparent.rename (Apparent.liftRenaming ρ) body)
  | .sometimes body =>
      .sometimes (Apparent.rename (Apparent.liftRenaming ρ) body)

/-- Capture-free substitution beneath either primitive binder. -/
def substitute (σ : Apparent.Substitution Γ Δ Ξ) :
    FirstOrder Γ Δ → FirstOrder Γ Ξ
  | .always body =>
      .always (Apparent.substitute (Apparent.liftSubstitution σ) body)
  | .sometimes body =>
      .sometimes (Apparent.substitute (Apparent.liftSubstitution σ) body)

/-- A free apparent variable is significant in a quantified proposition when
its shifted occurrence is significant in the matrix. -/
def Significant (v : BoundVar Δ .elementaryProposition) :
    FirstOrder Γ Δ → Prop
  | .always body => Apparent.Significant (.succ v) body
  | .sometimes body => Apparent.Significant (.succ v) body

/-- First-order negation. The two constructor cases reduce definitionally to
✱9·01 and ✱9·02; no semantic Lean negation is involved. -/
def neg : FirstOrder Γ Δ → FirstOrder Γ Δ :=
  Quantified.neg (fun proposition => Apparent.neg proposition)

prefix:max "∼₁" => neg

@[simp] theorem neg_always
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    neg (always body) = sometimes (.neg body) := rfl

@[simp] theorem neg_sometimes
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    neg (sometimes body) = always (.neg body) := rfl

end FirstOrder
end PM
