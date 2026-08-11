-- PM-CONTEXT-FOUNDATION Principia/Syntax/Formula.lean
namespace PM

inductive RealType where
  | elementaryProposition : RealType
  deriving DecidableEq, Repr

abbrev RealContext := List RealType

inductive RealVar : (Γ : RealContext) → RealType → Type where
  | zero : RealVar (τ :: Γ) τ
  | succ : RealVar Γ τ → RealVar (σ :: Γ) τ
  deriving DecidableEq, Repr

inductive Elementary : RealContext → Type where
  | constant : String → Elementary Γ
  | var : RealVar Γ .elementaryProposition → Elementary Γ
  | neg : Elementary Γ → Elementary Γ
  | disj : Elementary Γ → Elementary Γ → Elementary Γ
  deriving DecidableEq, Repr

namespace Elementary

prefix:max "∼ₚ" => neg

infixl:55 " ∨ₚ " => disj

def imp (p q : Elementary Γ) : Elementary Γ := disj (neg p) q

infixr:54 " ⊃ₚ " => imp

end Elementary
end PM

-- PM-CONTEXT-FOUNDATION Principia/Syntax/Apparent.lean
namespace PM

abbrev BoundContext := List RealType

inductive BoundVar : (Δ : BoundContext) → RealType → Type where
  | zero : BoundVar (τ :: Δ) τ
  | succ : BoundVar Δ τ → BoundVar (σ :: Δ) τ
  deriving DecidableEq, Repr

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

abbrev RealRenaming (Γ Ξ : RealContext) :=
  {τ : RealType} → RealVar Γ τ → RealVar Ξ τ

def renameReal (ρ : RealRenaming Γ Ξ) : Apparent Γ Δ → Apparent Ξ Δ
  | .constant name => .constant name
  | .real v => .real (ρ v)
  | .bound v => .bound v
  | .neg proposition => .neg (renameReal ρ proposition)
  | .disj left right => .disj (renameReal ρ left) (renameReal ρ right)

def weakenReal (proposition : Apparent Γ Δ) : Apparent (τ :: Γ) Δ :=
  renameReal (fun v => .succ v) proposition

def boundFormula (v : BoundVar Δ .elementaryProposition) : Apparent Γ Δ :=
  .bound v

def ofElementary : Elementary Γ → Apparent Γ Δ
  | .constant name => .constant name
  | .var v => .real v
  | .neg proposition => .neg (ofElementary proposition)
  | .disj left right => .disj (ofElementary left) (ofElementary right)

def toElementary? : Apparent Γ Δ → Option (Elementary Γ)
  | .constant name => some (.constant name)
  | .real v => some (.var v)
  | .bound _ => none
  | .neg proposition => (toElementary? proposition).map .neg
  | .disj left right => do
      let p ← toElementary? left
      let q ← toElementary? right
      pure (.disj p q)

def closedToElementary : Apparent Γ [] → Elementary Γ
  | .constant name => .constant name
  | .real v => .var v
  | .bound v => nomatch v
  | .neg proposition => .neg (closedToElementary proposition)
  | .disj left right => .disj (closedToElementary left) (closedToElementary right)

abbrev Renaming (Δ Ξ : BoundContext) :=
  BoundVar Δ .elementaryProposition → BoundVar Ξ .elementaryProposition

def liftRenaming (ρ : Renaming Δ Ξ) :
    Renaming (.elementaryProposition :: Δ) (.elementaryProposition :: Ξ)
  | .zero => .zero
  | .succ v => .succ (ρ v)

def outerVariableRenaming :
    Renaming (.elementaryProposition :: Δ)
      (.elementaryProposition :: .elementaryProposition :: Δ)
  | .zero => .succ .zero
  | .succ v => .succ (.succ v)

def innerVariableRenaming :
    Renaming (.elementaryProposition :: Δ)
      (.elementaryProposition :: .elementaryProposition :: Δ)
  | .zero => .zero
  | .succ v => .succ (.succ v)

def rename (ρ : Renaming Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real v => .real v
  | .bound v => .bound (ρ v)
  | .neg proposition => .neg (rename ρ proposition)
  | .disj left right => .disj (rename ρ left) (rename ρ right)

def weaken (proposition : Apparent Γ Δ) : Apparent Γ (τ :: Δ) :=
  rename (fun v => .succ v) proposition

abbrev Substitution (Γ : RealContext) (Δ Ξ : BoundContext) :=
  BoundVar Δ .elementaryProposition → Apparent Γ Ξ

def liftSubstitution (σ : Substitution Γ Δ Ξ) :
    Substitution Γ (.elementaryProposition :: Δ)
      (.elementaryProposition :: Ξ)
  | .zero => boundFormula .zero
  | .succ v => weaken (σ v)

def substitute (σ : Substitution Γ Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real v => .real v
  | .bound v => σ v
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

def instantiateSubstitution (argument : Apparent Γ Δ) :
    Substitution Γ (.elementaryProposition :: Δ) Δ
  | .zero => argument
  | .succ predecessor => .bound predecessor

def instantiate (body : Apparent Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : Apparent Γ Δ :=
  substitute (instantiateSubstitution argument) body

def atReal (body : Apparent Γ [.elementaryProposition])
    (x : RealVar Γ .elementaryProposition) : Elementary Γ :=
  closedToElementary (instantiate body (.real x))

def abstractHead : Elementary (.elementaryProposition :: Γ) →
    Apparent Γ [.elementaryProposition]
  | .constant name => .constant name
  | .var .zero => .bound .zero
  | .var (.succ v) => .real v
  | .neg proposition => .neg (abstractHead proposition)
  | .disj left right => .disj (abstractHead left) (abstractHead right)

def openHead : Apparent Γ [.elementaryProposition] →
    Elementary (.elementaryProposition :: Γ)
  | .constant name => .constant name
  | .real v => .var (.succ v)
  | .bound .zero => .var .zero
  | .bound (.succ v) => nomatch v
  | .neg proposition => .neg (openHead proposition)
  | .disj left right => .disj (openHead left) (openHead right)

def abstractRealHead : Apparent (.elementaryProposition :: Γ) Δ →
    Apparent Γ (.elementaryProposition :: Δ)
  | .constant name => .constant name
  | .real .zero => .bound .zero
  | .real (.succ predecessor) => .real predecessor
  | .bound boundVariable => .bound (.succ boundVariable)
  | .neg proposition => .neg (abstractRealHead proposition)
  | .disj left right => .disj (abstractRealHead left) (abstractRealHead right)

def openRealHead : Apparent Γ (.elementaryProposition :: Δ) →
    Apparent (.elementaryProposition :: Γ) Δ
  | .constant name => .constant name
  | .real realVariable => .real (.succ realVariable)
  | .bound .zero => .real .zero
  | .bound (.succ predecessor) => .bound predecessor
  | .neg proposition => .neg (openRealHead proposition)
  | .disj left right => .disj (openRealHead left) (openRealHead right)

@[simp] theorem openRealHead_abstractRealHead
    (proposition : Apparent (.elementaryProposition :: Γ) Δ) :
    openRealHead (abstractRealHead proposition) = proposition := by
  induction proposition with
  | constant name => rfl
  | real realVariable => cases realVariable <;> rfl
  | bound boundVariable => rfl
  | neg proposition ih =>
      change Apparent.neg (openRealHead (abstractRealHead proposition)) =
        Apparent.neg proposition
      rw [ih]
  | disj left right ihLeft ihRight =>
      change Apparent.disj (openRealHead (abstractRealHead left))
        (openRealHead (abstractRealHead right)) = Apparent.disj left right
      rw [ihLeft, ihRight]

def significant (v : BoundVar Δ .elementaryProposition) : Apparent Γ Δ → Bool
  | .constant _ => false
  | .real _ => false
  | .bound candidate =>
      v == candidate
  | .neg proposition => significant v proposition
  | .disj left right => significant v left || significant v right

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

inductive Quantified (Matrix : BoundContext → Type) (Δ : BoundContext) where
  | always : Matrix (.elementaryProposition :: Δ) → Quantified Matrix Δ
  | sometimes : Matrix (.elementaryProposition :: Δ) → Quantified Matrix Δ

namespace Quantified

def neg (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ) :
    Quantified Matrix Δ → Quantified Matrix Δ
  | .always body => .sometimes (matrixNeg body)
  | .sometimes body => .always (matrixNeg body)

def disjAlwaysSometimes
    (renameMatrix : {Δ Ξ : BoundContext} → Apparent.Renaming Δ Ξ →
      Matrix Δ → Matrix Ξ)
    (disjMatrix : {Δ : BoundContext} → Matrix Δ → Matrix Δ → Matrix Δ)
    (φ ψ : Matrix (.elementaryProposition :: Δ)) :
    Quantified (Quantified Matrix) Δ :=
  Quantified.always
    (Quantified.sometimes
      (disjMatrix
        (renameMatrix Apparent.outerVariableRenaming φ)
        (renameMatrix Apparent.innerVariableRenaming ψ)))

def disjSometimesAlways
    (renameMatrix : {Δ Ξ : BoundContext} → Apparent.Renaming Δ Ξ →
      Matrix Δ → Matrix Ξ)
    (disjMatrix : {Δ : BoundContext} → Matrix Δ → Matrix Δ → Matrix Δ)
    (ψ φ : Matrix (.elementaryProposition :: Δ)) :
    Quantified (Quantified Matrix) Δ :=
  Quantified.always
    (Quantified.sometimes
      (disjMatrix
        (renameMatrix Apparent.innerVariableRenaming ψ)
        (renameMatrix Apparent.outerVariableRenaming φ)))

@[simp] theorem neg_always
    {Matrix : BoundContext → Type}
    (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ)
    (body : Matrix (.elementaryProposition :: Δ)) :
    neg (Δ := Δ) matrixNeg (@Quantified.always Matrix Δ body) =
      @Quantified.sometimes Matrix Δ (matrixNeg body) := rfl

@[simp] theorem neg_sometimes
    {Matrix : BoundContext → Type}
    (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ)
    (body : Matrix (.elementaryProposition :: Δ)) :
    neg (Δ := Δ) matrixNeg (@Quantified.sometimes Matrix Δ body) =
      @Quantified.always Matrix Δ (matrixNeg body) := rfl

end Quantified

abbrev FirstOrder (Γ : RealContext) : BoundContext → Type :=
  Quantified (Apparent Γ)

abbrev SecondOrder (Γ : RealContext) : BoundContext → Type :=
  Quantified (FirstOrder Γ)

namespace FirstOrder

abbrev always (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := Quantified.always body

abbrev sometimes (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := Quantified.sometimes body

def weakenReal : FirstOrder Γ Δ → FirstOrder (τ :: Γ) Δ
  | Quantified.always body => Quantified.always (Apparent.weakenReal body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.weakenReal body)

def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    FirstOrder Γ Δ → FirstOrder Ξ Δ
  | Quantified.always body => Quantified.always (Apparent.renameReal ρ body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.renameReal ρ body)

def abstractRealHead : FirstOrder (.elementaryProposition :: Γ) Δ →
    FirstOrder Γ (.elementaryProposition :: Δ)
  | Quantified.always body => Quantified.always (Apparent.abstractRealHead body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.abstractRealHead body)

def openRealHead : FirstOrder Γ (.elementaryProposition :: Δ) →
    FirstOrder (.elementaryProposition :: Γ) Δ
  | Quantified.always body => Quantified.always (Apparent.openRealHead body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.openRealHead body)

@[simp] theorem openRealHead_abstractRealHead
    (proposition : FirstOrder (.elementaryProposition :: Γ) Δ) :
    openRealHead (abstractRealHead proposition) = proposition := by
  cases proposition with
  | always body =>
      change Quantified.always
        (Apparent.openRealHead (Apparent.abstractRealHead body)) =
          Quantified.always body
      rw [Apparent.openRealHead_abstractRealHead]
  | sometimes body =>
      change Quantified.sometimes
        (Apparent.openRealHead (Apparent.abstractRealHead body)) =
          Quantified.sometimes body
      rw [Apparent.openRealHead_abstractRealHead]

def rename (ρ : Apparent.Renaming Δ Ξ) : FirstOrder Γ Δ → FirstOrder Γ Ξ
  | Quantified.always body =>
      Quantified.always (Apparent.rename (Apparent.liftRenaming ρ) body)
  | Quantified.sometimes body =>
      Quantified.sometimes (Apparent.rename (Apparent.liftRenaming ρ) body)

def substitute (σ : Apparent.Substitution Γ Δ Ξ) :
    FirstOrder Γ Δ → FirstOrder Γ Ξ
  | Quantified.always body =>
      Quantified.always
        (Apparent.substitute (Apparent.liftSubstitution σ) body)
  | Quantified.sometimes body =>
      Quantified.sometimes
        (Apparent.substitute (Apparent.liftSubstitution σ) body)

def Significant (v : BoundVar Δ .elementaryProposition) :
    FirstOrder Γ Δ → Prop
  | Quantified.always body => Apparent.Significant (.succ v) body
  | Quantified.sometimes body => Apparent.Significant (.succ v) body

def neg : FirstOrder Γ Δ → FirstOrder Γ Δ :=
  Quantified.neg (fun proposition => Apparent.neg proposition)

prefix:max "∼₁" => neg

@[simp] theorem neg_always
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    neg (always body) = sometimes (.neg body) := rfl

@[simp] theorem neg_sometimes
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    neg (sometimes body) = always (.neg body) := rfl

def disjRightElementary : FirstOrder Γ Δ → Elementary Γ → FirstOrder Γ Δ
  | Quantified.always body, proposition =>
      always (body ∨ₐ Apparent.ofElementary proposition)
  | Quantified.sometimes body, proposition =>
      sometimes (body ∨ₐ Apparent.ofElementary proposition)

def disjElementaryLeft : Elementary Γ → FirstOrder Γ Δ → FirstOrder Γ Δ
  | proposition, Quantified.always body =>
      always (Apparent.ofElementary proposition ∨ₐ body)
  | proposition, Quantified.sometimes body =>
      sometimes (Apparent.ofElementary proposition ∨ₐ body)

def impElementaryToFirst (proposition : Elementary Γ) :
    FirstOrder Γ Δ → FirstOrder Γ Δ :=
  disjElementaryLeft (Elementary.neg proposition)

@[simp] theorem star_9_03_reduction
    (body : Apparent Γ (.elementaryProposition :: Δ))
    (proposition : Elementary Γ) :
    disjRightElementary (always body) proposition =
      always (body ∨ₐ Apparent.ofElementary proposition) := rfl

@[simp] theorem star_9_04_reduction
    (proposition : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    disjElementaryLeft proposition (always body) =
      always (Apparent.ofElementary proposition ∨ₐ body) := rfl

@[simp] theorem star_9_05_reduction
    (body : Apparent Γ (.elementaryProposition :: Δ))
    (proposition : Elementary Γ) :
    disjRightElementary (sometimes body) proposition =
      sometimes (body ∨ₐ Apparent.ofElementary proposition) := rfl

@[simp] theorem star_9_06_reduction
    (proposition : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    disjElementaryLeft proposition (sometimes body) =
      sometimes (Apparent.ofElementary proposition ∨ₐ body) := rfl

def disjAlwaysSometimes
    (φ ψ : Apparent Γ (.elementaryProposition :: Δ)) : SecondOrder Γ Δ :=
  Quantified.disjAlwaysSometimes Apparent.rename Apparent.disj φ ψ

def disjSometimesAlways
    (ψ φ : Apparent Γ (.elementaryProposition :: Δ)) : SecondOrder Γ Δ :=
  Quantified.disjSometimesAlways Apparent.rename Apparent.disj ψ φ

@[simp] theorem star_9_07_reduction
    (φ ψ : Apparent Γ (.elementaryProposition :: Δ)) :
    disjAlwaysSometimes φ ψ =
      Quantified.always
        (Quantified.sometimes
          (Apparent.rename Apparent.outerVariableRenaming φ ∨ₐ
            Apparent.rename Apparent.innerVariableRenaming ψ)) := rfl

@[simp] theorem star_9_08_reduction
    (ψ φ : Apparent Γ (.elementaryProposition :: Δ)) :
    disjSometimesAlways ψ φ =
      Quantified.always
        (Quantified.sometimes
          (Apparent.rename Apparent.innerVariableRenaming ψ ∨ₐ
            Apparent.rename Apparent.outerVariableRenaming φ)) := rfl

end FirstOrder
end PM

-- PM-CONTEXT-FOUNDATION Principia/Syntax/Ordered.lean
namespace PM

namespace OrderedFormula

inductive FirstOrderDisjunctionScope where
  | sameAssignedOrder
  | universalRightElementary
  | elementaryLeftUniversal
  | existentialRightElementary
  | elementaryLeftExistential
  | universalLeftExistential
  | existentialLeftUniversal

end OrderedFormula

inductive OrderedDisjunctionScope : Nat → Type where
  | elementary : OrderedDisjunctionScope 0
  | firstOrder : OrderedFormula.FirstOrderDisjunctionScope →
      OrderedDisjunctionScope 1

inductive OrderedFormula (Γ : RealContext) : Nat → Type where
  | elementary : Elementary Γ → OrderedFormula Γ 0
  | firstOrder : FirstOrder Γ [] → OrderedFormula Γ 1

  | secondOrder : SecondOrder Γ [] → OrderedFormula Γ 2
  | neg : OrderedFormula Γ order → OrderedFormula Γ order
  | disj : OrderedDisjunctionScope order → OrderedFormula Γ order →
      OrderedFormula Γ order → OrderedFormula Γ order

namespace OrderedFormula

prefix:max "∼ₒ" => neg

def scopedDisj (scope : OrderedDisjunctionScope order)
    (left right : OrderedFormula Γ order) : OrderedFormula Γ order :=
  .disj scope left right

def scopedImp (scope : OrderedDisjunctionScope order)
    (p q : OrderedFormula Γ order) : OrderedFormula Γ order :=
  scopedDisj scope (∼ₒ p) q

def scopedFirstOrderDisj (scope : FirstOrderDisjunctionScope)
    (left right : OrderedFormula Γ 1) : OrderedFormula Γ 1 :=
  scopedDisj (.firstOrder scope) left right

def firstImp (left right : OrderedFormula Γ 1) : OrderedFormula Γ 1 :=
  scopedImp (.firstOrder .sameAssignedOrder) left right

def always (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.always body)

def sometimes (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.sometimes body)

def alwaysFirstOrder (body : FirstOrder Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  .secondOrder (Quantified.always body)

def embedElementary (p : Elementary Γ) : OrderedFormula Γ 0 := .elementary p

def eraseElementary? : OrderedFormula Γ order → Option (Elementary Γ)
  | .elementary p => some p
  | .firstOrder _ => none
  | .secondOrder _ => none
  | .neg p => (eraseElementary? p).map .neg
  | .disj .elementary p q => do
      let p ← eraseElementary? p
      let q ← eraseElementary? q
      pure (.disj p q)
  | .disj (.firstOrder _) _ _ => none

@[simp] theorem erase_embedElementary (p : Elementary Γ) :
    eraseElementary? (embedElementary p) = some p := rfl

end OrderedFormula

end PM

-- PM-CONTEXT-FOUNDATION Principia/Deduction/System.lean
namespace PM

inductive Derivation : {Γ : RealContext} → Elementary Γ → Prop where

  | star_1_1 {p q : Elementary []} :
      Derivation p → Derivation (p ⊃ₚ q) → Derivation q

  | star_1_11 {Γ : RealContext} {φ ψ : Elementary Γ}
      (hasRealVariable : Γ ≠ []) :
      Derivation φ → Derivation (φ ⊃ₚ ψ) → Derivation ψ

  | star_1_2 {Γ : RealContext} (p : Elementary Γ) :
      Derivation ((p ∨ₚ p) ⊃ₚ p)

  | star_1_3 {Γ : RealContext} (p q : Elementary Γ) :
      Derivation (q ⊃ₚ (p ∨ₚ q))

  | star_1_4 {Γ : RealContext} (p q : Elementary Γ) :
      Derivation ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p))

  | star_1_5 {Γ : RealContext} (p q r : Elementary Γ) :
      Derivation ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r)))

  | star_1_6 {Γ : RealContext} (p q r : Elementary Γ) :
      Derivation ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)))

notation:45 "⊢ₚ " p => Derivation p

namespace Derivation

theorem detach {Γ : PM.RealContext} {φ ψ : PM.Elementary Γ}
    (hφ : PM.Derivation φ) (hφψ : PM.Derivation (φ ⊃ₚ ψ)) :
    PM.Derivation ψ := by
  match Γ, φ, ψ, hφ, hφψ with
  | [], φ, ψ, hφ, hφψ => exact PM.Derivation.star_1_1 hφ hφψ
  | (τ :: Δ), φ, ψ, hφ, hφψ =>
      exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hφ hφψ

end Derivation

end PM

-- PM-CONTEXT-FOUNDATION Principia/Deduction/Ordered.lean
namespace PM

structure OrderedRuleBook (Γ : RealContext) (order : Nat) where

  Primitive : OrderedFormula Γ order → Type

inductive OrderedDerivation (rules : OrderedRuleBook Γ order) :
    OrderedFormula Γ order → Prop where
  | primitive {p : OrderedFormula Γ order} : rules.Primitive p →
      OrderedDerivation rules p
  | detach {p q : OrderedFormula Γ order} (scope : OrderedDisjunctionScope order) :
      OrderedDerivation rules p → OrderedDerivation rules (OrderedFormula.scopedImp scope p q) →
        OrderedDerivation rules q

end PM

-- PM-CONTEXT-LOCAL Principia/Architecture/FirstOrderPrerequisites.lean
namespace PM.Architecture.FirstOrderPrerequisites

open PM.OrderedFormula

private structure MatrixSyntaxAt (order : Nat) where
  Matrix : RealContext → BoundContext → Type
  renameReal : {Γ Ξ : RealContext} → {Δ : BoundContext} →
    Apparent.RealRenaming Γ Ξ → Matrix Γ Δ → Matrix Ξ Δ
  abstractHead : {Γ : RealContext} → {Δ : BoundContext} →
    Matrix (.elementaryProposition :: Γ) Δ →
      Matrix Γ (.elementaryProposition :: Δ)
  all : {Γ : RealContext} →
    Matrix Γ [.elementaryProposition] → OrderedFormula Γ (order + 1)

private def firstOrderMatrixSyntaxAt : MatrixSyntaxAt 1 where
  Matrix := fun Γ Δ => FirstOrder Γ Δ
  renameReal := fun ρ proposition => FirstOrder.renameReal ρ proposition
  abstractHead := fun proposition => FirstOrder.abstractRealHead proposition
  all := fun body => OrderedFormula.alwaysFirstOrder body

def firstOrderToSecondAll (body : FirstOrder Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  firstOrderMatrixSyntaxAt.all body

@[simp] theorem firstOrderToSecondAll_reduction
    (body : FirstOrder Γ [.elementaryProposition]) :
    firstOrderToSecondAll body = OrderedFormula.alwaysFirstOrder body := rfl

def closedFirstOrderAlphaRenaming : Apparent.Renaming [] [] :=
  fun emptyVariable => nomatch emptyVariable

@[simp] theorem closedFirstOrder_alpha
    (body : Apparent Γ [.elementaryProposition]) :
    FirstOrder.rename closedFirstOrderAlphaRenaming (FirstOrder.always body) =
      FirstOrder.always body := by
  change Quantified.always
    (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) body) =
      Quantified.always body
  congr 1
  induction body with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ emptyBoundVariable => exact nomatch emptyBoundVariable
  | neg proposition ih =>
      change Apparent.neg
        (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) proposition) =
          Apparent.neg proposition
      rw [ih]
  | disj left right ihLeft ihRight =>
      change Apparent.disj
        (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) left)
        (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) right) =
          Apparent.disj left right
      rw [ihLeft, ihRight]

def matrixImp (φ ψ : Apparent Γ Δ) : Apparent Γ Δ :=
  Apparent.disj (Apparent.neg φ) ψ

def star_9_1_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 1 :=
  .firstOrder
    (FirstOrder.impElementaryToFirst (Apparent.openHead φ)
      (FirstOrder.weakenReal (FirstOrder.sometimes φ)))

def star_9_11_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: .elementaryProposition :: Γ) 1 :=
  let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
  let φx := Apparent.atReal lifted .zero
  let φy := Apparent.atReal lifted (.succ .zero)
  let conclusion := FirstOrder.weakenReal
    (FirstOrder.weakenReal (FirstOrder.sometimes φ))
  .firstOrder (FirstOrder.impElementaryToFirst (φx ∨ₚ φy) conclusion)

def star_9_21_target (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp
    (OrderedFormula.always (matrixImp φ ψ))
    (firstImp (OrderedFormula.always φ) (OrderedFormula.always ψ))

def star_9_23_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp (OrderedFormula.always φ) (OrderedFormula.always φ)

def star_9_25_target (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  firstImp
    (OrderedFormula.always (Apparent.ofElementary p ∨ₐ φ))
    (.firstOrder (FirstOrder.disjElementaryLeft p (FirstOrder.always φ)))

inductive OrderedAssertion : {Γ : RealContext} → {order : Nat} →
    OrderedFormula Γ order → Prop where
  | elementary {p : Elementary Γ} : Derivation p →
      OrderedAssertion (.elementary p)

  | star_9_1 (φ : Apparent Γ [.elementaryProposition]) :
      OrderedAssertion (star_9_1_target φ)

  | star_9_11 (φ : Apparent Γ [.elementaryProposition]) :
      OrderedAssertion (star_9_11_target φ)

  | star_9_12 {p q : OrderedFormula Γ 1} :
      OrderedAssertion p → OrderedAssertion (firstImp p q) →
      OrderedAssertion q

  | star_9_12_elementary_to_first {p : Elementary Γ} {q : FirstOrder Γ []} :
      OrderedAssertion (.elementary p) →
      OrderedAssertion (.firstOrder (FirstOrder.impElementaryToFirst p q)) →
      OrderedAssertion (.firstOrder q)

  | star_9_13 (φ : Apparent Γ [.elementaryProposition]) :
      OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.elementary (Apparent.openHead φ)) →
      OrderedAssertion (.firstOrder (FirstOrder.always φ))

  | star_9_13_first (φ : FirstOrder Γ [.elementaryProposition]) :
      OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.firstOrder (FirstOrder.openRealHead φ)) →
      OrderedAssertion (firstOrderToSecondAll φ)

abbrev Star_9_21Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (star_9_21_target φ ψ)

def derive_star_9_23 (φ : Apparent Γ [.elementaryProposition])
    (elementaryId : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary (Apparent.openHead (matrixImp φ φ))))
    (monotonicity : Star_9_21Derivation φ φ) :
    OrderedAssertion (star_9_23_target φ) :=
  OrderedAssertion.star_9_12
    (OrderedAssertion.star_9_13 (matrixImp φ φ) elementaryId)
    monotonicity

abbrev Star_9_25Derivation (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (star_9_25_target p φ)

def derive_star_9_25 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition])
    (identity : OrderedAssertion
      (star_9_23_target (Apparent.ofElementary p ∨ₐ φ))) :
    Star_9_25Derivation p φ :=
  identity

end PM.Architecture.FirstOrderPrerequisites

-- PM-CONTEXT-LOCAL Principia/Architecture/FirstOrderQ259.lean
namespace PM.Architecture.FirstOrderQ259

def star_9_3_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  let p := OrderedFormula.always φ
  OrderedFormula.firstImp
    (OrderedFormula.scopedFirstOrderDisj .sameAssignedOrder p p) p

def star_9_31_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  let p := OrderedFormula.sometimes φ
  OrderedFormula.firstImp
    (OrderedFormula.scopedFirstOrderDisj .sameAssignedOrder p p) p

def star_9_32_target (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.impElementaryToFirst q (FirstOrder.always φ))

def star_9_33_target (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.impElementaryToFirst q (FirstOrder.sometimes φ))

end PM.Architecture.FirstOrderQ259

-- PM-CONTEXT-LOCAL Principia/Architecture/Q259ClosedRuleBook.lean
namespace PM.Architecture.Q259ClosedRuleBook

open PM.Architecture.FirstOrderPrerequisites

structure Q259ClosedRuleBook where

  star_9_21 : {Γ : RealContext} →
    (φ ψ : Apparent Γ [.elementaryProposition]) →
    Star_9_21Derivation φ ψ

  star_9_25 : {Γ : RealContext} → (p : Elementary Γ) →
    (φ : Apparent Γ [.elementaryProposition]) →
    Star_9_25Derivation p φ

abbrev Star_9_3Derivation (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_3_target φ)

abbrev Star_9_31Derivation (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_31_target φ)

abbrev Star_9_32Derivation (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_32_target q φ)

abbrev Star_9_33Derivation (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_33_target q φ)

end PM.Architecture.Q259ClosedRuleBook
