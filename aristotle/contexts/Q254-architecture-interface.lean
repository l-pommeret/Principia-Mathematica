/- Architecture-experimental opaque interface. This file is not a repository import,
   does not establish canonical PM coverage, and cannot be promoted. -/

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
  | .real (.succ variable) => .real variable
  | .bound variable => .bound (.succ variable)
  | .neg proposition => .neg (abstractRealHead proposition)
  | .disj left right => .disj (abstractRealHead left) (abstractRealHead right)

def openRealHead : Apparent Γ (.elementaryProposition :: Δ) →
    Apparent (.elementaryProposition :: Γ) Δ
  | .constant name => .constant name
  | .real variable => .real (.succ variable)
  | .bound .zero => .real .zero
  | .bound (.succ variable) => .bound variable
  | .neg proposition => .neg (openRealHead proposition)
  | .disj left right => .disj (openRealHead left) (openRealHead right)

@[simp] theorem openRealHead_abstractRealHead
    (proposition : Apparent (.elementaryProposition :: Γ) Δ) :
    openRealHead (abstractRealHead proposition) = proposition := by
  induction proposition with
  | constant name => rfl
  | real variable => cases variable <;> rfl
  | bound variable => rfl
  | neg proposition ih => simp [abstractRealHead, openRealHead, ih]
  | disj left right ihLeft ihRight =>
      simp [abstractRealHead, openRealHead, ihLeft, ihRight]

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
  cases proposition <;> simp [abstractRealHead, openRealHead]

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


-- OPAQUE-PM-DEPENDENCY PM1:✱9·03 4a93ebde8b2739c4df14f6bca9d50ff02b1eed5f2b48c2824d113d5b55872e00
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_03 {Γ Δ}
    (body : PM.Apparent Γ (.elementaryProposition :: Δ))
    (proposition : PM.Elementary Γ) : PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9

-- OPAQUE-PM-DEPENDENCY PM1:✱9·04 3e70e4d0a88f30428a666afffd907f0c5df6d7da75594d3fe7e69cb0628ae6a6
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_04 {Γ Δ}
    (proposition : PM.Elementary Γ)
    (body : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9

-- OPAQUE-PM-DEPENDENCY PM1:✱9·05 b7886cd8227a0f21f0564e5586112b13ea0bd0106aa61547a218440e0b12d97c
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_05 {Γ Δ}
    (body : PM.Apparent Γ (.elementaryProposition :: Δ))
    (proposition : PM.Elementary Γ) : PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9

-- OPAQUE-PM-DEPENDENCY PM1:✱9·06 49af3daa13583aa728671180ffe5283c557de4648c8a80ebc1fb1a19ffb4c380
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_06 {Γ Δ}
    (proposition : PM.Elementary Γ)
    (body : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9
