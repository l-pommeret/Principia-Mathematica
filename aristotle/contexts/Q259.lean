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

abbrev SchemaAssignment (Γ Ξ : RealContext) :=
  RealVar Γ .elementaryProposition → Elementary Ξ

def schemaInstance (σ : SchemaAssignment Γ Ξ) : Elementary Γ → Elementary Ξ
  | .constant name => .constant name
  | .var v => σ v
  | .neg proposition => .neg (schemaInstance σ proposition)
  | .disj left right => .disj (schemaInstance σ left) (schemaInstance σ right)

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

def diagonalRealRenaming :
    RealRenaming (.elementaryProposition :: .elementaryProposition :: Γ)
      (.elementaryProposition :: Γ)
  | _, .zero => .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ predecessor) => .succ predecessor

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

def elementaryValue : Apparent Γ [.elementaryProposition] →
    Elementary Γ → Elementary Γ
  | .constant name, _ => .constant name
  | .real v, _ => .var v
  | .bound .zero, argument => argument
  | .neg proposition, argument => .neg (elementaryValue proposition argument)
  | .disj left right, argument => .disj
      (elementaryValue left argument) (elementaryValue right argument)

@[simp] theorem elementaryValue_ofElementary (p argument : Elementary Γ) :
    elementaryValue (ofElementary p : Apparent Γ [.elementaryProposition]) argument = p := by
  induction p with
  | constant name => rfl
  | var v => rfl
  | neg p ih => simp [ofElementary, elementaryValue, ih]
  | disj p q ihp ihq => simp [ofElementary, elementaryValue, ihp, ihq]

@[simp] theorem elementaryValue_weakenReal_zero
    (φ : Apparent Γ [.elementaryProposition]) :
    elementaryValue (weakenReal φ) (.var .zero) = openHead φ := by
  induction φ with
  | constant name => rfl
  | real v => rfl
  | bound v =>
      cases v with
      | zero => rfl
      | succ tail => exact nomatch tail
  | neg p ih =>
      have hp : elementaryValue (renameReal (fun v => .succ v) p) (.var .zero) = openHead p := by
        simpa [weakenReal] using ih
      simp only [weakenReal, renameReal, elementaryValue, openHead]
      rw [hp]
  | disj p q ihp ihq =>
      have hp : elementaryValue (renameReal (fun v => .succ v) p) (.var .zero) = openHead p := by
        simpa [weakenReal] using ihp
      have hq : elementaryValue (renameReal (fun v => .succ v) q) (.var .zero) = openHead q := by
        simpa [weakenReal] using ihq
      simp only [weakenReal, renameReal, elementaryValue, openHead]
      rw [hp, hq]

@[simp] theorem elementaryValue_renameReal_succ_zero
    (φ : Apparent Γ [.elementaryProposition]) :
    elementaryValue (renameReal (fun v => .succ v) φ) (.var .zero) = openHead φ := by
  simpa [weakenReal] using elementaryValue_weakenReal_zero φ

@[simp] theorem substitute_liftInstantiate_renameOuter_weakenReal
    (φ : Apparent Γ [.elementaryProposition]) :
    substitute (liftSubstitution
      (instantiateSubstitution (.real (.zero : RealVar
        (.elementaryProposition :: Γ) .elementaryProposition))))
      (rename (fun _ => .succ .zero) (weakenReal φ)) =
      (ofElementary (openHead φ) : Apparent (.elementaryProposition :: Γ)
        [.elementaryProposition]) := by
  induction φ with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ emptyVariable => exact nomatch emptyVariable
  | neg proposition ih =>
      simpa [substitute, rename, weakenReal, renameReal, ofElementary, openHead]
        using congrArg neg ih
  | disj left right ihLeft ihRight =>
      change disj (substitute _ (rename _ (weakenReal left)))
        (substitute _ (rename _ (weakenReal right))) =
        disj (ofElementary (openHead left)) (ofElementary (openHead right))
      rw [ihLeft, ihRight]

@[simp] theorem substitute_liftInstantiate_renameInner_weakenReal
    (φ : Apparent Γ [.elementaryProposition]) :
    substitute (liftSubstitution
      (instantiateSubstitution (.real (.zero : RealVar
        (.elementaryProposition :: Γ) .elementaryProposition))))
      (rename (fun _ => .zero) (weakenReal φ)) = weakenReal φ := by
  induction φ with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ emptyVariable => exact nomatch emptyVariable
  | neg proposition ih =>
      simpa [substitute, rename, weakenReal, renameReal] using congrArg neg ih
  | disj left right ihLeft ihRight =>
      change disj (substitute _ (rename _ (weakenReal left)))
        (substitute _ (rename _ (weakenReal right))) =
        disj (weakenReal left) (weakenReal right)
      rw [ihLeft, ihRight]

@[simp] theorem substitute_liftInstantiate_ofElementary
    (p : Elementary (.elementaryProposition :: Γ)) :
    substitute (liftSubstitution
      (instantiateSubstitution (.real (.zero : RealVar
        (.elementaryProposition :: Γ) .elementaryProposition))))
      (ofElementary p : Apparent (.elementaryProposition :: Γ)
        (.elementaryProposition :: .elementaryProposition :: [])) = ofElementary p := by
  induction p with
  | constant name => rfl
  | var realVariable => rfl
  | neg proposition ih => simpa [substitute, ofElementary] using congrArg neg ih
  | disj left right ihLeft ihRight => simp [substitute, ofElementary, ihLeft, ihRight]

def openHeadOrBound (φ : Apparent Γ [.elementaryProposition]) :
    Apparent (.elementaryProposition :: Γ) [.elementaryProposition] :=
  Apparent.ofElementary (openHead φ) ∨ₐ Apparent.weakenReal φ

@[simp] theorem openHeadOrBound_left
    (φ : Apparent Γ [.elementaryProposition]) :
    openHeadOrBound φ =
      Apparent.ofElementary (openHead φ) ∨ₐ Apparent.weakenReal φ := rfl

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

def abstractRealOuter : Apparent (.elementaryProposition :: Γ)
    (.elementaryProposition :: Δ) →
    Apparent Γ (.elementaryProposition :: .elementaryProposition :: Δ)
  | .constant name => .constant name
  | .real .zero => .bound (.succ .zero)
  | .real (.succ predecessor) => .real predecessor
  | .bound .zero => .bound .zero
  | .bound (.succ predecessor) => .bound (.succ (.succ predecessor))
  | .neg proposition => .neg (abstractRealOuter proposition)
  | .disj left right => .disj (abstractRealOuter left) (abstractRealOuter right)

def openRealOuter : Apparent Γ
    (.elementaryProposition :: .elementaryProposition :: Δ) →
    Apparent (.elementaryProposition :: Γ) (.elementaryProposition :: Δ)
  | .constant name => .constant name
  | .real realVariable => .real (.succ realVariable)
  | .bound .zero => .bound .zero
  | .bound (.succ .zero) => .real .zero
  | .bound (.succ (.succ predecessor)) => .bound (.succ predecessor)
  | .neg proposition => .neg (openRealOuter proposition)
  | .disj left right => .disj (openRealOuter left) (openRealOuter right)

@[simp] theorem openRealOuter_abstractRealOuter
    (proposition : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    openRealOuter (abstractRealOuter proposition) = proposition := by
  induction proposition with
  | constant name => rfl
  | real realVariable => cases realVariable <;> rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ predecessor => rfl
  | neg proposition ih =>
      change Apparent.neg (openRealOuter (abstractRealOuter proposition)) =
        Apparent.neg proposition
      rw [ih]
  | disj left right ihLeft ihRight =>
      change Apparent.disj (openRealOuter (abstractRealOuter left))
        (openRealOuter (abstractRealOuter right)) = Apparent.disj left right
      rw [ihLeft, ihRight]

@[simp] theorem abstractRealOuter_ofElementary_openHead
    (φ : Apparent Γ [.elementaryProposition]) :
    abstractRealOuter (ofElementary (openHead φ)) = weaken φ := by
  induction φ with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ emptyBoundVariable => exact nomatch emptyBoundVariable
  | neg proposition ih =>
      change Apparent.neg (abstractRealOuter (ofElementary (openHead proposition))) =
        Apparent.neg (weaken proposition)
      rw [ih]
  | disj left right ihLeft ihRight =>
      change Apparent.disj
        (abstractRealOuter (ofElementary (openHead left)))
        (abstractRealOuter (ofElementary (openHead right))) =
        Apparent.disj (weaken left) (weaken right)
      rw [ihLeft, ihRight]

@[simp] theorem abstractRealOuter_weakenReal
    (φ : Apparent Γ [.elementaryProposition]) :
    abstractRealOuter (weakenReal φ) = rename innerVariableRenaming φ := by
  induction φ with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ emptyBoundVariable => exact nomatch emptyBoundVariable
  | neg proposition ih =>
      change Apparent.neg (abstractRealOuter (weakenReal proposition)) =
        Apparent.neg (rename innerVariableRenaming proposition)
      rw [ih]
  | disj left right ihLeft ihRight =>
      change Apparent.disj (abstractRealOuter (weakenReal left))
        (abstractRealOuter (weakenReal right)) =
        Apparent.disj (rename innerVariableRenaming left)
          (rename innerVariableRenaming right)
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

inductive FirstOrderMatrix (Γ : RealContext) (Δ : BoundContext) where
  | quantified : FirstOrder Γ Δ → FirstOrderMatrix Γ Δ
  | neg : FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Δ
  | disj : FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Δ

namespace FirstOrderMatrix

prefix:max "∼₁ₘ" => neg
infixl:55 " ∨₁ₘ " => disj

def ofFirstOrder (proposition : FirstOrder Γ Δ) : FirstOrderMatrix Γ Δ :=
  .quantified proposition

def imp (p q : FirstOrderMatrix Γ Δ) : FirstOrderMatrix Γ Δ :=
  ∼₁ₘ p ∨₁ₘ q

infixr:54 " ⊃₁ₘ " => imp

abbrev Quantified (Γ : RealContext) (Δ : BoundContext) :=
  PM.Quantified (FirstOrderMatrix Γ) Δ

end FirstOrderMatrix

namespace SecondOrder

def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    SecondOrder Γ Δ → SecondOrder Ξ Δ
  | Quantified.always (Quantified.always body) =>
      Quantified.always (Quantified.always (Apparent.renameReal ρ body))
  | Quantified.always (Quantified.sometimes body) =>
      Quantified.always (Quantified.sometimes (Apparent.renameReal ρ body))
  | Quantified.sometimes (Quantified.always body) =>
      Quantified.sometimes (Quantified.always (Apparent.renameReal ρ body))
  | Quantified.sometimes (Quantified.sometimes body) =>
      Quantified.sometimes (Quantified.sometimes (Apparent.renameReal ρ body))

end SecondOrder

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

def abstractRealOuter : FirstOrder (.elementaryProposition :: Γ) Δ →
    FirstOrder Γ (.elementaryProposition :: Δ)
  | Quantified.always body => Quantified.always (Apparent.abstractRealOuter body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.abstractRealOuter body)

def openRealOuter : FirstOrder Γ (.elementaryProposition :: Δ) →
    FirstOrder (.elementaryProposition :: Γ) Δ
  | Quantified.always body => Quantified.always (Apparent.openRealOuter body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.openRealOuter body)

@[simp] theorem openRealOuter_abstractRealOuter
    (proposition : FirstOrder (.elementaryProposition :: Γ) Δ) :
    openRealOuter (abstractRealOuter proposition) = proposition := by
  cases proposition with
  | always body =>
      change Quantified.always
        (Apparent.openRealOuter (Apparent.abstractRealOuter body)) =
          Quantified.always body
      rw [Apparent.openRealOuter_abstractRealOuter]
  | sometimes body =>
      change Quantified.sometimes
        (Apparent.openRealOuter (Apparent.abstractRealOuter body)) =
          Quantified.sometimes body
      rw [Apparent.openRealOuter_abstractRealOuter]

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

def instantiate (body : FirstOrder Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : FirstOrder Γ Δ :=
  substitute (Apparent.instantiateSubstitution argument) body

def atReal (body : FirstOrder Γ [.elementaryProposition])
    (x : RealVar Γ .elementaryProposition) : FirstOrder Γ [] :=
  instantiate body (.real x)

@[simp] theorem instantiate_always
    (body : Apparent Γ (.elementaryProposition :: .elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) :
    instantiate (always body) argument =
      always (Apparent.substitute
        (Apparent.liftSubstitution (Apparent.instantiateSubstitution argument)) body) := rfl

@[simp] theorem instantiate_sometimes
    (body : Apparent Γ (.elementaryProposition :: .elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) :
    instantiate (sometimes body) argument =
      sometimes (Apparent.substitute
        (Apparent.liftSubstitution (Apparent.instantiateSubstitution argument)) body) := rfl

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

def disjRightMatrix : FirstOrder Γ Δ → Apparent Γ Δ → FirstOrder Γ Δ
  | Quantified.always body, proposition =>
      always (body ∨ₐ Apparent.weaken proposition)
  | Quantified.sometimes body, proposition =>
      sometimes (body ∨ₐ Apparent.weaken proposition)

def disjElementaryLeft : Elementary Γ → FirstOrder Γ Δ → FirstOrder Γ Δ
  | proposition, Quantified.always body =>
      always (Apparent.ofElementary proposition ∨ₐ body)
  | proposition, Quantified.sometimes body =>
      sometimes (Apparent.ofElementary proposition ∨ₐ body)

def disjMatrixLeft : Apparent Γ Δ → FirstOrder Γ Δ → FirstOrder Γ Δ
  | proposition, Quantified.always body =>
      always (Apparent.weaken proposition ∨ₐ body)
  | proposition, Quantified.sometimes body =>
      sometimes (Apparent.weaken proposition ∨ₐ body)

def impElementaryToFirst (proposition : Elementary Γ) :
    FirstOrder Γ Δ → FirstOrder Γ Δ :=
  disjElementaryLeft (Elementary.neg proposition)

def impFirstToMatrix (proposition : FirstOrder Γ Δ)
    (conclusion : Apparent Γ Δ) : FirstOrder Γ Δ :=
  disjRightMatrix (neg proposition) conclusion

@[simp] theorem star_9_03_matrix_reduction
    (body : Apparent Γ (.elementaryProposition :: Δ))
    (proposition : Apparent Γ Δ) :
    disjRightMatrix (always body) proposition =
      always (body ∨ₐ Apparent.weaken proposition) := rfl

@[simp] theorem star_9_04_matrix_reduction
    (proposition : Apparent Γ Δ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    disjMatrixLeft proposition (always body) =
      always (Apparent.weaken proposition ∨ₐ body) := rfl

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

namespace FirstOrderMatrix

def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    FirstOrderMatrix Γ Δ → FirstOrderMatrix Ξ Δ
  | .quantified proposition => .quantified (FirstOrder.renameReal ρ proposition)
  | .neg proposition => .neg (renameReal ρ proposition)
  | .disj left right => .disj (renameReal ρ left) (renameReal ρ right)

def rename (ρ : Apparent.Renaming Δ Ξ) :
    FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Ξ
  | .quantified proposition => .quantified (FirstOrder.rename ρ proposition)
  | .neg proposition => .neg (rename ρ proposition)
  | .disj left right => .disj (rename ρ left) (rename ρ right)

def weaken (proposition : FirstOrderMatrix Γ Δ) :
    FirstOrderMatrix Γ (.elementaryProposition :: Δ) :=
  rename (fun v => .succ v) proposition

def substitute (σ : Apparent.Substitution Γ Δ Ξ) :
    FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Ξ
  | .quantified proposition => .quantified (FirstOrder.substitute σ proposition)
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

def renameQuantified (ρ : Apparent.Renaming Δ Ξ) :
    Quantified Γ Δ → Quantified Γ Ξ
  | PM.Quantified.always body =>
      PM.Quantified.always (rename (Apparent.liftRenaming ρ) body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (rename (Apparent.liftRenaming ρ) body)

def substituteQuantified (σ : Apparent.Substitution Γ Δ Ξ) :
    Quantified Γ Δ → Quantified Γ Ξ
  | PM.Quantified.always body =>
      PM.Quantified.always (substitute (Apparent.liftSubstitution σ) body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (substitute (Apparent.liftSubstitution σ) body)

def instantiate (body : FirstOrderMatrix Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : FirstOrderMatrix Γ Δ :=
  substitute (Apparent.instantiateSubstitution argument) body

def atReal (body : FirstOrderMatrix Γ [.elementaryProposition])
    (x : RealVar Γ .elementaryProposition) : FirstOrderMatrix Γ [] :=
  instantiate body (.real x)

def abstractRealOuter : FirstOrderMatrix (.elementaryProposition :: Γ) Δ →
    FirstOrderMatrix Γ (.elementaryProposition :: Δ)
  | .quantified proposition => .quantified (FirstOrder.abstractRealOuter proposition)
  | .neg proposition => .neg (abstractRealOuter proposition)
  | .disj left right => .disj (abstractRealOuter left) (abstractRealOuter right)

def openRealOuter : FirstOrderMatrix Γ (.elementaryProposition :: Δ) →
    FirstOrderMatrix (.elementaryProposition :: Γ) Δ
  | .quantified proposition => .quantified (FirstOrder.openRealOuter proposition)
  | .neg proposition => .neg (openRealOuter proposition)
  | .disj left right => .disj (openRealOuter left) (openRealOuter right)

@[simp] theorem openRealOuter_abstractRealOuter
    (proposition : FirstOrderMatrix (.elementaryProposition :: Γ) Δ) :
    openRealOuter (abstractRealOuter proposition) = proposition := by
  induction proposition with
  | quantified proposition => simp [abstractRealOuter, openRealOuter]
  | neg proposition ih => simp [abstractRealOuter, openRealOuter, ih]
  | disj left right ihLeft ihRight => simp [abstractRealOuter, openRealOuter, ihLeft, ihRight]

def ofSecondOrder : SecondOrder Γ Δ → Quantified Γ Δ
  | PM.Quantified.always body => PM.Quantified.always (.quantified body)
  | PM.Quantified.sometimes body => PM.Quantified.sometimes (.quantified body)

@[simp] theorem instantiate_quantified
    (body : FirstOrder Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) :
    instantiate (.quantified body) argument =
      .quantified (FirstOrder.instantiate body argument) := rfl

def impToQuantified (premise : FirstOrderMatrix Γ Δ) :
    Quantified Γ Δ → Quantified Γ Δ
  | PM.Quantified.always body =>
      PM.Quantified.always (imp (weaken premise) body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (imp (weaken premise) body)

def star_9_1_higher_target
    (body : FirstOrderMatrix Γ [.elementaryProposition])
    (value : RealVar Γ .elementaryProposition) : Quantified Γ [] :=
  impToQuantified (atReal body value) (PM.Quantified.sometimes body)

abbrev ThirdOrder (Γ : RealContext) (Δ : BoundContext) :=
  PM.Quantified (Quantified Γ) Δ

def renameQuantifiedReal (ρ : Apparent.RealRenaming Γ Ξ) :
    Quantified Γ Δ → Quantified Ξ Δ
  | PM.Quantified.always body => PM.Quantified.always (renameReal ρ body)
  | PM.Quantified.sometimes body => PM.Quantified.sometimes (renameReal ρ body)

def renameThirdReal (ρ : Apparent.RealRenaming Γ Ξ) :
    ThirdOrder Γ Δ → ThirdOrder Ξ Δ
  | PM.Quantified.always body =>
      PM.Quantified.always (renameQuantifiedReal ρ body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (renameQuantifiedReal ρ body)

def renameThird (ρ : Apparent.Renaming Δ Ξ) :
    ThirdOrder Γ Δ → ThirdOrder Γ Ξ
  | PM.Quantified.always body =>
      PM.Quantified.always (renameQuantified (Apparent.liftRenaming ρ) body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (renameQuantified (Apparent.liftRenaming ρ) body)

def substituteThird (σ : Apparent.Substitution Γ Δ Ξ) :
    ThirdOrder Γ Δ → ThirdOrder Γ Ξ
  | PM.Quantified.always body =>
      PM.Quantified.always (substituteQuantified (Apparent.liftSubstitution σ) body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (substituteQuantified (Apparent.liftSubstitution σ) body)

inductive ThirdOrderFormula (Γ : RealContext) (Δ : BoundContext) where
  | quantified : ThirdOrder Γ Δ → ThirdOrderFormula Γ Δ
  | neg : ThirdOrderFormula Γ Δ → ThirdOrderFormula Γ Δ
  | disj : ThirdOrderFormula Γ Δ → ThirdOrderFormula Γ Δ → ThirdOrderFormula Γ Δ

namespace ThirdOrderFormula

prefix:max "∼₃" => neg
infixl:55 " ∨₃ " => disj

def imp (p q : ThirdOrderFormula Γ Δ) : ThirdOrderFormula Γ Δ := ∼₃ p ∨₃ q
infixr:54 " ⊃₃ " => imp

def ofThirdOrder (proposition : ThirdOrder Γ Δ) : ThirdOrderFormula Γ Δ :=
  .quantified proposition

def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    ThirdOrderFormula Γ Δ → ThirdOrderFormula Ξ Δ
  | .quantified proposition => .quantified (renameThirdReal ρ proposition)
  | .neg proposition => .neg (renameReal ρ proposition)
  | .disj left right => .disj (renameReal ρ left) (renameReal ρ right)

def rename (ρ : Apparent.Renaming Δ Ξ) :
    ThirdOrderFormula Γ Δ → ThirdOrderFormula Γ Ξ
  | .quantified proposition => .quantified (renameThird ρ proposition)
  | .neg proposition => .neg (rename ρ proposition)
  | .disj left right => .disj (rename ρ left) (rename ρ right)

def weaken (proposition : ThirdOrderFormula Γ Δ) :
    ThirdOrderFormula Γ (.elementaryProposition :: Δ) :=
  rename (fun v => .succ v) proposition

def substitute (σ : Apparent.Substitution Γ Δ Ξ) :
    ThirdOrderFormula Γ Δ → ThirdOrderFormula Γ Ξ
  | .quantified proposition => .quantified (substituteThird σ proposition)
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

def instantiate (body : ThirdOrderFormula Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : ThirdOrderFormula Γ Δ :=
  substitute (Apparent.instantiateSubstitution argument) body

end ThirdOrderFormula

def abstractQuantifiedOuter : Quantified (.elementaryProposition :: Γ) Δ →
    Quantified Γ (.elementaryProposition :: Δ)
  | PM.Quantified.always body =>
      PM.Quantified.always (abstractRealOuter body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (abstractRealOuter body)

def abstractThirdOuter : Quantified (.elementaryProposition :: Γ) Δ →
    ThirdOrder Γ Δ :=
  PM.Quantified.always ∘ abstractQuantifiedOuter

@[simp] theorem impToQuantified_sometimes
    (premise : FirstOrderMatrix Γ Δ)
    (body : FirstOrderMatrix Γ (.elementaryProposition :: Δ)) :
    impToQuantified premise (PM.Quantified.sometimes body) =
      PM.Quantified.sometimes (imp (weaken premise) body) := rfl

@[simp] theorem star_9_1_higher_target_reduction
    (body : FirstOrderMatrix Γ [.elementaryProposition])
    (value : RealVar Γ .elementaryProposition) :
    star_9_1_higher_target body value =
      PM.Quantified.sometimes (imp (weaken (atReal body value)) body) := rfl

end FirstOrderMatrix
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

  | secondOrder : OrderedDisjunctionScope 2

inductive OrderedFormula (Γ : RealContext) : Nat → Type where
  | elementary : Elementary Γ → OrderedFormula Γ 0
  | firstOrder : FirstOrder Γ [] → OrderedFormula Γ 1

  | firstOrderMatrix : FirstOrderMatrix Γ [] → OrderedFormula Γ 1

  | secondOrder : SecondOrder Γ [] → OrderedFormula Γ 2

  | secondOrderMatrix : FirstOrderMatrix.Quantified Γ [] → OrderedFormula Γ 2

  | thirdOrderMatrix : FirstOrderMatrix.ThirdOrder Γ [] → OrderedFormula Γ 3

  | thirdOrderFormula : FirstOrderMatrix.ThirdOrderFormula Γ [] → OrderedFormula Γ 3
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

def secondImp (left right : OrderedFormula Γ 2) : OrderedFormula Γ 2 :=
  scopedImp .secondOrder left right

def always (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.always body)

def sometimes (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.sometimes body)

def alwaysFirstOrder (body : FirstOrder Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  .secondOrder (Quantified.always body)

def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    OrderedFormula Γ order → OrderedFormula Ξ order
  | .elementary p => .elementary (Elementary.schemaInstance (fun v => .var (ρ v)) p)
  | .firstOrder p => .firstOrder (FirstOrder.renameReal ρ p)
  | .firstOrderMatrix p => .firstOrderMatrix (FirstOrderMatrix.renameReal ρ p)
  | .secondOrder p => .secondOrder (SecondOrder.renameReal ρ p)
  | .secondOrderMatrix p =>
      .secondOrderMatrix (by
        cases p with
        | always body => exact .always (FirstOrderMatrix.renameReal ρ body)
        | sometimes body => exact .sometimes (FirstOrderMatrix.renameReal ρ body))
  | .thirdOrderMatrix p => .thirdOrderMatrix (FirstOrderMatrix.renameThirdReal ρ p)
  | .thirdOrderFormula p => .thirdOrderFormula (FirstOrderMatrix.ThirdOrderFormula.renameReal ρ p)
  | .neg p => .neg (renameReal ρ p)
  | .disj scope p q => .disj scope (renameReal ρ p) (renameReal ρ q)

def embedElementary (p : Elementary Γ) : OrderedFormula Γ 0 := .elementary p

def eraseElementary? : OrderedFormula Γ order → Option (Elementary Γ)
  | .elementary p => some p
  | .firstOrder _ => none
  | .firstOrderMatrix _ => none
  | .secondOrder _ => none
  | .secondOrderMatrix _ => none
  | .thirdOrderMatrix _ => none
  | .thirdOrderFormula _ => none
  | .neg p => (eraseElementary? p).map .neg
  | .disj .elementary p q => do
      let p ← eraseElementary? p
      let q ← eraseElementary? q
      pure (.disj p q)
  | .disj (.firstOrder _) _ _ => none
  | .disj .secondOrder _ _ => none

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

theorem instantiateSchema {Γ Ξ : PM.RealContext}
    (σ : PM.Elementary.SchemaAssignment Γ Ξ) {p : PM.Elementary Γ}
    (proof : PM.Derivation p) :
    PM.Derivation (PM.Elementary.schemaInstance σ p) := by
  induction proof with
  | star_1_1 hp hpq ihp ihpq =>
      cases Ξ with
      | nil => exact PM.Derivation.star_1_1 (ihp σ) (ihpq σ)
      | cons τ Δ =>
          exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) (ihp σ) (ihpq σ)
  | star_1_11 _ hp hpq ihp ihpq =>
      cases Ξ with
      | nil => exact PM.Derivation.star_1_1 (ihp σ) (ihpq σ)
      | cons τ Δ =>
          exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) (ihp σ) (ihpq σ)
  | star_1_2 p => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_2 (Γ := Ξ) (PM.Elementary.schemaInstance σ p))
  | star_1_3 p q => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_3 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q))
  | star_1_4 p q => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_4 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q))
  | star_1_5 p q r => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_5 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r))
  | star_1_6 p q r => simpa [PM.Elementary.imp, PM.Elementary.schemaInstance] using
      (PM.Derivation.star_1_6 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r))

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

-- PM-CONTEXT-PREDECLARATION PM1:✱2·05 PM.FirstEdition.Volume1.Star2.star_2_05
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_05 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.star_1_6 (∼ₚ p) q r

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-PREDECLARATION PM1:✱2·07 PM.FirstEdition.Volume1.Star2.star_2_07
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_07 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (p ∨ₚ p)) :=
  PM.Derivation.star_1_3 p p

end PM.FirstEdition.Volume1.Star2

-- PM-CONTEXT-PREDECLARATION PM1:✱2·08 PM.FirstEdition.Volume1.Star2.star_2_08
namespace PM.FirstEdition.Volume1.Star2

theorem star_2_08 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ p) :=
  PM.Derivation.detach (star_2_07 p)
    (PM.Derivation.detach (PM.Derivation.star_1_2 p)
      (star_2_05 p (p ∨ₚ p) p))

end PM.FirstEdition.Volume1.Star2

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

def star_9_1_instance_target (φ : Apparent Γ [.elementaryProposition])
    (value : Elementary Γ) : OrderedFormula Γ 1 :=
  .firstOrder
    (FirstOrder.impElementaryToFirst
      (Apparent.elementaryValue φ value)
      (FirstOrder.sometimes φ))

def star_9_1_higher_ordered_target
    (body : FirstOrderMatrix Γ [.elementaryProposition])
    (value : RealVar Γ .elementaryProposition) : OrderedFormula Γ 2 :=
  .secondOrderMatrix (FirstOrderMatrix.star_9_1_higher_target body value)

def star_9_13_higher_target
    (body : FirstOrderMatrix.Quantified (.elementaryProposition :: Γ) []) :
    OrderedFormula Γ 3 :=
  .thirdOrderMatrix (FirstOrderMatrix.abstractThirdOuter body)

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

def star_9_3_line4_matrix (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder Γ [.elementaryProposition] :=
  let inner : FirstOrder Γ [.elementaryProposition] :=
    FirstOrder.always (Apparent.rename Apparent.innerVariableRenaming φ)
  FirstOrder.impFirstToMatrix (FirstOrder.disjMatrixLeft φ inner) φ

def star_9_3_line2_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 1 :=
  .firstOrder
    (FirstOrder.sometimes
      (matrixImp (Apparent.openHeadOrBound φ)
        (Apparent.ofElementary (Apparent.openHead φ))))

def star_9_3_line4_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  firstOrderToSecondAll (star_9_3_line4_matrix φ)

def star_9_23_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp (OrderedFormula.always φ) (OrderedFormula.always φ)

def star_9_22_target (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp (OrderedFormula.always (matrixImp φ ψ))
    (firstImp (OrderedFormula.sometimes φ) (OrderedFormula.sometimes ψ))

def star_9_24_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp (OrderedFormula.sometimes φ) (OrderedFormula.sometimes φ)

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

  | star_9_1_instance (φ : Apparent Γ [.elementaryProposition])
      (value : Elementary Γ) :
      OrderedAssertion (star_9_1_instance_target φ value)

  | star_9_1_higher (body : FirstOrderMatrix Γ [.elementaryProposition])
      (value : RealVar Γ .elementaryProposition) :
      OrderedAssertion (star_9_1_higher_ordered_target body value)

  | star_9_13_higher
      (body : FirstOrderMatrix.Quantified (.elementaryProposition :: Γ) []) :
      OrderedAssertion (.secondOrderMatrix body) →
      OrderedAssertion (star_9_13_higher_target body)

  | star_9_11 (φ : Apparent Γ [.elementaryProposition]) :
      OrderedAssertion (star_9_11_target φ)

  | star_9_12 {p q : OrderedFormula Γ 1} :
      OrderedAssertion p → OrderedAssertion (firstImp p q) →
      OrderedAssertion q

  | star_9_12_second {p q : OrderedFormula Γ 2} :
      OrderedAssertion p → OrderedAssertion (secondImp p q) →
      OrderedAssertion q

  | star_9_12_higher
      (body : FirstOrderMatrix Γ [.elementaryProposition])
      (value : RealVar Γ .elementaryProposition)
      (premise : FirstOrder Γ []) :
      FirstOrderMatrix.atReal body value = .quantified premise →
      OrderedAssertion (.firstOrder premise) →
      OrderedAssertion (star_9_1_higher_ordered_target body value) →
      OrderedAssertion (.secondOrderMatrix (PM.Quantified.sometimes body))

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
        (.firstOrder (FirstOrder.openRealOuter φ)) →
      OrderedAssertion (firstOrderToSecondAll φ)

def derive_star_9_3_line2 (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_3_line2_target φ) := by
  let χ : Apparent (.elementaryProposition :: Γ) [.elementaryProposition] :=
    matrixImp (Apparent.openHeadOrBound φ)
      (Apparent.ofElementary (Apparent.openHead φ))
  have line1 : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary ((Apparent.openHead φ ∨ₚ Apparent.openHead φ) ⊃ₚ
        Apparent.openHead φ)) :=
    .elementary (PM.Derivation.star_1_2 (Apparent.openHead φ))
  have lineOneInstance : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.firstOrder
        (FirstOrder.impElementaryToFirst
          ((Apparent.openHead φ ∨ₚ Apparent.openHead φ) ⊃ₚ Apparent.openHead φ)
          (FirstOrder.sometimes χ))) := by
    simpa [star_9_1_instance_target, χ, matrixImp, Apparent.openHeadOrBound,
      Apparent.elementaryValue, Apparent.weakenReal, Apparent.renameReal,
      Apparent.rename] using
      OrderedAssertion.star_9_1_instance χ (.var .zero)
  exact OrderedAssertion.star_9_12_elementary_to_first line1 lineOneInstance

def star_9_3_line3_matrix (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder Γ [.elementaryProposition] :=
  FirstOrder.abstractRealOuter
    (FirstOrder.sometimes
      (matrixImp (Apparent.openHeadOrBound φ)
        (Apparent.ofElementary (Apparent.openHead φ))))

def star_9_3_line3_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  firstOrderToSecondAll (star_9_3_line3_matrix φ)

theorem star_9_3_line3_to_line4 (φ : Apparent Γ [.elementaryProposition]) :
    star_9_3_line3_matrix φ = star_9_3_line4_matrix φ := by
  simp only [star_9_3_line3_matrix, star_9_3_line4_matrix,
    FirstOrder.abstractRealOuter, FirstOrder.impFirstToMatrix,
    FirstOrder.disjMatrixLeft, FirstOrder.disjRightMatrix, FirstOrder.neg,
    Quantified.neg, matrixImp, Apparent.openHeadOrBound,
    Apparent.abstractRealOuter, Apparent.abstractRealOuter_ofElementary_openHead]
  rw [← Apparent.abstractRealOuter_weakenReal φ]

def derive_star_9_3_line3 (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_3_line3_target φ) := by
  have line2 : OrderedAssertion
      (.firstOrder (FirstOrder.openRealOuter (star_9_3_line3_matrix φ))) := by
    simpa [star_9_3_line2_target, star_9_3_line3_matrix] using
      derive_star_9_3_line2 φ
  simpa [star_9_3_line3_target] using
    OrderedAssertion.star_9_13_first (star_9_3_line3_matrix φ) line2

def derive_star_9_3_line4 (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_3_line4_target φ) := by
  change OrderedAssertion (firstOrderToSecondAll (star_9_3_line4_matrix φ))
  rw [← star_9_3_line3_to_line4 φ]
  exact derive_star_9_3_line3 φ

def derive_star_9_21_line2 (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.firstOrder (FirstOrder.sometimes
        (matrixImp
          (Apparent.ofElementary ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
          (matrixImp (Apparent.weakenReal φ)
            (Apparent.ofElementary (Apparent.openHead ψ)))))) := by
  let χ : Apparent (.elementaryProposition :: Γ) [.elementaryProposition] :=
    matrixImp
      (Apparent.ofElementary ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
      (matrixImp (Apparent.weakenReal φ)
        (Apparent.ofElementary (Apparent.openHead ψ)))
  have line1 : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary (((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ) ⊃ₚ
        ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))) :=
    .elementary (PM.FirstEdition.Volume1.Star2.star_2_08
      ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
  have lineOneInstance : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.firstOrder (FirstOrder.impElementaryToFirst
        (((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ) ⊃ₚ
          ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
        (FirstOrder.sometimes χ))) := by
    simpa [star_9_1_instance_target, χ, matrixImp, Apparent.elementaryValue,
      Apparent.weakenReal, Apparent.renameReal, Apparent.rename] using
      OrderedAssertion.star_9_1_instance χ (.var .zero)
  exact OrderedAssertion.star_9_12_elementary_to_first line1 lineOneInstance

def star_9_21_line3_matrix (φ ψ : Apparent Γ [.elementaryProposition]) :
    FirstOrderMatrix (.elementaryProposition :: Γ)
      [.elementaryProposition] :=
  let φx := Apparent.rename (fun _ => .succ .zero) (Apparent.weakenReal φ)
  let ψx := Apparent.rename (fun _ => .succ .zero) (Apparent.weakenReal ψ)
  let φy := Apparent.rename (fun _ => .zero) (Apparent.weakenReal φ)
  let ψz : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: .elementaryProposition :: []) :=
    Apparent.ofElementary (Apparent.openHead ψ)
  .quantified (FirstOrder.sometimes (matrixImp (matrixImp φx ψx)
    (matrixImp φy ψz)))

@[simp] theorem star_9_21_line3_matrix_beta
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    FirstOrderMatrix.atReal (star_9_21_line3_matrix φ ψ) .zero =
      .quantified (FirstOrder.sometimes
        (matrixImp
          (Apparent.ofElementary ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
          (matrixImp (Apparent.weakenReal φ)
            (Apparent.ofElementary (Apparent.openHead ψ))))) := by
  simp only [FirstOrderMatrix.atReal, FirstOrderMatrix.instantiate,
    FirstOrderMatrix.substitute, FirstOrder.substitute, star_9_21_line3_matrix]
  change FirstOrderMatrix.quantified (FirstOrder.sometimes
    (Apparent.substitute _ (matrixImp (matrixImp _ _) (matrixImp _ _)))) =
    FirstOrderMatrix.quantified (FirstOrder.sometimes _)
  simp only [matrixImp, Apparent.substitute]
  rw [Apparent.substitute_liftInstantiate_renameOuter_weakenReal,
    Apparent.substitute_liftInstantiate_renameOuter_weakenReal,
    Apparent.substitute_liftInstantiate_renameInner_weakenReal,
    Apparent.substitute_liftInstantiate_ofElementary]
  rfl

def derive_star_9_21_line3 (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (.secondOrderMatrix
      (PM.Quantified.sometimes (star_9_21_line3_matrix φ ψ))) := by
  apply OrderedAssertion.star_9_12_higher (star_9_21_line3_matrix φ ψ) .zero
    (FirstOrder.sometimes
      (matrixImp
        (Apparent.ofElementary ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
        (matrixImp (Apparent.weakenReal φ)
          (Apparent.ofElementary (Apparent.openHead ψ)))))
  · exact star_9_21_line3_matrix_beta φ ψ
  · exact derive_star_9_21_line2 φ ψ
  · exact OrderedAssertion.star_9_1_higher (star_9_21_line3_matrix φ ψ) .zero

def derive_star_9_21_line4 (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_13_higher_target
      (PM.Quantified.sometimes (star_9_21_line3_matrix φ ψ))) :=
  OrderedAssertion.star_9_13_higher
    (PM.Quantified.sometimes (star_9_21_line3_matrix φ ψ))
    (derive_star_9_21_line3 φ ψ)

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

def derive_star_9_24 (φ : Apparent Γ [.elementaryProposition])
    (elementaryId : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary (Apparent.openHead (matrixImp φ φ))))
    (existentialMonotonicity : OrderedAssertion (star_9_22_target φ φ)) :
    OrderedAssertion (star_9_24_target φ) :=
  OrderedAssertion.star_9_12
    (OrderedAssertion.star_9_13 (matrixImp φ φ) elementaryId)
    existentialMonotonicity

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

-- PM-CONTEXT-LOCAL Principia/Syntax/CanonicalOrderedFormula.lean
namespace PM.CanonicalOrderedFormula

inductive Quantifier where
  | always | sometimes
  deriving DecidableEq, Repr

inductive Raw : RealContext → Type where
  | elementary : Elementary Γ → Raw Γ

  | schema : Nat → Raw Γ
  | bound : Nat → Raw Γ
  | quantified : Quantifier → Raw Γ → Raw Γ
  | neg : Raw Γ → Raw Γ
  | disj : Raw Γ → Raw Γ → Raw Γ
  deriving DecidableEq, Repr

def openOuterAt (cutoff : Nat) : Raw Γ → Raw (.elementaryProposition :: Γ)
  | .elementary p => .elementary
      (Elementary.schemaInstance (fun v => .var (.succ v)) p)
  | .schema slot => .schema slot
  | .bound index =>
      if index < cutoff + 1 then .bound index
      else if index = cutoff + 1 then .elementary (.var .zero)
      else .bound (index - 1)
  | .quantified q body => .quantified q (openOuterAt (cutoff + 1) body)
  | .neg p => .neg (openOuterAt cutoff p)
  | .disj p q => .disj (openOuterAt cutoff p) (openOuterAt cutoff q)

def openOuter (p : Raw Γ) : Raw (.elementaryProposition :: Γ) :=
  openOuterAt 0 p

def abstractElementary : Elementary (.elementaryProposition :: Γ) → Raw Γ
  | .constant name => .elementary (.constant name)
  | .var .zero => .bound 1
  | .var (.succ v) => .elementary (.var v)
  | .neg p => .neg (abstractElementary p)
  | .disj p q => .disj (abstractElementary p) (abstractElementary q)

def abstractElementaryAt (cutoff : Nat) :
    Elementary (.elementaryProposition :: Γ) → Raw Γ
  | .constant name => .elementary (.constant name)
  | .var .zero => .bound (cutoff + 1)
  | .var (.succ v) => .elementary (.var v)
  | .neg p => .neg (abstractElementaryAt cutoff p)
  | .disj p q => .disj (abstractElementaryAt cutoff p) (abstractElementaryAt cutoff q)

def abstractOuterAt (cutoff : Nat) : Raw (.elementaryProposition :: Γ) → Raw Γ
  | .elementary p => abstractElementaryAt cutoff p
  | .schema slot => .schema slot
  | .bound index =>
      if index ≤ cutoff then .bound index else .bound (index + 1)
  | .quantified q body => .quantified q (abstractOuterAt (cutoff + 1) body)
  | .neg p => .neg (abstractOuterAt cutoff p)
  | .disj p q => .disj (abstractOuterAt cutoff p) (abstractOuterAt cutoff q)

def abstractOuter (p : Raw (.elementaryProposition :: Γ)) : Raw Γ :=
  abstractOuterAt 0 p

def Admissible (cutoff : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .schema _ => True
  | .bound index => index ≠ cutoff + 1
  | .quantified _ body => Admissible (cutoff + 1) body
  | .neg p => Admissible cutoff p
  | .disj p q => Admissible cutoff p ∧ Admissible cutoff q

def shiftIndex (cutoff index : Nat) : Nat :=
  if cutoff ≤ index then index + 1 else index

theorem shiftIndex_comm (i j index : Nat) (h : i ≤ j) :
    shiftIndex (j + 1) (shiftIndex i index) =
      shiftIndex i (shiftIndex j index) := by
  by_cases hi : i ≤ index
  · by_cases hj : j ≤ index
    · have hleft : j + 1 ≤ index + 1 := by omega
      have hright : i ≤ index + 1 := by omega
      simp [shiftIndex, hi, hj, hleft, hright]
    · have hleft : ¬ j + 1 ≤ index + 1 := by omega
      simp [shiftIndex, hi, hj, hleft]
  · have hj : ¬ j ≤ index := by omega
    have hleft : ¬ j + 1 ≤ index := by omega
    simp [shiftIndex, hi, hj, hleft]

def shiftBoundAt (cutoff : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .schema slot => .schema slot
  | .bound index => .bound (shiftIndex cutoff index)
  | .quantified q body => .quantified q (shiftBoundAt (cutoff + 1) body)
  | .neg p => .neg (shiftBoundAt cutoff p)
  | .disj p q => .disj (shiftBoundAt cutoff p) (shiftBoundAt cutoff q)

def weakenBound (p : Raw Γ) : Raw Γ := shiftBoundAt 0 p

theorem shiftBoundAt_comm (i j : Nat) (p : Raw Γ) (h : i ≤ j) :
    shiftBoundAt (j + 1) (shiftBoundAt i p) =
      shiftBoundAt i (shiftBoundAt j p) := by
  induction p generalizing i j with
  | elementary proposition => rfl
  | schema slot => rfl
  | bound index => exact congrArg Raw.bound (shiftIndex_comm i j index h)
  | quantified quantifier body ih =>
      simp only [shiftBoundAt]
      exact congrArg (Raw.quantified quantifier) (ih (i + 1) (j + 1) (by omega))
  | neg proposition ih =>
      simp only [shiftBoundAt]
      exact congrArg Raw.neg (ih i j h)
  | disj left right ihLeft ihRight =>
      simp only [shiftBoundAt]
      rw [ihLeft i j h, ihRight i j h]

theorem weakenBound_weakenBound_eq_shiftBoundAt_one (p : Raw Γ) :
    weakenBound (weakenBound p) = shiftBoundAt 1 (weakenBound p) := by
  simpa [weakenBound] using (shiftBoundAt_comm 0 0 p (by omega)).symm

def FreshBelowAt (depth count : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .schema _ => True
  | .bound index => index < depth ∨ depth + count ≤ index
  | .quantified _ body => FreshBelowAt (depth + 1) count body
  | .neg p => FreshBelowAt depth count p
  | .disj p q => FreshBelowAt depth count p ∧ FreshBelowAt depth count q

def FreshBelow (count : Nat) (p : Raw Γ) : Prop := FreshBelowAt 0 count p

theorem freshBelowAt_zero (depth : Nat) (p : Raw Γ) : FreshBelowAt depth 0 p := by
  induction p generalizing depth with
  | elementary proposition => trivial
  | schema slot => trivial
  | bound index =>
      by_cases below : index < depth
      · exact Or.inl below
      · exact Or.inr (by omega)
  | quantified quantifier body ih => exact ih (depth + 1)
  | neg proposition ih => exact ih depth
  | disj left right ihLeft ihRight => exact ⟨ihLeft depth, ihRight depth⟩

theorem freshBelowAt_shift (depth count : Nat) (p : Raw Γ) :
    FreshBelowAt depth count p →
      FreshBelowAt depth (count + 1) (shiftBoundAt depth p) := by
  intro fresh
  induction p generalizing depth count with
  | elementary proposition => trivial
  | schema slot => trivial
  | bound index =>
      simp only [FreshBelowAt, shiftBoundAt]
      rcases fresh with inner | external
      · have noShift : ¬ depth ≤ index := by omega
        simp [shiftIndex, noShift]
        exact Or.inl inner
      · have doShift : depth ≤ index := by omega
        simp [shiftIndex, doShift]
        exact Or.inr (by omega)
  | quantified quantifier body ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact ih (depth + 1) count fresh
  | neg proposition ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact ih depth count fresh
  | disj left right ihLeft ihRight =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact ⟨ihLeft depth count fresh.1, ihRight depth count fresh.2⟩

theorem shiftBoundAt_freshBelowAt (depth count : Nat) (p : Raw Γ)
    (fresh : FreshBelowAt depth count p) :
    shiftBoundAt (depth + count) p = shiftBoundAt depth p := by
  induction p generalizing depth count with
  | elementary proposition => rfl
  | schema slot => rfl
  | bound index =>
      simp only [FreshBelowAt] at fresh
      simp only [shiftBoundAt]
      rcases fresh with inner | external
      · have leftNo : ¬ depth + count ≤ index := by omega
        have rightNo : ¬ depth ≤ index := by omega
        simp [shiftIndex, leftNo, rightNo]
      · have leftYes : depth + count ≤ index := external
        have rightYes : depth ≤ index := by omega
        simp [shiftIndex, leftYes, rightYes]
  | quantified quantifier body ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      congr 1
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (depth + 1) count fresh
  | neg proposition ih =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      exact congrArg Raw.neg (ih depth count fresh)
  | disj left right ihLeft ihRight =>
      simp only [FreshBelowAt, shiftBoundAt] at fresh ⊢
      rw [ihLeft depth count fresh.1, ihRight depth count fresh.2]

def UnusedBoundAt (cutoff : Nat) : Raw Γ → Prop
  | .elementary _ => True
  | .schema _ => True
  | .bound index => index ≠ cutoff
  | .quantified _ body => UnusedBoundAt (cutoff + 1) body
  | .neg p => UnusedBoundAt cutoff p
  | .disj p q => UnusedBoundAt cutoff p ∧ UnusedBoundAt cutoff q

def dropUnusedBoundAt (cutoff : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .schema slot => .schema slot
  | .bound index =>
      if index < cutoff then .bound index else .bound (index - 1)
  | .quantified q body => .quantified q (dropUnusedBoundAt (cutoff + 1) body)
  | .neg p => .neg (dropUnusedBoundAt cutoff p)
  | .disj p q => .disj (dropUnusedBoundAt cutoff p) (dropUnusedBoundAt cutoff q)

def dropUnusedBound (p : Raw Γ) : Raw Γ := dropUnusedBoundAt 0 p

theorem shiftBoundAt_dropUnusedBoundAt
    (p : Raw Γ) (h : UnusedBoundAt cutoff p) :
    shiftBoundAt cutoff (dropUnusedBoundAt cutoff p) = p := by
  induction p generalizing cutoff with
  | elementary proposition => rfl
  | schema slot => rfl
  | bound index =>
      simp only [UnusedBoundAt] at h
      by_cases below : index < cutoff
      · have noShift : ¬ cutoff ≤ index := by omega
        simp [dropUnusedBoundAt, shiftBoundAt, shiftIndex, below, noShift]
      · have above : cutoff < index := by omega
        have shifted : cutoff ≤ index - 1 := by omega
        simp [dropUnusedBoundAt, shiftBoundAt, shiftIndex, below, shifted]
        omega
  | quantified quantifier body ih =>
      simp only [dropUnusedBoundAt, shiftBoundAt]
      exact congrArg (Raw.quantified quantifier) (ih h)
  | neg proposition ih =>
      simp only [dropUnusedBoundAt, shiftBoundAt]
      exact congrArg Raw.neg (ih h)
  | disj left right ihLeft ihRight =>
      simp only [dropUnusedBoundAt, shiftBoundAt] at h ⊢
      rw [ihLeft h.1, ihRight h.2]

theorem weakenBound_dropUnusedBound
    (p : Raw Γ) (h : UnusedBoundAt 0 p) :
    weakenBound (dropUnusedBound p) = p :=
  shiftBoundAt_dropUnusedBoundAt p h

def renameBound (ρ : Nat → Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .schema slot => .schema slot
  | .bound index => .bound (ρ index)
  | .quantified q body =>
      .quantified q (renameBound (fun index =>
        match index with | 0 => 0 | n + 1 => ρ n + 1) body)
  | .neg p => .neg (renameBound ρ p)
  | .disj p q => .disj (renameBound ρ p) (renameBound ρ q)

abbrev Substitution (Γ Ξ : RealContext) := Elementary Γ → Raw Ξ

namespace Substitution

def lift (σ : Substitution Γ Ξ) : Substitution Γ Ξ :=
  fun proposition => weakenBound (σ proposition)

def liftN : Nat → Substitution Γ Ξ → Substitution Γ Ξ
  | 0, σ => σ
  | n + 1, σ => lift (liftN n σ)

@[simp] theorem lift_apply (σ : Substitution Γ Ξ) (proposition : Elementary Γ) :
    lift σ proposition = weakenBound (σ proposition) := rfl

@[simp] theorem liftN_zero (σ : Substitution Γ Ξ) : liftN 0 σ = σ := rfl

@[simp] theorem liftN_succ (n : Nat) (σ : Substitution Γ Ξ) :
    liftN (n + 1) σ = lift (liftN n σ) := rfl

end Substitution

def substitute (σ : Substitution Γ Ξ) : Raw Γ → Raw Ξ
  | .elementary proposition => σ proposition
  | .schema slot => .schema slot
  | .bound index => .bound index
  | .quantified quantifier body =>
      .quantified quantifier (substitute (Substitution.lift σ) body)
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

@[simp] theorem substitute_elementary (σ : Substitution Γ Ξ)
    (proposition : Elementary Γ) :
    substitute σ (.elementary proposition) = σ proposition := rfl

@[simp] theorem substitute_bound (σ : Substitution Γ Ξ) (index : Nat) :
    substitute σ (.bound index) = .bound index := rfl

theorem substitution_liftN_fresh (σ : Substitution Γ Ξ)
    (count : Nat) (proposition : Elementary Γ) :
    FreshBelow count (Substitution.liftN count σ proposition) := by
  induction count with
  | zero => exact freshBelowAt_zero 0 _
  | succ count ih =>
      change FreshBelowAt 0 (count + 1)
        (shiftBoundAt 0 (Substitution.liftN count σ proposition))
      exact freshBelowAt_shift 0 count _ ih

theorem substitution_liftN_succ_as_shift (σ : Substitution Γ Ξ)
    (count : Nat) (proposition : Elementary Γ) :
    Substitution.liftN (count + 1) σ proposition =
      shiftBoundAt count (Substitution.liftN count σ proposition) := by
  change shiftBoundAt 0 (Substitution.liftN count σ proposition) = _
  simpa using (shiftBoundAt_freshBelowAt 0 count _
    (substitution_liftN_fresh σ count proposition)).symm

theorem substitute_liftN_shiftBoundAt (σ : Substitution Γ Ξ)
    (count : Nat) (p : Raw Γ) :
    substitute (Substitution.liftN (count + 1) σ) (shiftBoundAt count p) =
      shiftBoundAt count (substitute (Substitution.liftN count σ) p) := by
  induction p generalizing count with
  | elementary proposition =>
      exact substitution_liftN_succ_as_shift σ count proposition
  | schema slot => rfl
  | bound index => rfl
  | quantified quantifier body ih =>
      simp only [shiftBoundAt, substitute, Substitution.liftN_succ]
      exact congrArg (Raw.quantified quantifier) (ih (count + 1))
  | neg proposition ih =>
      simp only [shiftBoundAt, substitute]
      exact congrArg Raw.neg (ih count)
  | disj left right ihLeft ihRight =>
      simp only [shiftBoundAt, substitute]
      rw [ihLeft count, ihRight count]

theorem substitute_lift_weakenBound (σ : Substitution Γ Ξ) (p : Raw Γ) :
    substitute (Substitution.lift σ) (weakenBound p) =
      weakenBound (substitute σ p) := by
  simpa [weakenBound] using substitute_liftN_shiftBoundAt σ 0 p

abbrev SchemaSubstitution (Γ : RealContext) := Nat → Raw Γ

def substituteSchema (σ : SchemaSubstitution Γ) : Raw Γ → Raw Γ
  | .elementary proposition => .elementary proposition
  | .schema slot => σ slot
  | .bound index => .bound index
  | .quantified quantifier body =>
      .quantified quantifier
        (substituteSchema (fun slot => weakenBound (σ slot)) body)
  | .neg proposition => .neg (substituteSchema σ proposition)
  | .disj left right => .disj (substituteSchema σ left) (substituteSchema σ right)

def smartNeg : Raw Γ → Raw Γ
  | .quantified .always body => .quantified .sometimes (smartNeg body)
  | .quantified .sometimes body => .quantified .always (smartNeg body)
  | proposition => .neg proposition

def rawSize : Raw Γ → Nat
  | .elementary _ | .schema _ | .bound _ => 1
  | .quantified _ p | .neg p => rawSize p + 1
  | .disj p q => rawSize p + rawSize q + 1

def elementaryExpandedSize : Elementary Γ → Nat
  | .constant _ | .var _ => 1
  | .neg p => elementaryExpandedSize p + 1
  | .disj p q => elementaryExpandedSize p + elementaryExpandedSize q + 1

def expandedSize : Raw Γ → Nat
  | .elementary p => elementaryExpandedSize p
  | .schema _ | .bound _ => 1
  | .quantified _ p | .neg p => expandedSize p + 1
  | .disj p q => expandedSize p + expandedSize q + 1

@[simp] theorem expandedSize_shiftBoundAt (cutoff : Nat) (p : Raw Γ) :
    expandedSize (shiftBoundAt cutoff p) = expandedSize p := by
  induction p generalizing cutoff with
  | elementary proposition => rfl
  | schema slot => rfl
  | bound index => by_cases h : cutoff ≤ index <;>
      simp [shiftBoundAt, expandedSize, h]
  | quantified quantifier body ih => simp [shiftBoundAt, expandedSize, ih]
  | neg proposition ih => simp [shiftBoundAt, expandedSize, ih]
  | disj left right ihLeft ihRight =>
      simp [shiftBoundAt, expandedSize, ihLeft, ihRight]

@[simp] theorem expandedSize_abstractElementaryAt
    (cutoff : Nat) (p : Elementary (.elementaryProposition :: Γ)) :
    expandedSize (abstractElementaryAt cutoff p) = elementaryExpandedSize p := by
  induction p generalizing cutoff with
  | constant name => rfl
  | var v => cases v <;> rfl
  | neg proposition ih => simp [abstractElementaryAt, expandedSize,
      elementaryExpandedSize, ih]
  | disj left right ihLeft ihRight =>
      simp [abstractElementaryAt, expandedSize, elementaryExpandedSize,
        ihLeft, ihRight]

@[simp] theorem expandedSize_abstractOuterAt
    (cutoff : Nat) (p : Raw (.elementaryProposition :: Γ)) :
    expandedSize (abstractOuterAt cutoff p) = expandedSize p := by
  induction p generalizing cutoff with
  | elementary proposition => simp [abstractOuterAt, expandedSize]
  | schema slot => rfl
  | bound index => by_cases h : index ≤ cutoff <;>
      simp [abstractOuterAt, expandedSize, h]
  | quantified quantifier body ih => simp [abstractOuterAt, expandedSize, ih]
  | neg proposition ih => simp [abstractOuterAt, expandedSize, ih]
  | disj left right ihLeft ihRight =>
      simp [abstractOuterAt, expandedSize, ihLeft, ihRight]

def smartDisjAux : Nat → Raw Γ → Raw Γ → Raw Γ
  | 0, p, q => .disj p q
  | fuel + 1, .quantified .always p, .quantified .sometimes q =>
      .quantified .always (.quantified .sometimes
        (smartDisjAux fuel (weakenBound p) q))
  | fuel + 1, .quantified .sometimes p, .quantified .always q =>
      .quantified .always (.quantified .sometimes
        (smartDisjAux fuel (weakenBound p) q))
  | fuel + 1, .quantified q p, r =>
      .quantified q (smartDisjAux fuel p (weakenBound r))
  | fuel + 1, p, .quantified q r =>
      .quantified q (smartDisjAux fuel (weakenBound p) r)
  | _ + 1, p, q => .disj p q

def smartDisj (p q : Raw Γ) : Raw Γ :=
  smartDisjAux (rawSize p + rawSize q) p q

def smartDisjScopedAux : Nat → Nat → Raw Γ → Raw Γ → Raw Γ
  | _, 0, p, q => .disj p q
  | depth, fuel + 1, .quantified .always p, .quantified .sometimes q =>
      .quantified .always (.quantified .sometimes
        (smartDisjScopedAux (depth + 2) fuel
          (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)))
  | depth, fuel + 1, .quantified .sometimes p, .quantified .always q =>
      .quantified .always (.quantified .sometimes
        (smartDisjScopedAux (depth + 2) fuel
          (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)))
  | depth, fuel + 1, .quantified quantifier p, q =>
      .quantified quantifier
        (smartDisjScopedAux (depth + 1) fuel p (shiftBoundAt depth q))
  | depth, fuel + 1, p, .quantified quantifier q =>
      .quantified quantifier
        (smartDisjScopedAux (depth + 1) fuel (shiftBoundAt depth p) q)
  | _, _ + 1, p, q => .disj p q

def smartDisjScoped (p q : Raw Γ) : Raw Γ :=
  smartDisjScopedAux 0 (expandedSize p + expandedSize q + 1) p q

def smartImp (p q : Raw Γ) : Raw Γ := smartDisj (smartNeg p) q

theorem abstractOuterAt_smartNeg
    (cutoff : Nat) (p : Raw (.elementaryProposition :: Γ)) :
    abstractOuterAt cutoff (smartNeg p) =
      smartNeg (abstractOuterAt cutoff p) := by
  induction p generalizing cutoff with
  | quantified quantifier body ih =>
      cases quantifier <;>
        simp [smartNeg, abstractOuterAt, ih]
  | elementary proposition =>
      cases proposition with
      | constant name => rfl
      | var v => cases v <;> rfl
      | neg p => rfl
      | disj p q => rfl
  | bound index =>
      by_cases h : index ≤ cutoff <;>
        simp [smartNeg, abstractOuterAt, h]
  | _ => rfl

@[simp] theorem shiftBoundAt_elementary (p : Elementary Γ) :
    shiftBoundAt cutoff (.elementary p) = .elementary p := rfl

@[simp] theorem smartNeg_always (p : Raw Γ) :
    smartNeg (.quantified .always p) = .quantified .sometimes (smartNeg p) := rfl

end PM.CanonicalOrderedFormula

-- PM-CONTEXT-LOCAL Principia/Architecture/CanonicalOrderedAdapters.lean
namespace PM.Architecture.CanonicalOrderedAdapters

open PM.CanonicalOrderedFormula

def boundIndex : BoundVar Δ .elementaryProposition → Nat
  | .zero => 0
  | .succ v => boundIndex v + 1

def ofApparent : Apparent Γ Δ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound v => .bound (boundIndex v)
  | .neg p => .neg (ofApparent p)
  | .disj p q => .disj (ofApparent p) (ofApparent q)

def ofApparentAt (depth : Nat) : Apparent Γ Δ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .real v => .elementary (.var v)
  | .bound v => .bound (boundIndex v + depth)
  | .neg p => .neg (ofApparentAt depth p)
  | .disj p q => .disj (ofApparentAt depth p) (ofApparentAt depth q)

def ofFirstOrderAt (depth : Nat) : FirstOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofApparentAt (depth + 1) body)
  | .sometimes body => .quantified .sometimes (ofApparentAt (depth + 1) body)

def ofFirstOrder : FirstOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofApparent body)
  | .sometimes body => .quantified .sometimes (ofApparent body)

def ofFirstOrderMatrix : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrder p
  | .neg p => smartNeg (ofFirstOrderMatrix p)
  | .disj p q => smartDisj (ofFirstOrderMatrix p) (ofFirstOrderMatrix q)

def ofFirstOrderMatrixScoped : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrder p
  | .neg p => smartNeg (ofFirstOrderMatrixScoped p)
  | .disj p q =>
      smartDisjScoped (ofFirstOrderMatrixScoped p) (ofFirstOrderMatrixScoped q)

def smartDisjScopedAt (depth : Nat) (p q : Raw Γ) : Raw Γ :=
  smartDisjScopedAux depth (expandedSize p + expandedSize q + 1) p q

def ofFirstOrderMatrixScopedAt (depth : Nat) :
    FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrderAt depth p
  | .neg p => smartNeg (ofFirstOrderMatrixScopedAt depth p)
  | .disj p q => smartDisjScopedAt depth
      (ofFirstOrderMatrixScopedAt depth p)
      (ofFirstOrderMatrixScopedAt depth q)

def normalizeFirstOrderMatrixAfterAbstract (depth : Nat)
    (matrix : FirstOrderMatrix (.elementaryProposition :: Γ) Δ) : Raw Γ :=
  if depth = 0 then
    ofFirstOrderMatrixScoped (FirstOrderMatrix.abstractRealOuter matrix)
  else
    ofFirstOrderMatrixScopedAt depth
      (FirstOrderMatrix.abstractRealOuter matrix)

def ofFirstOrderMatrixRedex : FirstOrderMatrix Γ Δ → Raw Γ
  | .quantified p => ofFirstOrder p
  | .neg p => .neg (ofFirstOrderMatrixRedex p)
  | .disj p q =>
      .disj (ofFirstOrderMatrixRedex p) (ofFirstOrderMatrixRedex q)

structure ScopedFirstOrderMatrixReification
    (Δ : BoundContext) (raw : Raw Γ) where
  formula : FirstOrderMatrix Γ Δ
  roundTrip : ofFirstOrderMatrixScoped formula = raw

def reifyFirstOrderScoped (p : FirstOrder Γ Δ) :
    ScopedFirstOrderMatrixReification Δ (ofFirstOrder p) where
  formula := .quantified p
  roundTrip := rfl

def ScopedFirstOrderMatrixReification.neg
    (certificate : ScopedFirstOrderMatrixReification Δ raw) :
    ScopedFirstOrderMatrixReification Δ (smartNeg raw) where
  formula := .neg certificate.formula
  roundTrip := by simp [ofFirstOrderMatrixScoped, certificate.roundTrip]

def ScopedFirstOrderMatrixReification.disj
    (left : ScopedFirstOrderMatrixReification Δ p)
    (right : ScopedFirstOrderMatrixReification Δ q) :
    ScopedFirstOrderMatrixReification Δ (smartDisjScoped p q) where
  formula := .disj left.formula right.formula
  roundTrip := by
    simp [ofFirstOrderMatrixScoped, left.roundTrip, right.roundTrip]

def ofSecondOrder : SecondOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrder body)
  | .sometimes body => .quantified .sometimes (ofFirstOrder body)

def ofSecondMatrix : FirstOrderMatrix.Quantified Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrderMatrix body)
  | .sometimes body => .quantified .sometimes (ofFirstOrderMatrix body)

def ofSecondMatrixScoped : FirstOrderMatrix.Quantified Γ Δ → Raw Γ
  | .always body => .quantified .always (ofFirstOrderMatrixScoped body)
  | .sometimes body => .quantified .sometimes (ofFirstOrderMatrixScoped body)

def ofSecondMatrixScopedAt (depth : Nat) :
    FirstOrderMatrix.Quantified Γ Δ → Raw Γ
  | .always body => .quantified .always
      (ofFirstOrderMatrixScopedAt (depth + 1) body)
  | .sometimes body => .quantified .sometimes
      (ofFirstOrderMatrixScopedAt (depth + 1) body)

def ofThirdOrder : FirstOrderMatrix.ThirdOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofSecondMatrix body)
  | .sometimes body => .quantified .sometimes (ofSecondMatrix body)

def ofThirdOrderScoped : FirstOrderMatrix.ThirdOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofSecondMatrixScoped body)
  | .sometimes body => .quantified .sometimes (ofSecondMatrixScoped body)

def ofThirdOrderScopedAt (depth : Nat) :
    FirstOrderMatrix.ThirdOrder Γ Δ → Raw Γ
  | .always body => .quantified .always (ofSecondMatrixScopedAt (depth + 1) body)
  | .sometimes body =>
      .quantified .sometimes (ofSecondMatrixScopedAt (depth + 1) body)

def ofThirdOrderFormula : FirstOrderMatrix.ThirdOrderFormula Γ Δ → Raw Γ
  | .quantified p => ofThirdOrder p
  | .neg p => .neg (ofThirdOrderFormula p)
  | .disj p q => .disj (ofThirdOrderFormula p) (ofThirdOrderFormula q)

def ofThirdOrderFormulaScoped : FirstOrderMatrix.ThirdOrderFormula Γ Δ → Raw Γ
  | .quantified p => ofThirdOrderScoped p
  | .neg p => .neg (ofThirdOrderFormulaScoped p)
  | .disj p q =>
      .disj (ofThirdOrderFormulaScoped p) (ofThirdOrderFormulaScoped q)

def ofOrdered : OrderedFormula Γ order → Raw Γ
  | .elementary p => .elementary p
  | .firstOrder p => ofFirstOrder p
  | .firstOrderMatrix p => ofFirstOrderMatrix p
  | .secondOrder p => ofSecondOrder p
  | .secondOrderMatrix p => ofSecondMatrix p
  | .thirdOrderMatrix p => ofThirdOrder p
  | .thirdOrderFormula p => ofThirdOrderFormula p
  | .neg p => .neg (ofOrdered p)
  | .disj _ p q => .disj (ofOrdered p) (ofOrdered q)

def star_9_21_phi_x_raw (φ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.rename
    (fun _ => (.succ .zero : BoundVar
      (.elementaryProposition :: .elementaryProposition :: []) .elementaryProposition))
    (Apparent.weakenReal φ))

def star_9_21_psi_x_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.rename
    (fun _ => (.succ .zero : BoundVar
      (.elementaryProposition :: .elementaryProposition :: []) .elementaryProposition))
    (Apparent.weakenReal ψ))

def star_9_21_phi_y_raw (φ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.rename
    (fun _ => (.zero : BoundVar
      (.elementaryProposition :: .elementaryProposition :: []) .elementaryProposition))
    (Apparent.weakenReal φ))

def star_9_21_psi_z_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw
    (.elementaryProposition :: Γ) :=
  ofApparent (Apparent.ofElementary (Apparent.openHead ψ) :
    Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: .elementaryProposition :: []))

def closeLeadingRaw (p : Raw (.elementaryProposition :: Γ)) : Raw Γ :=
  abstractOuter p

def star_9_21_phi_x_closed_raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_phi_x_raw φ)

def star_9_21_psi_x_closed_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_psi_x_raw ψ)

def star_9_21_phi_y_closed_raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_phi_y_raw φ)

def star_9_21_psi_z_closed_raw (ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  closeLeadingRaw (star_9_21_psi_z_raw ψ)

@[simp] theorem ofApparent_neg (p : Apparent Γ Δ) :
    ofApparent (∼ₐ p) = .neg (ofApparent p) := rfl

theorem ofApparent_abstractRealOuter
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    ofApparent (Apparent.abstractRealOuter p) =
      abstractOuter (ofApparent p) := by
  induction p with
  | constant name => rfl
  | real realVariable => cases realVariable <;> rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ predecessor => rfl
  | neg proposition ih =>
      simp [ofApparent, Apparent.abstractRealOuter, abstractOuter,
        abstractOuterAt, ih]
  | disj left right ihLeft ihRight =>
      simp [ofApparent, Apparent.abstractRealOuter, abstractOuter,
        abstractOuterAt, ihLeft, ihRight]

theorem ofApparentAt_abstractRealOuter
    (depth : Nat)
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    ofApparentAt depth (Apparent.abstractRealOuter p) =
      abstractOuterAt depth (ofApparentAt depth p) := by
  induction p with
  | constant name => rfl
  | real realVariable => cases realVariable <;> simp [ofApparentAt,
      Apparent.abstractRealOuter, abstractOuterAt, abstractElementaryAt,
      boundIndex] <;> omega
  | bound boundVariable =>
      cases boundVariable with
      | zero => simp [ofApparentAt, Apparent.abstractRealOuter,
          abstractOuterAt, boundIndex]
      | succ predecessor =>
          have above : ¬ boundIndex predecessor + 1 + depth ≤ depth := by omega
          simp [ofApparentAt, Apparent.abstractRealOuter,
            abstractOuterAt, boundIndex, above]
          omega
  | neg proposition ih =>
      simp [ofApparentAt, Apparent.abstractRealOuter, abstractOuterAt, ih]
  | disj left right ihLeft ihRight =>
      simp [ofApparentAt, Apparent.abstractRealOuter, abstractOuterAt,
        ihLeft, ihRight]

theorem ofFirstOrderAt_abstractRealOuter
    (depth : Nat) (p : FirstOrder (.elementaryProposition :: Γ) Δ) :
    ofFirstOrderAt depth (FirstOrder.abstractRealOuter p) =
      abstractOuterAt depth (ofFirstOrderAt depth p) := by
  cases p <;>
    simp [FirstOrder.abstractRealOuter, ofFirstOrderAt, abstractOuterAt,
      ofApparentAt_abstractRealOuter]

theorem openOuter_ofApparent
    (p : Apparent Γ (.elementaryProposition :: .elementaryProposition :: Δ)) :
    openOuter (ofApparent p) = ofApparent (Apparent.openRealOuter p) := by
  induction p with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ predecessor =>
          cases predecessor with
          | zero => rfl
          | succ tail => rfl
  | neg proposition ih =>
      change Raw.neg (openOuter (ofApparent proposition)) =
        Raw.neg (ofApparent (Apparent.openRealOuter proposition))
      exact congrArg Raw.neg ih
  | disj left right ihLeft ihRight =>
      change Raw.disj (openOuter (ofApparent left)) (openOuter (ofApparent right)) =
        Raw.disj (ofApparent (Apparent.openRealOuter left))
          (ofApparent (Apparent.openRealOuter right))
      rw [ihLeft, ihRight]

theorem openOuter_abstractOuter_ofApparent
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    openOuter (abstractOuter (ofApparent p)) = ofApparent p := by
  rw [← ofApparent_abstractRealOuter]
  rw [openOuter_ofApparent]
  simp

theorem openOuter_star_9_21_phi_x_closed_raw
    (φ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_phi_x_closed_raw φ) = star_9_21_phi_x_raw φ :=
  openOuter_abstractOuter_ofApparent _

theorem openOuter_star_9_21_psi_x_closed_raw
    (ψ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_psi_x_closed_raw ψ) = star_9_21_psi_x_raw ψ :=
  openOuter_abstractOuter_ofApparent _

theorem openOuter_star_9_21_phi_y_closed_raw
    (φ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_phi_y_closed_raw φ) = star_9_21_phi_y_raw φ :=
  openOuter_abstractOuter_ofApparent _

theorem openOuter_star_9_21_psi_z_closed_raw
    (ψ : Apparent Γ [.elementaryProposition]) :
    openOuter (star_9_21_psi_z_closed_raw ψ) = star_9_21_psi_z_raw ψ :=
  openOuter_abstractOuter_ofApparent _

theorem star_9_21_phi_x_closed_unused_zero
    (φ : Apparent Γ [.elementaryProposition]) :
    UnusedBoundAt 0 (star_9_21_phi_x_closed_raw φ) := by
  induction φ with
  | constant name => trivial
  | real realVariable =>
      change True
      trivial
  | bound boundVariable =>
      cases boundVariable
      simp [star_9_21_phi_x_closed_raw, closeLeadingRaw,
        star_9_21_phi_x_raw, ofApparent, abstractOuter, abstractOuterAt,
        Apparent.weakenReal, Apparent.renameReal,
        UnusedBoundAt, boundIndex]
      rename_i impossible
      exact nomatch impossible
  | neg proposition ih =>
      exact ih
  | disj left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight⟩

theorem star_9_21_psi_x_closed_unused_zero
    (ψ : Apparent Γ [.elementaryProposition]) :
    UnusedBoundAt 0 (star_9_21_psi_x_closed_raw ψ) := by
  induction ψ with
  | constant name => trivial
  | real realVariable =>
      change True
      trivial
  | bound boundVariable =>
      cases boundVariable
      simp [star_9_21_psi_x_closed_raw, closeLeadingRaw,
        star_9_21_psi_x_raw, ofApparent, abstractOuter, abstractOuterAt,
        Apparent.weakenReal, Apparent.renameReal,
        UnusedBoundAt, boundIndex]
      rename_i impossible
      exact nomatch impossible
  | neg proposition ih => exact ih
  | disj left right ihLeft ihRight => exact ⟨ihLeft, ihRight⟩

theorem smartNeg_abstractOuter_ofApparent
    (p : Apparent (.elementaryProposition :: Γ)
      (.elementaryProposition :: Δ)) :
    smartNeg (abstractOuter (ofApparent p)) =
      abstractOuter (smartNeg (ofApparent p)) := by
  induction p with
  | constant name => rfl
  | real realVariable => cases realVariable <;> rfl
  | bound boundVariable => cases boundVariable <;> rfl
  | neg proposition ih => simp [ofApparent, smartNeg, abstractOuter, abstractOuterAt]
  | disj left right ihLeft ihRight =>
      simp [ofApparent, smartNeg, abstractOuter, abstractOuterAt]

def star_9_21_line4_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofThirdOrder (FirstOrderMatrix.abstractThirdOuter
    (PM.Quantified.sometimes
      (PM.Architecture.FirstOrderPrerequisites.star_9_21_line3_matrix φ ψ)))

def star_9_21_line4_explicit_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (ofFirstOrderMatrix (FirstOrderMatrix.abstractRealOuter
      (PM.Architecture.FirstOrderPrerequisites.star_9_21_line3_matrix φ ψ))))

theorem star_9_21_line4_raw_explicit
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    star_9_21_line4_raw φ ψ = star_9_21_line4_explicit_raw φ ψ := rfl

def rawImp (p q : Raw Γ) : Raw Γ := .disj (.neg p) q

def star_9_21_line4_named_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes (.quantified .sometimes
    (rawImp (rawImp (star_9_21_phi_x_closed_raw φ) (star_9_21_psi_x_closed_raw ψ))
      (rawImp (star_9_21_phi_y_closed_raw φ) (star_9_21_psi_z_closed_raw ψ)))))

def star_9_21_line5_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .sometimes
    (rawImp (dropUnusedBound
      (rawImp (star_9_21_phi_x_closed_raw φ) (star_9_21_psi_x_closed_raw ψ)))
      (.quantified .sometimes
        (rawImp (star_9_21_phi_y_closed_raw φ) (star_9_21_psi_z_closed_raw ψ)))))

def star_9_21_line6_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.quantified .sometimes
      (.neg (rawImp (star_9_21_phi_x_closed_raw φ) (star_9_21_psi_x_closed_raw ψ))))
    (.quantified .always (.quantified .sometimes
      (.disj (.neg (star_9_21_phi_y_closed_raw φ)) (star_9_21_psi_z_closed_raw ψ))))

def star_9_21_line7_raw (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  star_9_21_line6_raw φ ψ

theorem star_9_21_line4_raw_named
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    star_9_21_line4_raw φ ψ = star_9_21_line4_named_raw φ ψ := by
  change Raw.quantified .always (Raw.quantified .sometimes (Raw.quantified .sometimes
    (ofApparent (Apparent.abstractRealOuter
      (PM.Architecture.FirstOrderPrerequisites.matrixImp
        (PM.Architecture.FirstOrderPrerequisites.matrixImp _ _)
        (PM.Architecture.FirstOrderPrerequisites.matrixImp _ _)))))) = _
  simp only [PM.Architecture.FirstOrderPrerequisites.matrixImp,
    Apparent.abstractRealOuter, ofApparent]
  simp only [star_9_21_line4_named_raw, rawImp,
    star_9_21_phi_x_closed_raw, star_9_21_psi_x_closed_raw,
    star_9_21_phi_y_closed_raw, star_9_21_psi_z_closed_raw,
    closeLeadingRaw, star_9_21_phi_x_raw, star_9_21_psi_x_raw,
    star_9_21_phi_y_raw, star_9_21_psi_z_raw]
  rw [ofApparent_abstractRealOuter,
    ofApparent_abstractRealOuter,
    ofApparent_abstractRealOuter,
    ofApparent_abstractRealOuter]

end PM.Architecture.CanonicalOrderedAdapters

-- PM-CONTEXT-LOCAL Principia/Architecture/CanonicalNormalization.lean
namespace PM.Architecture.CanonicalNormalization

open PM.CanonicalOrderedFormula

inductive NormalizesScoped : Raw Γ → Raw Γ → Prop where
  | refl (p) : NormalizesScoped p p
  | negAlways (p) :
      NormalizesScoped (.neg (.quantified .always p))
        (.quantified .sometimes (.neg p))
  | negSometimes (p) :
      NormalizesScoped (.neg (.quantified .sometimes p))
        (.quantified .always (.neg p))

  | star_9_06_imp (p q) :
      NormalizesScoped (.quantified .sometimes
        (.disj (.neg (weakenBound p)) q))
        (.disj (.neg p) (.quantified .sometimes q))

  | star_9_21_line5_line6 (φ ψ : Apparent Γ [.elementaryProposition]) :
      NormalizesScoped
        (CanonicalOrderedAdapters.star_9_21_line5_raw φ ψ)
        (CanonicalOrderedAdapters.star_9_21_line6_raw φ ψ)
  | disjRight (q p r) :
      NormalizesScoped (.disj (.quantified q p) r)
        (.quantified q (.disj p (weakenBound r)))
  | disjLeft (q p r) :
      NormalizesScoped (.disj r (.quantified q p))
        (.quantified q (.disj (weakenBound r) p))

  | disjAlwaysSometimes (p q) :
      NormalizesScoped (.disj (.quantified .always p) (.quantified .sometimes q))
        (.quantified .always (.quantified .sometimes
          (.disj (weakenBound p) (shiftBoundAt 1 q))))

  | disjSometimesAlways (p q) :
      NormalizesScoped (.disj (.quantified .sometimes p) (.quantified .always q))
        (.quantified .always (.quantified .sometimes
          (.disj (weakenBound q) (shiftBoundAt 1 p))))
  | alwaysCongr : NormalizesScoped p q →
      NormalizesScoped (.quantified .always p) (.quantified .always q)
  | sometimesCongr : NormalizesScoped p q →
      NormalizesScoped (.quantified .sometimes p) (.quantified .sometimes q)
  | negCongr : NormalizesScoped p q →
      NormalizesScoped (.neg p) (.neg q)
  | disjCongr : NormalizesScoped p q → NormalizesScoped r s →
      NormalizesScoped (.disj p r) (.disj q s)
  | trans : NormalizesScoped p q → NormalizesScoped q r → NormalizesScoped p r

theorem normalizesSmartNeg (p : Raw Γ) :
    NormalizesScoped (.neg p) (smartNeg p) := by
  induction p with
  | quantified quantifier body ih =>
      cases quantifier
      · exact .trans (.negAlways body) (.sometimesCongr ih)
      · exact .trans (.negSometimes body) (.alwaysCongr ih)
  | _ => exact .refl _

inductive NormalizesScopedAt : Nat → Raw Γ → Raw Γ → Prop where
  | refl (depth) (p) : NormalizesScopedAt depth p p
  | negAlways (depth) (p) :
      NormalizesScopedAt depth (.neg (.quantified .always p))
        (.quantified .sometimes (.neg p))
  | negSometimes (depth) (p) :
      NormalizesScopedAt depth (.neg (.quantified .sometimes p))
        (.quantified .always (.neg p))
  | disjRight (depth) (q) (p r) :
      NormalizesScopedAt depth (.disj (.quantified q p) r)
        (.quantified q (.disj p (shiftBoundAt depth r)))
  | disjLeft (depth) (q) (p r) :
      NormalizesScopedAt depth (.disj r (.quantified q p))
        (.quantified q (.disj (shiftBoundAt depth r) p))
  | disjAlwaysSometimes (depth) (p q) :
      NormalizesScopedAt depth
        (.disj (.quantified .always p) (.quantified .sometimes q))
        (.quantified .always (.quantified .sometimes
          (.disj (shiftBoundAt (depth + 1) p)
            (shiftBoundAt (depth + 1) q))))
  | disjSometimesAlways (depth) (p q) :
      NormalizesScopedAt depth
        (.disj (.quantified .sometimes p) (.quantified .always q))
        (.quantified .always (.quantified .sometimes
          (.disj (shiftBoundAt (depth + 1) p)
            (shiftBoundAt (depth + 1) q))))

  | alwaysImpToSometimesAntecedent (depth) (p q) :
      NormalizesScopedAt depth
        (.quantified .always
          (.disj (.neg p) (shiftBoundAt depth q)))
        (.disj (.neg (.quantified .sometimes p)) q)

  | sometimesDisjToDisjSometimes (depth) (p q) :
      NormalizesScopedAt depth
        (.quantified .sometimes (.quantified .sometimes
          (.disj (shiftBoundAt (depth + 1) p)
            (shiftBoundAt (depth + 1) q))))
        (.disj (.quantified .sometimes p) (.quantified .sometimes q))

  | sometimesDisjIndependentLeft (depth) (p q) :
      NormalizesScopedAt depth
        (.quantified .sometimes
          (.disj (shiftBoundAt depth p) q))
        (.disj p (.quantified .sometimes q))

  | sometimesDisjIndependentLeftWitness (depth) (p q)
      (unused : UnusedBoundAt depth p) :
      NormalizesScopedAt depth
        (.quantified .sometimes (.disj p q))
        (.disj (dropUnusedBoundAt depth p) (.quantified .sometimes q))

  | sometimesSometimesDisjWitness (depth) (p q)
      (unused : UnusedBoundAt depth p) :
      NormalizesScopedAt depth
        (.quantified .sometimes (.quantified .sometimes (.disj p q)))
        (.disj
          (.quantified .sometimes (dropUnusedBoundAt depth p))
          (.quantified .sometimes q))
  | quantifiedCongr (depth) (q) : NormalizesScopedAt (depth + 1) p r →
      NormalizesScopedAt depth (.quantified q p) (.quantified q r)

  | quantifiedClosedCongr (q) : NormalizesScopedAt 0 p r →
      NormalizesScopedAt 0 (.quantified q p) (.quantified q r)
  | negCongr (depth) : NormalizesScopedAt depth p q →
      NormalizesScopedAt depth (.neg p) (.neg q)
  | disjCongr (depth) : NormalizesScopedAt depth p q →
      NormalizesScopedAt depth r s →
      NormalizesScopedAt depth (.disj p r) (.disj q s)
  | trans : NormalizesScopedAt depth p q → NormalizesScopedAt depth q r →
      NormalizesScopedAt depth p r

theorem star_9_07_at (depth : Nat) (p q : Raw Γ) :
    NormalizesScopedAt depth
      (.disj (.quantified .always p) (.quantified .sometimes q))
      (.quantified .always (.quantified .sometimes
        (.disj (shiftBoundAt (depth + 1) p)
          (shiftBoundAt (depth + 1) q)))) :=
  .disjAlwaysSometimes depth p q

theorem star_9_08_at (depth : Nat) (p q : Raw Γ) :
    NormalizesScopedAt depth
      (.disj (.quantified .sometimes p) (.quantified .always q))
      (.quantified .always (.quantified .sometimes
        (.disj (shiftBoundAt (depth + 1) p)
          (shiftBoundAt (depth + 1) q)))) :=
  .disjSometimesAlways depth p q

def smartDisjScopedCertifiedAux (depth : Nat) :
    (fuel : Nat) → (p q : Raw Γ) →
      { r : Raw Γ // NormalizesScopedAt depth (.disj p q) r }
  | 0, p, q => ⟨.disj p q, .refl _ _⟩
  | fuel + 1, .quantified .always p, .quantified .sometimes q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 2) fuel
        (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)
      ⟨.quantified .always (.quantified .sometimes recursive.1),
        .trans (.disjAlwaysSometimes depth p q)
          (.quantifiedCongr depth .always
            (.quantifiedCongr (depth + 1) .sometimes recursive.2))⟩
  | fuel + 1, .quantified .sometimes p, .quantified .always q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 2) fuel
        (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)
      ⟨.quantified .always (.quantified .sometimes recursive.1),
        .trans (.disjSometimesAlways depth p q)
          (.quantifiedCongr depth .always
            (.quantifiedCongr (depth + 1) .sometimes recursive.2))⟩
  | fuel + 1, .quantified quantifier p, q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 1) fuel p
        (shiftBoundAt depth q)
      ⟨.quantified quantifier recursive.1,
        .trans (.disjRight depth quantifier p q)
          (.quantifiedCongr depth quantifier recursive.2)⟩
  | fuel + 1, p, .quantified quantifier q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 1) fuel
        (shiftBoundAt depth p) q
      ⟨.quantified quantifier recursive.1,
        .trans (.disjLeft depth quantifier q p)
          (.quantifiedCongr depth quantifier recursive.2)⟩
  | _ + 1, p, q => ⟨.disj p q, .refl _ _⟩

theorem smartDisjScopedCertifiedAux_value
    (depth fuel : Nat) (p q : Raw Γ) :
    (smartDisjScopedCertifiedAux depth fuel p q).1 =
      smartDisjScopedAux depth fuel p q := by
  induction fuel generalizing depth p q with
  | zero => rfl
  | succ fuel ih =>
      cases p <;> cases q <;> try rfl
      all_goals try { cases ‹Quantifier› }
      all_goals try { cases ‹Quantifier› }
      all_goals try { simp [smartDisjScopedCertifiedAux, smartDisjScopedAux, ih] }
      case quantified.quantified qp p qq q =>
        cases qp <;> cases qq <;>
          simp [smartDisjScopedCertifiedAux, smartDisjScopedAux, ih]

theorem normalizesSmartDisjScopedAux
    (depth fuel : Nat) (p q : Raw Γ) :
    NormalizesScopedAt depth (.disj p q)
      (smartDisjScopedAux depth fuel p q) := by
  rw [← smartDisjScopedCertifiedAux_value depth fuel p q]
  exact (smartDisjScopedCertifiedAux depth fuel p q).property

theorem normalizesSmartDisjScoped (p q : Raw Γ) :
    NormalizesScopedAt 0 (.disj p q) (smartDisjScoped p q) := by
  exact normalizesSmartDisjScopedAux 0
    (expandedSize p + expandedSize q + 1) p q

theorem normalizesSmartNegAt (depth : Nat) (p : Raw Γ) :
    NormalizesScopedAt depth (.neg p) (smartNeg p) := by
  induction p generalizing depth with
  | quantified quantifier body ih =>
      cases quantifier
      · exact .trans (.negAlways depth body)
          (.quantifiedCongr depth .sometimes (ih (depth + 1)))
      · exact .trans (.negSometimes depth body)
          (.quantifiedCongr depth .always (ih (depth + 1)))
  | _ => exact .refl _ _

theorem normalizesFirstOrderMatrixRedexScoped
    (matrix : FirstOrderMatrix Γ Δ) :
    NormalizesScopedAt 0
      (CanonicalOrderedAdapters.ofFirstOrderMatrixRedex matrix)
      (CanonicalOrderedAdapters.ofFirstOrderMatrixScoped matrix) := by
  induction matrix with
  | quantified proposition => exact .refl _ _
  | neg matrix ih =>
      exact .trans (.negCongr 0 ih)
        (normalizesSmartNegAt 0 _)
  | disj left right ihLeft ihRight =>
      exact .trans (.disjCongr 0 ihLeft ihRight)
        (normalizesSmartDisjScoped _ _)

def Star921Line5Line6Stable : Prop :=
  ∀ {Γ Ξ} (σ : Substitution Γ Ξ)
    (φ ψ : Apparent Γ [.elementaryProposition]),
    NormalizesScoped
      (substitute σ (CanonicalOrderedAdapters.star_9_21_line5_raw φ ψ))
      (substitute σ (CanonicalOrderedAdapters.star_9_21_line6_raw φ ψ))

theorem NormalizesScoped.substitute
    (stable921 : Star921Line5Line6Stable)
    {p q : Raw Γ} (certificate : NormalizesScoped p q) (σ : Substitution Γ Ξ) :
    NormalizesScoped (CanonicalOrderedFormula.substitute σ p)
      (CanonicalOrderedFormula.substitute σ q) := by
  induction certificate generalizing Ξ with
  | refl p => exact .refl _
  | negAlways p => exact .negAlways _
  | negSometimes p => exact .negSometimes _
  | star_9_06_imp p q =>
      simpa [CanonicalOrderedFormula.substitute,
        CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.star_9_06_imp (CanonicalOrderedFormula.substitute σ p)
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) q)
  | star_9_21_line5_line6 φ ψ => exact stable921 σ φ ψ
  | disjRight quantifier p r =>
      simpa [CanonicalOrderedFormula.substitute,
        CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjRight quantifier
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute σ r)
  | disjLeft quantifier p r =>
      simpa [CanonicalOrderedFormula.substitute,
        CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjLeft quantifier
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute σ r)
  | disjAlwaysSometimes p q =>
      have commute := CanonicalOrderedFormula.substitute_liftN_shiftBoundAt σ 1 q
      simp only [Substitution.liftN_succ, Substitution.liftN_zero] at commute
      simp only [CanonicalOrderedFormula.substitute]
      rw [commute]
      simpa [CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjAlwaysSometimes
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) q)
  | disjSometimesAlways p q =>
      have commute := CanonicalOrderedFormula.substitute_liftN_shiftBoundAt σ 1 p
      simp only [Substitution.liftN_succ, Substitution.liftN_zero] at commute
      simp only [CanonicalOrderedFormula.substitute]
      rw [commute]
      simpa [CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjSometimesAlways
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) q)
  | alwaysCongr certificate ih =>
      simpa [CanonicalOrderedFormula.substitute] using
        NormalizesScoped.alwaysCongr (ih (Substitution.lift σ))
  | sometimesCongr certificate ih =>
      simpa [CanonicalOrderedFormula.substitute] using
        NormalizesScoped.sometimesCongr (ih (Substitution.lift σ))
  | negCongr certificate ih => exact .negCongr (ih σ)
  | disjCongr left right ihLeft ihRight => exact .disjCongr (ihLeft σ) (ihRight σ)
  | trans first second ihFirst ihSecond => exact .trans (ihFirst σ) (ihSecond σ)

end PM.Architecture.CanonicalNormalization

-- PM-CONTEXT-LOCAL Principia/Architecture/CanonicalOrderedJudgement.lean
namespace PM.Architecture.CanonicalOrderedJudgement

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalNormalization

def CanonicalOrderedAssertion (raw : Raw Γ) : Prop :=
  ∃ (order : Nat) (formula : OrderedFormula Γ order),
    OrderedAssertion formula ∧ ofOrdered formula = raw

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

def NormalizedCanonicalAssertion (raw : Raw Γ) : Prop :=
  ∃ (order : Nat) (formula : OrderedFormula Γ order),
    OrderedAssertion formula ∧ NormalizesScoped (ofOrdered formula) raw

structure ReifiedSubstitution (σ : Substitution Γ Ξ) where
  order : Elementary Γ → Nat
  formula : ∀ proposition : Elementary Γ, OrderedFormula Ξ (order proposition)
  proof : ∀ proposition : Elementary Γ, OrderedAssertion (formula proposition)
  roundTrip : ∀ proposition : Elementary Γ,
    ofOrdered (formula proposition) = σ proposition

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

def star_9_21_schema_raw : Raw Γ :=
  .disj
    (.quantified .sometimes (.neg (.disj (.neg (.schema 0)) (.schema 1))))
    (.quantified .always (.quantified .sometimes
      (.disj (.neg (.schema 0)) (.schema 1))))

@[simp] theorem substituteSchema_star_9_21_schema_raw
    (σ : SchemaSubstitution Γ) :
    substituteSchema σ star_9_21_schema_raw =
      .disj
        (.quantified .sometimes
          (.neg (.disj (.neg (weakenBound (σ 0))) (weakenBound (σ 1)))))
        (.quantified .always (.quantified .sometimes
          (.disj (.neg (weakenBound (weakenBound (σ 0))))
            (weakenBound (weakenBound (σ 1)))))) := rfl

theorem substituteSchema_star_9_21_schema_raw_scoped
    (σ : SchemaSubstitution Γ) :
    substituteSchema σ star_9_21_schema_raw =
      .disj
        (.quantified .sometimes
          (.neg (.disj (.neg (weakenBound (σ 0))) (weakenBound (σ 1)))))
        (.quantified .always (.quantified .sometimes
          (.disj (.neg (shiftBoundAt 1 (weakenBound (σ 0))))
            (shiftBoundAt 1 (weakenBound (σ 1)))))) := by
  rw [substituteSchema_star_9_21_schema_raw]
  rw [weakenBound_weakenBound_eq_shiftBoundAt_one,
    weakenBound_weakenBound_eq_shiftBoundAt_one]

def star_9_21_four_slot_template : Raw Γ :=
  .disj
    (.quantified .sometimes (.neg (.disj (.neg (.schema 0)) (.schema 1))))
    (.quantified .always (.quantified .sometimes
      (.disj (.neg (.schema 2)) (.schema 3))))

def evaluateStar921Slots (phiX psiX phiY psiZ : Raw Γ) : Raw Γ :=
  .disj
    (.quantified .sometimes (.neg (.disj (.neg phiX) psiX)))
    (.quantified .always (.quantified .sometimes
      (.disj (.neg phiY) psiZ)))

structure CoherentStar921Slots
    (φ ψ : Apparent Γ [.elementaryProposition]) where
  phiX : Raw Γ
  psiX : Raw Γ
  phiY : Raw Γ
  psiZ : Raw Γ
  phiXValue : phiX = star_9_21_phi_x_closed_raw φ
  psiXValue : psiX = star_9_21_psi_x_closed_raw ψ
  phiYValue : phiY = star_9_21_phi_y_closed_raw φ
  psiZValue : psiZ = star_9_21_psi_z_closed_raw ψ

def apparentStar921Slots (φ ψ : Apparent Γ [.elementaryProposition]) :
    CoherentStar921Slots φ ψ where
  phiX := star_9_21_phi_x_closed_raw φ
  psiX := star_9_21_psi_x_closed_raw ψ
  phiY := star_9_21_phi_y_closed_raw φ
  psiZ := star_9_21_psi_z_closed_raw ψ
  phiXValue := rfl
  psiXValue := rfl
  phiYValue := rfl
  psiZValue := rfl

theorem evaluateStar921Slots_apparent
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    evaluateStar921Slots
      (star_9_21_phi_x_closed_raw φ) (star_9_21_psi_x_closed_raw ψ)
      (star_9_21_phi_y_closed_raw φ) (star_9_21_psi_z_closed_raw ψ) =
      star_9_21_line7_raw φ ψ := rfl

def normalize {source target : Raw Γ}
    (certificate : NormalizesScoped source target)
    (assertion : CanonicalOrderedAssertion source) :
    NormalizedCanonicalAssertion target := by
  rcases assertion with ⟨order, formula, proof, equation⟩
  subst source
  exact ⟨order, formula, proof, certificate⟩

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

def derive_star_9_21_line7_normalized
    (φ ψ : Apparent Γ [.elementaryProposition]) :
    NormalizedCanonicalAssertion (star_9_21_line7_raw φ ψ) := by
  apply normalize (star_9_21_line4_line7_certificate φ ψ)
  exact image_of_ordered (derive_star_9_21_line4 φ ψ)

end PM.Architecture.CanonicalOrderedJudgement

-- PM-CONTEXT-LOCAL Principia/Architecture/Star921MatrixKernel.lean
namespace PM.Architecture.Star921MatrixKernel

open PM.Architecture.FirstOrderPrerequisites
open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

structure MatrixFunctionSchema (Γ : RealContext) where
  left : FirstOrder Γ [.elementaryProposition]
  right : Apparent Γ [.elementaryProposition]

def star_9_3_alpha (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder Γ [.elementaryProposition] :=
  FirstOrder.disjMatrixLeft φ
    (FirstOrder.always (Apparent.rename Apparent.innerVariableRenaming φ))

def star_9_3_beta (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] := φ

def star_9_3_matrix_schema (φ : Apparent Γ [.elementaryProposition]) :
    MatrixFunctionSchema Γ where
  left := star_9_3_alpha φ
  right := star_9_3_beta φ

theorem star_9_3_matrix_schema_line4
    (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder.impFirstToMatrix (star_9_3_matrix_schema φ).left
      (star_9_3_matrix_schema φ).right = star_9_3_line4_matrix φ := rfl

def matrixSchemaImpRaw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  ofFirstOrder (FirstOrder.impFirstToMatrix schema.left schema.right)

def star_9_21_matrix_line1_raw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  .disj (.neg (matrixSchemaImpRaw schema)) (matrixSchemaImpRaw schema)

def star_9_21_matrix_line2_raw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  .quantified .sometimes
    (.disj (.neg (weakenBound (matrixSchemaImpRaw schema)))
      (weakenBound (matrixSchemaImpRaw schema)))

def star_9_21_matrix_line5_raw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  .disj
    (.neg (.quantified .always (ofFirstOrder schema.left)))
    (.quantified .always (ofApparent schema.right))

def star_9_3_ordered_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  let p := OrderedFormula.always φ
  OrderedFormula.firstImp
    (OrderedFormula.scopedFirstOrderDisj .sameAssignedOrder p p) p

def star_9_3_line6_raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (star_9_3_ordered_target φ)

inductive Star921MatrixSchemaDerivation :
    (schema : MatrixFunctionSchema Γ) → Raw Γ → Prop where

  | matrixIdentity :
      Star921MatrixSchemaDerivation schema (star_9_21_matrix_line1_raw schema)

  | indexedLine4
      (proof : OrderedAssertion (star_9_3_line4_target φ))
      (h : schema = star_9_3_matrix_schema φ) :
      Star921MatrixSchemaDerivation schema (matrixSchemaImpRaw schema)
  | star_9_21_firstOrder_instance :
      Star921MatrixSchemaDerivation schema (matrixSchemaImpRaw schema) →
      Star921MatrixSchemaDerivation schema (star_9_21_matrix_line5_raw schema)

  | star_9_3_normalize (φ : Apparent Γ [.elementaryProposition]) :
      Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
        (star_9_21_matrix_line5_raw (star_9_3_matrix_schema φ)) →
      Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
        (star_9_3_line6_raw φ)

def star_9_21_firstOrder_instance
    (schema : MatrixFunctionSchema Γ)
    (line4 : Star921MatrixSchemaDerivation schema (matrixSchemaImpRaw schema)) :
    Star921MatrixSchemaDerivation schema (star_9_21_matrix_line5_raw schema) :=
  .star_9_21_firstOrder_instance line4

inductive Star93Normalization
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ → Raw Γ → Prop where
  | star_9_03 : Star93Normalization φ
      (star_9_21_matrix_line5_raw (star_9_3_matrix_schema φ))
      (star_9_3_line6_raw φ)

theorem star_9_3_matrix_line4_raw
    (φ : Apparent Γ [.elementaryProposition]) :
    matrixSchemaImpRaw (star_9_3_matrix_schema φ) =
      ofFirstOrder (star_9_3_line4_matrix φ) := rfl

def derive_star_9_3_line4_schema
    (φ : Apparent Γ [.elementaryProposition]) :
    Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
      (matrixSchemaImpRaw (star_9_3_matrix_schema φ)) :=
  .indexedLine4 (derive_star_9_3_line4 φ) rfl

def derive_star_9_3_line5_schema
    (φ : Apparent Γ [.elementaryProposition]) :
    Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
      (star_9_21_matrix_line5_raw (star_9_3_matrix_schema φ)) :=
  star_9_21_firstOrder_instance _ (derive_star_9_3_line4_schema φ)

def star_9_3_schema
    (φ : Apparent Γ [.elementaryProposition]) :
    Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
      (star_9_3_line6_raw φ) :=
  .star_9_3_normalize φ (derive_star_9_3_line5_schema φ)

abbrev Star9CanonicalAssertion (target : Raw Γ) : Prop :=
  CanonicalOrderedJudgement.NormalizedCanonicalAssertion target

inductive Star9KernelAssertion (formula : OrderedFormula Γ order) : Prop where
  | indexed (proof : OrderedAssertion formula) : Star9KernelAssertion formula
  | star_9_3_from_schema
      (φ : Apparent Γ [.elementaryProposition])
      (schemaProof : Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
        (star_9_3_line6_raw φ))
      (targetRaw : star_9_3_line6_raw φ = ofOrdered formula) :
      Star9KernelAssertion formula
  | star_9_21_from_normalized
      (φ ψ : Apparent Γ [.elementaryProposition])
      (normalized : CanonicalOrderedJudgement.NormalizedCanonicalAssertion
        (star_9_21_line7_raw φ ψ))
      (targetRaw : star_9_21_line7_raw φ ψ = ofOrdered formula) :
      Star9KernelAssertion formula
  | star_9_23_from_closed
      (φ : Apparent Γ [.elementaryProposition])
      (identity : OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.elementary (Apparent.openHead (matrixImp φ φ))))
      (monotonicity : Star9CanonicalAssertion (star_9_21_line7_raw φ φ))
      (targetRaw : ofOrdered formula = ofOrdered (star_9_23_target φ)) :
      Star9KernelAssertion formula

def derive_star_9_3
    (φ : Apparent Γ [.elementaryProposition]) :
    Star9KernelAssertion (star_9_3_ordered_target φ) :=
  .star_9_3_from_schema φ (star_9_3_schema φ) rfl

namespace Star9KernelAssertion

def star_9_21 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star9CanonicalAssertion (star_9_21_line7_raw φ ψ) :=
  CanonicalOrderedJudgement.derive_star_9_21_line7_normalized φ ψ

def star_9_23 (φ : Apparent Γ [.elementaryProposition]) :
    Star9KernelAssertion (star_9_23_target φ) :=
  .star_9_23_from_closed φ
    (.elementary (PM.FirstEdition.Volume1.Star2.star_2_08
      (Apparent.openHead φ)))
    (star_9_21 φ φ) rfl

end Star9KernelAssertion

end PM.Architecture.Star921MatrixKernel

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
  .firstOrder
    (FirstOrder.impElementaryToFirst q
      (FirstOrder.disjRightElementary (FirstOrder.always φ) q))

def star_9_33_target (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder
    (FirstOrder.impElementaryToFirst q
      (FirstOrder.disjRightElementary (FirstOrder.sometimes φ) q))

end PM.Architecture.FirstOrderQ259

-- PM-CONTEXT-LOCAL Principia/Architecture/Star931Kernel.lean
namespace PM.Architecture.Star931Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
open PM.CanonicalOrderedFormula

def primitivePayload (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: .elementaryProposition :: Γ) [] :=
  let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
  FirstOrder.impElementaryToFirst
    (Apparent.atReal lifted .zero ∨ₚ Apparent.atReal lifted (.succ .zero))
    (FirstOrder.weakenReal (FirstOrder.weakenReal (FirstOrder.sometimes φ)))

def line1Matrix (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.abstractRealOuter (primitivePayload φ)

def line1Formula (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 2 :=
  FirstOrderPrerequisites.firstOrderToSecondAll (line1Matrix φ)

theorem line1Ordered (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (line1Formula φ) := by
  apply OrderedAssertion.star_9_13_first (line1Matrix φ)
  simpa [line1Formula, line1Matrix, primitivePayload, star_9_11_target] using
    OrderedAssertion.star_9_11 φ

def line1Raw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofOrdered (line1Formula φ)

def targetRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (FirstOrderQ259.star_9_31_target φ)

abbrev Line2Matrix (φ : Apparent Γ [.elementaryProposition]) :=
  FirstOrderMatrix (.elementaryProposition :: Γ) [.elementaryProposition]

def line2Antecedent (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.sometimes (Apparent.abstractRealOuter
    (Apparent.ofElementary
      (let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
       Apparent.atReal lifted .zero ∨ₚ Apparent.atReal lifted (.succ .zero))))

def line2Consequent (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder (.elementaryProposition :: Γ) [.elementaryProposition] :=
  FirstOrder.sometimes
    (Apparent.abstractRealOuter (Apparent.weakenReal (Apparent.weakenReal φ)))

def line2ScopedRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  smartDisjScoped (smartNeg (ofFirstOrder (line2Antecedent φ)))
    (ofFirstOrder (line2Consequent φ))

def line2Reification (φ : Apparent Γ [.elementaryProposition]) :
    ScopedFirstOrderMatrixReification [.elementaryProposition]
      (line2ScopedRaw φ) :=
  (reifyFirstOrderScoped (line2Antecedent φ)).neg.disj
    (reifyFirstOrderScoped (line2Consequent φ))

def line2Formula (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrderMatrix (.elementaryProposition :: Γ) [.elementaryProposition] :=
  (line2Reification φ).formula

def line3Carrier (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrderMatrix.Quantified (.elementaryProposition :: Γ) [] :=
  .always (line2Formula φ)

def line3Target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 3 :=
  star_9_13_higher_target (line3Carrier φ)

def closedLine3Raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (line3Target φ)

def closedLine3ScopedRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofThirdOrderScoped
    (FirstOrderMatrix.abstractThirdOuter (line3Carrier φ))

theorem closedLine3Raw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    closedLine3Raw φ =
      .quantified .always (.quantified .always
        (ofFirstOrderMatrix
          (FirstOrderMatrix.abstractRealOuter (line2Formula φ)))) := by
  rfl

theorem closedLine3ScopedRaw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    closedLine3ScopedRaw φ =
      .quantified .always (.quantified .always
        (ofFirstOrderMatrixScoped
          (FirstOrderMatrix.abstractRealOuter (line2Formula φ)))) := by
  rfl

def closedLine3DisplayRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always
    (ofFirstOrderMatrixRedex
      (FirstOrderMatrix.abstractRealOuter (line2Formula φ))))

theorem closedMatrixRedex_shape
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrderMatrixRedex
        (FirstOrderMatrix.abstractRealOuter (line2Formula φ)) =
      .disj
        (.neg (ofFirstOrder
          (FirstOrder.abstractRealOuter (line2Antecedent φ))))
        (ofFirstOrder
          (FirstOrder.abstractRealOuter (line2Consequent φ))) := by
  rfl

def closedConsequentOutside (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofFirstOrder (FirstOrder.sometimes φ)

theorem ofApparent_abstract_inner_weakenReal
    (φ : Apparent Γ [.elementaryProposition]) :
    ofApparent (Apparent.abstractRealOuter
      (Apparent.rename Apparent.innerVariableRenaming
        (Apparent.weakenReal (τ := .elementaryProposition) φ))) =
      shiftBoundAt 1 (ofApparent φ) := by
  induction φ with
  | constant name => rfl
  | real v => rfl
  | bound v =>
      cases v with
      | zero => rfl
      | succ v => exact nomatch v
  | neg p ih => exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj _ _ = Raw.disj _ _
      simp only [Apparent.weakenReal] at ihp ihq
      rw [ihp, ihq]

theorem closedConsequent_is_weakened
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrder (FirstOrder.abstractRealOuter (line2Consequent φ)) =
      shiftBoundAt 0 (closedConsequentOutside φ) := by
  change Raw.quantified .sometimes
      (ofApparent (Apparent.abstractRealOuter
        (Apparent.abstractRealOuter
          (Apparent.weakenReal (Apparent.weakenReal φ))))) = _
  rw [Apparent.abstractRealOuter_weakenReal]
  exact congrArg (Raw.quantified .sometimes)
    (ofApparent_abstract_inner_weakenReal φ)

def closedLine4DisplayRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always
    (.disj
      (.neg (.quantified .sometimes
        (ofFirstOrder (FirstOrder.abstractRealOuter (line2Antecedent φ)))))
      (closedConsequentOutside φ))

theorem closedLine3_to_line4
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (closedLine3DisplayRaw φ)
      (closedLine4DisplayRaw φ) := by
  rw [closedLine3DisplayRaw, closedMatrixRedex_shape,
    closedConsequent_is_weakened]
  exact .quantifiedClosedCongr .always
    (.alwaysImpToSometimesAntecedent 0
      (ofFirstOrder (FirstOrder.abstractRealOuter (line2Antecedent φ)))
      (closedConsequentOutside φ))

def closedAntecedentLeftUnder (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofApparent (Apparent.abstractRealOuter (Apparent.abstractRealOuter
    ((Apparent.ofElementary
      (Apparent.atReal (Apparent.weakenReal (Apparent.weakenReal φ)) .zero)) :
        Apparent (.elementaryProposition :: .elementaryProposition :: Γ)
          [.elementaryProposition])))

def closedAntecedentRightBody (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofApparent (Apparent.abstractRealOuter (Apparent.abstractRealOuter
    ((Apparent.ofElementary
      (Apparent.atReal (Apparent.weakenReal (Apparent.weakenReal φ))
        (.succ .zero))) :
          Apparent (.elementaryProposition :: .elementaryProposition :: Γ)
            [.elementaryProposition])))

theorem closedAntecedentRedex_shape
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrder (FirstOrder.abstractRealOuter (line2Antecedent φ)) =
      .quantified .sometimes
        (.disj (closedAntecedentLeftUnder φ)
          (closedAntecedentRightBody φ)) := by
  rfl

theorem closedAntecedentLeft_unused
    (φ : Apparent Γ [.elementaryProposition]) :
    UnusedBoundAt 0 (closedAntecedentLeftUnder φ) := by
  induction φ with
  | constant name => simp [closedAntecedentLeftUnder, UnusedBoundAt,
      Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
      Apparent.substitute, Apparent.instantiateSubstitution,
      Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
      Apparent.rename, Apparent.abstractRealOuter, ofApparent]
  | real v => simp [closedAntecedentLeftUnder, UnusedBoundAt,
      Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
      Apparent.substitute, Apparent.instantiateSubstitution,
      Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
      Apparent.rename, Apparent.abstractRealOuter, ofApparent]
  | bound v =>
      cases v with
      | zero => simp [closedAntecedentLeftUnder, UnusedBoundAt,
          Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
          Apparent.substitute, Apparent.instantiateSubstitution,
          Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
          Apparent.rename, Apparent.abstractRealOuter, ofApparent, boundIndex]
      | succ v => exact nomatch v
  | neg p ih =>
      simpa [closedAntecedentLeftUnder, UnusedBoundAt,
        Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
        Apparent.substitute, Apparent.instantiateSubstitution,
        Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
        Apparent.rename, Apparent.abstractRealOuter, ofApparent] using ih
  | disj p q ihp ihq =>
      simpa [closedAntecedentLeftUnder, UnusedBoundAt,
        Apparent.ofElementary, Apparent.atReal, Apparent.instantiate,
        Apparent.substitute, Apparent.instantiateSubstitution,
        Apparent.closedToElementary, Apparent.weakenReal, Apparent.renameReal,
        Apparent.rename, Apparent.abstractRealOuter, ofApparent] using And.intro ihp ihq

def closedFinalDisplayRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always
    (.disj
      (.neg (.disj
        (.quantified .sometimes
          (dropUnusedBound (closedAntecedentLeftUnder φ)))
        (.quantified .sometimes (closedAntecedentRightBody φ))))
      (closedConsequentOutside φ))

def exactTargetRaw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always
    (.disj
      (.neg (.disj
        (.quantified .sometimes
          (dropUnusedBound (closedAntecedentLeftUnder φ)))
        (.quantified .sometimes (closedAntecedentRightBody φ))))
      (closedConsequentOutside φ))

theorem closedFinalDisplayRaw_eq_exactTargetRaw
    (φ : Apparent Γ [.elementaryProposition]) :
    closedFinalDisplayRaw φ = exactTargetRaw φ := by
  rfl

theorem closedLine4_to_final
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (closedLine4DisplayRaw φ)
      (closedFinalDisplayRaw φ) := by
  rw [closedLine4DisplayRaw, closedAntecedentRedex_shape]
  exact .quantifiedClosedCongr .always
    (.disjCongr 0
      (.negCongr 0
        (.sometimesSometimesDisjWitness 0
          (closedAntecedentLeftUnder φ) (closedAntecedentRightBody φ)
          (closedAntecedentLeft_unused φ)))
      (.refl 0 (closedConsequentOutside φ)))

theorem closedLine3_to_final
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (closedLine3DisplayRaw φ)
      (closedFinalDisplayRaw φ) :=
  .trans (closedLine3_to_line4 φ) (closedLine4_to_final φ)

def closedLine3NormalizedRaw
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always
    (normalizeFirstOrderMatrixAfterAbstract 0 (line2Formula φ)))

structure ClosedLine3NormalizationCertificate
    (φ : Apparent Γ [.elementaryProposition]) where
  matrix : FirstOrderMatrix Γ
    [.elementaryProposition, .elementaryProposition]
  matrixExact : matrix = FirstOrderMatrix.abstractRealOuter (line2Formula φ)
  sourceExact : closedLine3DisplayRaw φ =
    .quantified .always (.quantified .always
      (ofFirstOrderMatrixRedex matrix))
  targetExact : closedLine3NormalizedRaw φ =
    .quantified .always (.quantified .always
      (ofFirstOrderMatrixScoped matrix))
  normalization : NormalizesScopedAt 0
    (closedLine3DisplayRaw φ) (closedLine3NormalizedRaw φ)

def closedLine3NormalizationCertificate
    (φ : Apparent Γ [.elementaryProposition]) :
    ClosedLine3NormalizationCertificate φ := by
  let matrix := FirstOrderMatrix.abstractRealOuter (line2Formula φ)
  refine ⟨matrix, rfl, rfl, ?_, ?_⟩
  · rfl
  · exact .quantifiedClosedCongr .always
      (.quantifiedClosedCongr .always
        (normalizesFirstOrderMatrixRedexScoped matrix))

def line2DisplayRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofFirstOrderMatrixRedex (line2Formula φ)

def line3DisplayRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  .quantified .always (line2DisplayRaw φ)

theorem line2DisplayRaw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    line2DisplayRaw φ =
      .disj (.neg (ofFirstOrder (line2Antecedent φ)))
        (ofFirstOrder (line2Consequent φ)) := by
  rfl

theorem line3DisplayRaw_unfold
    (φ : Apparent Γ [.elementaryProposition]) :
    line3DisplayRaw φ =
      .quantified .always
        (.disj (.neg (ofFirstOrder (line2Antecedent φ)))
          (ofFirstOrder (line2Consequent φ))) := by
  rw [line3DisplayRaw, line2DisplayRaw_unfold]

def line3ConsequentOutside (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  ofFirstOrder (FirstOrder.weakenReal (FirstOrder.sometimes φ))

theorem ofApparent_inner_weakenReal
    (φ : Apparent Γ [.elementaryProposition]) :
    ofApparent (Apparent.rename Apparent.innerVariableRenaming
      (Apparent.weakenReal (τ := .elementaryProposition) φ)) =
      shiftBoundAt 1 (ofApparent
        (Apparent.weakenReal (τ := .elementaryProposition) φ)) := by
  induction φ with
  | constant name => rfl
  | real v => rfl
  | bound v => cases v <;> rfl
  | neg p ih => exact congrArg Raw.neg ih
  | disj p q ihp ihq =>
      change Raw.disj _ _ = Raw.disj _ _
      have hp := ihp
      have hq := ihq
      simp only [Apparent.weakenReal] at hp hq
      rw [hp, hq]

theorem line2Consequent_is_weakened
    (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrder (line2Consequent φ) =
      weakenBound (line3ConsequentOutside φ) := by
  change Raw.quantified .sometimes
      (ofApparent (Apparent.abstractRealOuter
        (Apparent.weakenReal (Apparent.weakenReal φ)))) = _
  rw [Apparent.abstractRealOuter_weakenReal]
  exact congrArg (Raw.quantified .sometimes)
    (ofApparent_inner_weakenReal φ)

def line4DisplayRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  .disj
    (.neg (.quantified .sometimes (ofFirstOrder (line2Antecedent φ))))
    (line3ConsequentOutside φ)

theorem line3_to_line4
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (line3DisplayRaw φ) (line4DisplayRaw φ) := by
  rw [line3DisplayRaw_unfold, line2Consequent_is_weakened]
  exact .alwaysImpToSometimesAntecedent 0
    (ofFirstOrder (line2Antecedent φ)) (line3ConsequentOutside φ)

theorem line2ScopedRaw_roundTrip (φ : Apparent Γ [.elementaryProposition]) :
    ofFirstOrderMatrixScoped (line2Formula φ) = line2ScopedRaw φ :=
  (line2Reification φ).roundTrip

def line3ScopedRaw (φ : Apparent Γ [.elementaryProposition]) :
    Raw (.elementaryProposition :: Γ) :=
  .quantified .always (line2ScopedRaw φ)

theorem line3Display_to_scoped
    (φ : Apparent Γ [.elementaryProposition]) :
    NormalizesScopedAt 0 (line3DisplayRaw φ) (line3ScopedRaw φ) := by
  exact .quantifiedClosedCongr .always
    (normalizesFirstOrderMatrixRedexScoped (line2Formula φ))

structure Star931MatrixAssertion
    (φ : Apparent Γ [.elementaryProposition]) where
  source : OrderedAssertion (line1Formula φ)
  matrixCertificate :
    ScopedFirstOrderMatrixReification [.elementaryProposition]
      (line2ScopedRaw φ)

inductive Star931ClosedStage
    (φ : Apparent Γ [.elementaryProposition]) : Nat → Prop where
  | line2 (proof : Star931MatrixAssertion φ) : Star931ClosedStage φ 2
  | second_9_13
      (line2Proof : Star931ClosedStage φ 2)
      (carrier : FirstOrderMatrix.Quantified
        (.elementaryProposition :: Γ) [])
      (carrierExact : carrier = line3Carrier φ)
      (targetExact : star_9_13_higher_target carrier = line3Target φ) :
      Star931ClosedStage φ 3
  | star_9_03_02
      (line3Proof : Star931ClosedStage φ 3)
      (certificate : NormalizesScopedAt 0
        (closedLine3DisplayRaw φ) (closedLine4DisplayRaw φ)) :
      Star931ClosedStage φ 4
  | star_9_05_06
      (line4Proof : Star931ClosedStage φ 4)
      (certificate : NormalizesScopedAt 0
        (closedLine4DisplayRaw φ) (closedFinalDisplayRaw φ)) :
      Star931ClosedStage φ 5

structure Star931KernelAssertion
    (φ : Apparent Γ [.elementaryProposition]) where
  chain : Star931ClosedStage φ 5
  endpoint : Raw Γ
  endpointExact : endpoint = exactTargetRaw φ
  normalization : NormalizesScopedAt 0
    (closedLine3DisplayRaw φ) endpoint

def deriveLine2
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931MatrixAssertion φ where
  source := line1Ordered φ
  matrixCertificate := line2Reification φ

def derive
    (φ : Apparent Γ [.elementaryProposition]) :
    Star931KernelAssertion φ where
  chain := .star_9_05_06 (.star_9_03_02
    (.second_9_13 (.line2 (deriveLine2 φ)) (line3Carrier φ) rfl rfl)
    (closedLine3_to_line4 φ)) (closedLine4_to_final φ)
  endpoint := closedFinalDisplayRaw φ
  endpointExact := closedFinalDisplayRaw_eq_exactTargetRaw φ
  normalization := closedLine3_to_final φ

end PM.Architecture.Star931Kernel

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
  Star921MatrixKernel.Star9KernelAssertion (FirstOrderQ259.star_9_3_target φ)

theorem star_9_3 (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_3Derivation φ := by
  simpa [FirstOrderQ259.star_9_3_target,
    Star921MatrixKernel.star_9_3_ordered_target] using
    Star921MatrixKernel.derive_star_9_3 φ

abbrev Star_9_31Derivation (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Nonempty (Star931Kernel.Star931KernelAssertion φ)

theorem star_9_31 (_rules : Q259ClosedRuleBook)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_31Derivation φ :=
  ⟨Star931Kernel.derive φ⟩

abbrev Star_9_32Derivation (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_32_target q φ)

abbrev Star_9_33Derivation (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_33_target q φ)

theorem star_9_32 (rules : Q259ClosedRuleBook) (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_32Derivation q φ := by
  let body := Apparent.ofElementary (∼ₚ q) ∨ₐ (φ ∨ₐ Apparent.ofElementary q)
  have elementaryLine : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary (Apparent.openHead body)) := by
    exact OrderedAssertion.elementary
      (PM.Derivation.star_1_3
        (Apparent.openHead φ)
        (Apparent.openHead (Apparent.ofElementary q)))
  have universalLine : OrderedAssertion
      (.firstOrder (FirstOrder.always body)) :=
    OrderedAssertion.star_9_13 body elementaryLine
  exact OrderedAssertion.star_9_12 universalLine
    (rules.star_9_25 (∼ₚ q) (φ ∨ₐ Apparent.ofElementary q))

theorem star_9_33 (_rules : Q259ClosedRuleBook) (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_33Derivation q φ := by
  let body := matrixImp (Apparent.ofElementary q)
    (φ ∨ₐ Apparent.ofElementary q)
  have elementaryLine : OrderedAssertion
      (.elementary (Apparent.elementaryValue body q)) := by
    simpa [body, matrixImp, Apparent.elementaryValue, Elementary.imp] using
      OrderedAssertion.elementary (PM.Derivation.star_1_3
        (Apparent.elementaryValue φ q) q)
  exact OrderedAssertion.star_9_12_elementary_to_first elementaryLine
    (OrderedAssertion.star_9_1_instance body q)

end PM.Architecture.Q259ClosedRuleBook
