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
