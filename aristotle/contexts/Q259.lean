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
  | neg p ih => exact congrArg Elementary.neg ih
  | disj p q ihp ihq =>
      change Elementary.disj (elementaryValue (ofElementary p) argument)
        (elementaryValue (ofElementary q) argument) = Elementary.disj p q
      rw [ihp, ihq]

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
      change Elementary.neg
        (elementaryValue (renameReal (fun v => .succ v) p) (.var .zero)) =
        Elementary.neg (openHead p)
      exact congrArg Elementary.neg ih
  | disj p q ihp ihq =>
      change Elementary.disj
        (elementaryValue (weakenReal p) (.var .zero))
        (elementaryValue (weakenReal q) (.var .zero)) =
        Elementary.disj (openHead p) (openHead q)
      rw [ihp, ihq]

@[simp] theorem elementaryValue_renameReal_succ_zero
    (φ : Apparent Γ [.elementaryProposition]) :
    elementaryValue (renameReal (fun v => .succ v) φ) (.var .zero) = openHead φ := by
  exact elementaryValue_weakenReal_zero φ

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
      change neg (substitute _ (rename _ (weakenReal proposition))) =
        neg (ofElementary (openHead proposition))
      exact congrArg neg ih
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
      change neg (substitute _ (rename _ (weakenReal proposition))) =
        neg (weakenReal proposition)
      exact congrArg neg ih
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
  | neg proposition ih => exact congrArg neg ih
  | disj left right ihLeft ihRight =>
      change disj (substitute _ (ofElementary left))
        (substitute _ (ofElementary right)) = disj (ofElementary left) (ofElementary right)
      rw [ihLeft, ihRight]

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
  | neg proposition ih =>
      change Option.map Elementary.neg
        (toElementary? (ofElementary proposition)) = some (Elementary.neg proposition)
      rw [ih]
      rfl
  | disj left right ihLeft ihRight =>
      change (do
        let p ← toElementary? (ofElementary left)
        let q ← toElementary? (ofElementary right)
        some (Elementary.disj p q)) = some (Elementary.disj left right)
      rw [ihLeft, ihRight]
      change some (Elementary.disj left right) = some (Elementary.disj left right)
      rfl

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
  | quantified proposition =>
      exact congrArg FirstOrderMatrix.quantified
        (FirstOrder.openRealOuter_abstractRealOuter proposition)
  | neg proposition ih => exact congrArg FirstOrderMatrix.neg ih
  | disj left right ihLeft ihRight =>
      change FirstOrderMatrix.disj (openRealOuter (abstractRealOuter left))
        (openRealOuter (abstractRealOuter right)) = FirstOrderMatrix.disj left right
      rw [ihLeft, ihRight]

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

noncomputable def eraseElementary? {order : Nat} (formula : OrderedFormula Γ order) :
    Option (Elementary Γ) :=
  OrderedFormula.rec
    (motive := fun _ _ => Option (Elementary Γ))
    (fun p => some p)
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ => none) (fun _ => none)
    (fun _ erased => Option.rec none (fun p => some (.neg p)) erased)
    (fun _ _ _ left right =>
      Option.rec none
        (fun p => Option.rec none (fun q => some (.disj p q)) right)
        left)
    formula

macro_rules
  | `(term| match $x:term with
      | .secondOrder _ => none
      | .disj .secondOrder _ _ => none) => `($x)

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
  | star_1_2 p =>
      exact PM.Derivation.star_1_2 (Γ := Ξ) (PM.Elementary.schemaInstance σ p)
  | star_1_3 p q =>
      exact PM.Derivation.star_1_3 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
  | star_1_4 p q =>
      exact PM.Derivation.star_1_4 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
  | star_1_5 p q r =>
      exact PM.Derivation.star_1_5 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r)
  | star_1_6 p q r =>
      exact PM.Derivation.star_1_6 (Γ := Ξ)
        (PM.Elementary.schemaInstance σ p) (PM.Elementary.schemaInstance σ q)
        (PM.Elementary.schemaInstance σ r)

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

end PM

-- PM-CONTEXT-LOCAL Principia/Syntax/Ramified.lean
namespace PM.RamifiedSyntax

theorem natMaxSelf (order : Nat) : max order order = order := by
  unfold Max.max Nat.instMax maxOfLe
  change (if order ≤ order then order else order) = order
  rw [if_pos (Nat.le_refl order)]

theorem natMaxCongr
    {leftOrder rightOrder order : Nat}
    (leftEq : leftOrder = order)
    (rightEq : rightOrder = order) :
    max leftOrder rightOrder = order := by
  cases leftEq
  cases rightEq
  exact natMaxSelf _

universe u

inductive RSort where
  | individual
  | proposition (order : Nat)
  | function (arguments : List RSort) (resultOrder excess : Nat)

namespace RSort

mutual
  def height : RSort → Nat
    | .individual => 0
    | .proposition order => order
    | .function arguments resultOrder excess =>
        max (Nat.succ (maxHeight arguments)) (Nat.succ resultOrder) + excess

  def maxHeight : List RSort → Nat
    | [] => 0
    | argument :: arguments => max argument.height (maxHeight arguments)
end

def Predicative (sort : RSort) : Prop :=
  ∃ arguments resultOrder, sort = .function arguments resultOrder 0

end RSort

abbrev Context := List RSort

inductive Var : Context → RSort → Type where
  | zero : Var (sort :: context) sort
  | succ : Var context sort → Var (other :: context) sort

structure Signature where
  Symbol : RSort → Type u
  Negation : Nat → Type u
  Disjunction : Nat → Type u
  Universal : RSort → Nat → Type u
  Existential : RSort → Nat → Type u

inductive Term (signature : Signature) (real apparent : Context) : RSort → Type u where
  | real : Var real sort → Term signature real apparent sort
  | apparent : Var apparent sort → Term signature real apparent sort
  | symbol : signature.Symbol sort → Term signature real apparent sort

inductive Arguments (signature : Signature) (real apparent : Context) :
    List RSort → Type u where
  | nil : Arguments signature real apparent []
  | cons : Term signature real apparent sort →
      Arguments signature real apparent sorts →
      Arguments signature real apparent (sort :: sorts)

def bindOrder (matrixOrder : Nat) (sort : RSort) : Nat :=
  max matrixOrder (Nat.succ sort.height)

private theorem scopeSuccLeSucc {left right : Nat} :
    left ≤ right → left.succ ≤ right.succ :=
  fun proof => Nat.le.rec
    (motive := fun right _ => left.succ ≤ right.succ)
    Nat.le.refl (fun _ induction => Nat.le.step induction) proof

private theorem scopePredLePred {left right : Nat} (proof : left ≤ right) :
    left.pred ≤ right.pred := by
  induction proof with
  | refl => exact Nat.le.refl
  | @step right proof induction =>
      cases right with
      | zero => exact induction
      | succ right => exact Nat.le.step induction

private theorem scopeLeOfSuccLeSucc {left right : Nat}
    (proof : left.succ ≤ right.succ) : left ≤ right :=
  scopePredLePred proof

private theorem scopeNatMaxSuccSucc (left right : Nat) :
    max left.succ right.succ = (max left right).succ := by
  unfold Max.max Nat.instMax maxOfLe
  change (if left.succ ≤ right.succ then right.succ else left.succ) =
    (if left ≤ right then right else left).succ
  by_cases ordering : left ≤ right
  · rw [if_pos ordering, if_pos (scopeSuccLeSucc ordering)]
  · have successorOrdering : ¬ left.succ ≤ right.succ :=
      fun proof => ordering (scopeLeOfSuccLeSucc proof)
    rw [if_neg ordering, if_neg successorOrdering]

private theorem scopeNatMaxZeroRight : ∀ order : Nat, max order 0 = order
  | 0 => rfl
  | Nat.succ _order => rfl

private theorem scopeNatMaxAssoc : ∀ left middle right : Nat,
    max (max left middle) right = max left (max middle right)
  | 0, middle, right => rfl
  | Nat.succ left, 0, right => rfl
  | Nat.succ left, Nat.succ middle, 0 =>
      Eq.trans (scopeNatMaxZeroRight (max left.succ middle.succ))
        (congrArg (max left.succ)
          (scopeNatMaxZeroRight middle.succ).symm)
  | Nat.succ left, Nat.succ middle, Nat.succ right => by
      rw [scopeNatMaxSuccSucc, scopeNatMaxSuccSucc,
        scopeNatMaxSuccSucc, scopeNatMaxSuccSucc]
      exact congrArg Nat.succ (scopeNatMaxAssoc left middle right)

private theorem scopeNatMaxComm : ∀ left right : Nat,
    max left right = max right left
  | 0, 0 => rfl
  | 0, Nat.succ right => rfl
  | Nat.succ left, 0 => rfl
  | Nat.succ left, Nat.succ right => by
      rw [scopeNatMaxSuccSucc, scopeNatMaxSuccSucc]
      exact congrArg Nat.succ (scopeNatMaxComm left right)

private theorem scopeNatMaxSwapMiddle (left middle right : Nat) :
    max (max left middle) right = max (max left right) middle := by
  exact Eq.trans (scopeNatMaxAssoc left middle right)
    (Eq.trans
      (congrArg (fun order => max left order)
        (scopeNatMaxComm middle right))
      (scopeNatMaxAssoc left right middle).symm)

theorem bindOrderMaxRight
    (matrixOrder fixedOrder : Nat) (argument : RSort) :
    max (bindOrder matrixOrder argument) fixedOrder =
      bindOrder (max matrixOrder fixedOrder) argument := by
  unfold bindOrder
  exact (scopeNatMaxSwapMiddle matrixOrder fixedOrder
    (Nat.succ argument.height)).symm

theorem bindOrderMaxLeft
    (fixedOrder matrixOrder : Nat) (argument : RSort) :
    max fixedOrder (bindOrder matrixOrder argument) =
      bindOrder (max fixedOrder matrixOrder) argument := by
  unfold bindOrder
  exact (scopeNatMaxAssoc fixedOrder matrixOrder
    (Nat.succ argument.height)).symm

structure ExistentialVocabulary (signature : Signature)
    (sort : RSort) (matrixOrder : Nat) where
  printed : signature.Existential sort matrixOrder
  matrixNegation : signature.Negation matrixOrder
  universal : signature.Universal sort matrixOrder
  outerNegation : signature.Negation (bindOrder matrixOrder sort)

inductive IncompleteKind where
  | abstraction
  | description

inductive Formula (signature : Signature) (real : Context) : Context → Nat → Type u where
  | proposition : Term signature real apparent (.proposition order) →
      Formula signature real apparent order
  | apply : Term signature real apparent (.function sorts order excess) →
      Arguments signature real apparent sorts → Formula signature real apparent order
  | neg : signature.Negation order → Formula signature real apparent order →
      Formula signature real apparent order
  | disj : signature.Disjunction (max leftOrder rightOrder) →
      Formula signature real apparent leftOrder →
      Formula signature real apparent rightOrder →
      Formula signature real apparent (max leftOrder rightOrder)
  | always : signature.Universal sort matrixOrder →
      Formula signature real (sort :: apparent) matrixOrder →
      Formula signature real apparent (bindOrder matrixOrder sort)
  | incompleteScope (kind : IncompleteKind)
      (parameters : List RSort) (resultOrder excess scopeOrder : Nat) :
      Formula signature real (parameters ++ apparent) resultOrder →
      Formula signature real
        (.function parameters resultOrder excess :: apparent) scopeOrder →
      Formula signature real apparent scopeOrder
  | descriptionScope (sort : RSort) (conditionOrder scopeOrder : Nat) :
      Formula signature real (sort :: apparent) conditionOrder →
      Formula signature real (sort :: apparent) scopeOrder →
      Formula signature real apparent scopeOrder

def Formula.sometimes
    (existential : ExistentialVocabulary signature sort matrixOrder)
    (body : Formula signature real (sort :: apparent) matrixOrder) :
    Formula signature real apparent (bindOrder matrixOrder sort) :=
  .neg existential.outerNegation
    (.always existential.universal (.neg existential.matrixNegation body))

abbrev Renaming (source target : Context) :=
  {sort : RSort} → Var source sort → Var target sort

def liftRenaming (rho : Renaming source target) :
    Renaming (sort :: source) (sort :: target)
  | _, .zero => .zero
  | _, .succ v => .succ (rho v)

def swapHeadsRenaming :
    Renaming (leftSort :: rightSort :: context)
      (rightSort :: leftSort :: context)
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ v) => .succ (.succ v)

def Term.rename (rho : Renaming source target) :
    Term signature realCtx source sort → Term signature realCtx target sort
  | .real v => .real v
  | .apparent v => .apparent (rho v)
  | .symbol payload => .symbol payload

def Arguments.rename (rho : Renaming source target) :
    Arguments signature realCtx source sorts → Arguments signature realCtx target sorts
  | .nil => .nil
  | .cons term tail => .cons (term.rename rho) (tail.rename rho)

def liftRenamingN : (binders : List RSort) → Renaming source target →
    Renaming (binders ++ source) (binders ++ target)
  | [], rho => rho
  | _ :: rest, rho => liftRenaming (liftRenamingN rest rho)

def emptyRenaming : Renaming [] target
  | _, v => nomatch v

def Formula.rename (rho : Renaming source target) :
    Formula signature realCtx source order → Formula signature realCtx target order
  | .proposition term => .proposition (term.rename rho)
  | .apply function arguments => .apply (function.rename rho) (arguments.rename rho)
  | .neg meaning body => .neg meaning (body.rename rho)
  | .disj meaning left right => .disj meaning (left.rename rho) (right.rename rho)
  | .always meaning body => .always meaning (body.rename (liftRenaming rho))
  | .incompleteScope kind parameters resultOrder excess scopeOrder matrix continuation =>
      .incompleteScope kind parameters resultOrder excess scopeOrder
        (matrix.rename (liftRenamingN parameters rho))
        (continuation.rename (liftRenaming rho))
  | .descriptionScope sort conditionOrder scopeOrder condition continuation =>
      .descriptionScope sort conditionOrder scopeOrder
        (condition.rename (liftRenaming rho))
        (continuation.rename (liftRenaming rho))

def Formula.swapHeads
    (formula : Formula signature realCtx
      (leftSort :: rightSort :: apparent) order) :
    Formula signature realCtx (rightSort :: leftSort :: apparent) order :=
  formula.rename swapHeadsRenaming

abbrev Substitution (signature : Signature) (realCtx source target : Context) :=
  {sort : RSort} → Var source sort → Term signature realCtx target sort

def Term.weaken (term : Term signature realCtx appCtx sort) :
    Term signature realCtx (fresh :: appCtx) sort :=
  term.rename (fun v => .succ v)

def liftSubstitution (sigma : Substitution signature realCtx source target) :
    Substitution signature realCtx (sort :: source) (sort :: target)
  | _, .zero => .apparent .zero
  | _, .succ v => (sigma v).weaken

def liftSubstitutionN : (binders : List RSort) →
    Substitution signature realCtx source target →
    Substitution signature realCtx (binders ++ source) (binders ++ target)
  | [], sigma => sigma
  | _ :: rest, sigma => liftSubstitution (liftSubstitutionN rest sigma)

def Term.substitute (sigma : Substitution signature realCtx source target) :
    Term signature realCtx source sort → Term signature realCtx target sort
  | .real v => .real v
  | .apparent v => sigma v
  | .symbol payload => .symbol payload

def Arguments.substitute (sigma : Substitution signature realCtx source target) :
    Arguments signature realCtx source sorts → Arguments signature realCtx target sorts
  | .nil => .nil
  | .cons term tail => .cons (term.substitute sigma) (tail.substitute sigma)

def Formula.substitute (sigma : Substitution signature realCtx source target) :
    Formula signature realCtx source order → Formula signature realCtx target order
  | .proposition term => .proposition (term.substitute sigma)
  | .apply function arguments =>
      .apply (function.substitute sigma) (arguments.substitute sigma)
  | .neg meaning body => .neg meaning (body.substitute sigma)
  | .disj meaning left right =>
      .disj meaning (left.substitute sigma) (right.substitute sigma)
  | .always meaning body => .always meaning (body.substitute (liftSubstitution sigma))
  | .incompleteScope kind parameters resultOrder excess scopeOrder matrix continuation =>
      .incompleteScope kind parameters resultOrder excess scopeOrder
        (matrix.substitute (liftSubstitutionN parameters sigma))
        (continuation.substitute (liftSubstitution sigma))
  | .descriptionScope sort conditionOrder scopeOrder condition continuation =>
      .descriptionScope sort conditionOrder scopeOrder
        (condition.substitute (liftSubstitution sigma))
        (continuation.substitute (liftSubstitution sigma))

def instantiateSubstitution (argument : Term signature realCtx apparent sort) :
    Substitution signature realCtx (sort :: apparent) apparent
  | _, .zero => argument
  | _, .succ v => .apparent v

def Formula.instantiate
    (body : Formula signature realCtx (sort :: apparent) order)
    (argument : Term signature realCtx apparent sort) :
    Formula signature realCtx apparent order :=
  body.substitute (instantiateSubstitution argument)

def Formula.always₂
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort (bindOrder matrixOrder leftSort))
    (body : Formula signature realCtx
      (leftSort :: rightSort :: apparent) matrixOrder) :
    Formula signature realCtx apparent
      (bindOrder (bindOrder matrixOrder leftSort) rightSort) :=
  .always outer (.always inner body)

def Formula.instantiate₂
    (body : Formula signature realCtx
      (leftSort :: rightSort :: apparent) order)
    (left : Term signature realCtx apparent leftSort)
    (right : Term signature realCtx apparent rightSort) :
    Formula signature realCtx apparent order :=
  (body.instantiate left.weaken).instantiate right

@[simp] theorem substitute_apparent
    (sigma : Substitution signature realCtx source target) (v : Var source sort) :
    (Term.apparent v : Term signature realCtx source sort).substitute sigma = sigma v := rfl

@[simp] theorem liftSubstitution_zero
    (sigma : Substitution signature realCtx source target) :
    liftSubstitution (sort := sort) sigma (Var.zero : Var (sort :: source) sort) =
      (.apparent .zero : Term signature realCtx (sort :: target) sort) := rfl

@[simp] theorem liftSubstitution_succ
    (sigma : Substitution signature realCtx source target) (v : Var source sort) :
    liftSubstitution (sort := binder) sigma (.succ v) = (sigma v).weaken := rfl

@[simp] theorem instantiate_zero
    (body : Formula signature realCtx (sort :: apparent) order)
    (argument : Term signature realCtx apparent sort) :
    body.instantiate argument = body.substitute (instantiateSubstitution argument) := rfl

theorem substitute_always
    (sigma : Substitution signature realCtx source target)
    (meaning : signature.Universal sort matrixOrder)
    (body : Formula signature realCtx (sort :: source) matrixOrder) :
    (Formula.always meaning body).substitute sigma =
      .always meaning (body.substitute (liftSubstitution sigma)) := rfl

theorem substitute_preserves_term_sort
    (sigma : Substitution signature realCtx source target)
    (term : Term signature realCtx source sort) :
    ∃ output : Term signature realCtx target sort,
      output = term.substitute sigma := ⟨term.substitute sigma, rfl⟩

theorem substitute_preserves_formula_order
    (sigma : Substitution signature realCtx source target)
    (formula : Formula signature realCtx source order) :
    ∃ output : Formula signature realCtx target order,
      output = formula.substitute sigma := ⟨formula.substitute sigma, rfl⟩

def substitutionAfterRenaming
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target) :
    Substitution signature realCtx source target :=
  fun v => sigma (rho v)

@[simp] theorem lift_substitutionAfterRenaming_apply
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (v : Var (binder :: source) sort) :
    liftSubstitution (sort := binder) (substitutionAfterRenaming rho sigma) v =
      substitutionAfterRenaming (liftRenaming (sort := binder) rho)
        (liftSubstitution sigma) v := by
  cases v with
  | zero => rfl
  | succ v => rfl

@[simp] theorem liftN_substitutionAfterRenaming_apply
    (binders : List RSort) (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (v : Var (binders ++ source) sort) :
    liftSubstitutionN binders (substitutionAfterRenaming rho sigma) v =
      substitutionAfterRenaming (liftRenamingN binders rho)
        (liftSubstitutionN binders sigma) v := by
  induction binders with
  | nil => rfl
  | cons binder binders ih =>
      cases v with
      | zero => rfl
      | succ v =>
          change Term.weaken
            (liftSubstitutionN binders (substitutionAfterRenaming rho sigma) v) =
            Term.weaken
              (substitutionAfterRenaming (liftRenamingN binders rho)
                (liftSubstitutionN binders sigma) v)
          exact congrArg Term.weaken (ih v)

@[simp] theorem Term.rename_substitute
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (term : Term signature realCtx source sort) :
    (term.rename rho).substitute sigma =
      term.substitute (substitutionAfterRenaming rho sigma) := by
  cases term <;> rfl

@[simp] theorem Arguments.rename_substitute
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (arguments : Arguments signature realCtx source sorts) :
    (arguments.rename rho).substitute sigma =
      arguments.substitute (substitutionAfterRenaming rho sigma) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      change Arguments.cons ((term.rename rho).substitute sigma)
        ((tail.rename rho).substitute sigma) =
        Arguments.cons (term.substitute (substitutionAfterRenaming rho sigma))
          (tail.substitute (substitutionAfterRenaming rho sigma))
      rw [Term.rename_substitute, ih]

theorem Term.rename_substitute_of_pointwise
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (tau : Substitution signature realCtx source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma (rho v) = tau v)
    (term : Term signature realCtx source sort) :
    (term.rename rho).substitute sigma = term.substitute tau := by
  cases term with
  | real v => rfl
  | apparent v => exact pointwise v
  | symbol payload => rfl

theorem Arguments.rename_substitute_of_pointwise
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (tau : Substitution signature realCtx source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma (rho v) = tau v)
    (arguments : Arguments signature realCtx source sorts) :
    (arguments.rename rho).substitute sigma = arguments.substitute tau := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.rename_substitute_of_pointwise rho sigma tau pointwise term,
        ih]

theorem liftSubstitution_pointwise
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (tau : Substitution signature realCtx source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma (rho v) = tau v) :
    ∀ {sort} (v : Var (binder :: source) sort),
      liftSubstitution sigma (liftRenaming rho v) = liftSubstitution tau v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Term.weaken (pointwise v)

theorem liftSubstitutionN_pointwise
    (binders : List RSort)
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (tau : Substitution signature realCtx source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma (rho v) = tau v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftSubstitutionN binders sigma (liftRenamingN binders rho v) =
        liftSubstitutionN binders tau v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih =>
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact congrArg Term.weaken (ih v)

theorem Formula.rename_substitute_of_pointwise
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (tau : Substitution signature realCtx source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma (rho v) = tau v)
    (formula : Formula signature realCtx source order) :
    (formula.rename rho).substitute sigma = formula.substitute tau := by
  induction formula generalizing middle target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.rename_substitute_of_pointwise rho sigma tau pointwise term]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.rename_substitute_of_pointwise rho sigma tau pointwise function,
        Arguments.rename_substitute_of_pointwise rho sigma tau pointwise arguments]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih rho sigma tau pointwise]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH rho sigma tau pointwise, rightIH rho sigma tau pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      rw [ih (liftRenaming rho) (liftSubstitution sigma) (liftSubstitution tau)
        (liftSubstitution_pointwise rho sigma tau pointwise)]
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftRenamingN parameters rho) (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau)
          (liftSubstitutionN_pointwise parameters rho sigma tau pointwise),
        continuationIH (liftRenaming rho) (liftSubstitution sigma) (liftSubstitution tau)]
      exact liftSubstitution_pointwise rho sigma tau pointwise
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ = Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftRenaming rho) (liftSubstitution sigma) (liftSubstitution tau)
          (liftSubstitution_pointwise rho sigma tau pointwise),
        continuationIH (liftRenaming rho) (liftSubstitution sigma) (liftSubstitution tau)
          (liftSubstitution_pointwise rho sigma tau pointwise)]

@[simp] theorem Formula.rename_substitute
    (rho : Renaming source middle)
    (sigma : Substitution signature realCtx middle target)
    (formula : Formula signature realCtx source order) :
    (formula.rename rho).substitute sigma =
      formula.substitute (substitutionAfterRenaming rho sigma) :=
  Formula.rename_substitute_of_pointwise rho sigma
    (substitutionAfterRenaming rho sigma) (fun _ => rfl) formula

theorem swapHeads_preserves_term_sort
    (term : Term signature realCtx
      (leftSort :: rightSort :: apparent) sort) :
    ∃ output : Term signature realCtx
        (rightSort :: leftSort :: apparent) sort,
      output = term.rename swapHeadsRenaming :=
  ⟨term.rename swapHeadsRenaming, rfl⟩

theorem swapHeads_preserves_formula_order
    (formula : Formula signature realCtx
      (leftSort :: rightSort :: apparent) order) :
    ∃ output : Formula signature realCtx
        (rightSort :: leftSort :: apparent) order,
      output = formula.swapHeads :=
  ⟨formula.swapHeads, rfl⟩

theorem Formula.swapHeads_substitute
    (formula : Formula signature realCtx
      (leftSort :: rightSort :: apparent) order)
    (sigma : Substitution signature realCtx
      (rightSort :: leftSort :: apparent) target) :
    formula.swapHeads.substitute sigma =
      formula.substitute
        (substitutionAfterRenaming swapHeadsRenaming sigma) := by
  exact Formula.rename_substitute swapHeadsRenaming sigma formula

def classSort (resultOrder excess : Nat) : RSort :=
  .function [.individual] resultOrder excess

def relationSort (resultOrder excess : Nat) : RSort :=
  .function [.individual, .individual] resultOrder excess

def applyUnary
    (function : Term signature realCtx apparent (.function [argument] order excess))
    (term : Term signature realCtx apparent argument) :
    Formula signature realCtx apparent order :=
  .apply function (.cons term .nil)

def applyBinary
    (function : Term signature realCtx apparent
      (.function [leftSort, rightSort] order excess))
    (left : Term signature realCtx apparent leftSort)
    (right : Term signature realCtx apparent rightSort) :
    Formula signature realCtx apparent order :=
  .apply function (.cons left (.cons right .nil))

def star_9_01
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent (bindOrder matrixOrder argument) :=
  .sometimes existential (.neg negation body)

def star_9_02
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent (bindOrder matrixOrder argument) :=
  .always universal (.neg negation body)

def star_9_03
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    Formula signature real apparent
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  .always universal
    (.disj disjunction body (fixed.rename (fun v => .succ v)))

def star_9_04
    (universal : signature.Universal argument (max fixedOrder matrixOrder))
    (disjunction : signature.Disjunction (max fixedOrder matrixOrder))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .always universal
    (.disj disjunction (fixed.rename (fun v => .succ v)) body)

def star_9_05
    (existential : ExistentialVocabulary signature argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    Formula signature real apparent
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  .sometimes existential
    (.disj disjunction body (fixed.rename (fun v => .succ v)))

def star_9_06
    (existential : ExistentialVocabulary signature argument (max fixedOrder matrixOrder))
    (disjunction : signature.Disjunction (max fixedOrder matrixOrder))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .sometimes existential
    (.disj disjunction (fixed.rename (fun v => .succ v)) body)

def star_9_07
    (existential : ExistentialVocabulary signature rightSort matrixOrder)
    (universal : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real
      (rightSort :: leftSort :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder (bindOrder matrixOrder rightSort) leftSort) :=
  .always universal (.sometimes existential
    (Eq.mp (congrArg (Formula signature real
      (rightSort :: leftSort :: apparent)) (natMaxSelf matrixOrder))
      (.disj
        (Eq.mp (congrArg signature.Disjunction
          (natMaxSelf matrixOrder).symm) disjunction)
        phi psi)))

def star_9_08
    (existential : ExistentialVocabulary signature rightSort matrixOrder)
    (universal : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (disjunction : signature.Disjunction matrixOrder)
    (psi phi : Formula signature real
      (rightSort :: leftSort :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder (bindOrder matrixOrder rightSort) leftSort) :=
  .always universal (.sometimes existential
    (Eq.mp (congrArg (Formula signature real
      (rightSort :: leftSort :: apparent)) (natMaxSelf matrixOrder))
      (.disj
        (Eq.mp (congrArg signature.Disjunction
          (natMaxSelf matrixOrder).symm) disjunction)
        psi phi)))

theorem star_9_01_unfold
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    star_9_01 existential negation body =
      .sometimes existential (.neg negation body) := rfl

theorem star_9_02_unfold
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    star_9_02 universal negation body =
      .always universal (.neg negation body) := rfl

theorem star_9_03_unfold
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    star_9_03 universal disjunction body fixed =
      .always universal
        (.disj disjunction body (fixed.rename (fun v => .succ v))) := rfl

theorem star_9_03_fold
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    (.always universal
        (.disj disjunction body (fixed.rename (fun v => .succ v)))) =
      star_9_03 universal disjunction body fixed := rfl

theorem star_9_04_unfold
    (universal : signature.Universal argument (max fixedOrder matrixOrder))
    (disjunction : signature.Disjunction (max fixedOrder matrixOrder))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    star_9_04 universal disjunction fixed body =
      .always universal
        (.disj disjunction (fixed.rename (fun v => .succ v)) body) := rfl

theorem star_9_04_fold
    (universal : signature.Universal argument (max fixedOrder matrixOrder))
    (disjunction : signature.Disjunction (max fixedOrder matrixOrder))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    (.always universal
        (.disj disjunction (fixed.rename (fun v => .succ v)) body)) =
      star_9_04 universal disjunction fixed body := rfl

theorem star_9_05_unfold
    (existential : ExistentialVocabulary signature argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    star_9_05 existential disjunction body fixed =
      .sometimes existential
        (.disj disjunction body (fixed.rename (fun v => .succ v))) := rfl

theorem star_9_06_unfold
    (existential : ExistentialVocabulary signature argument (max fixedOrder matrixOrder))
    (disjunction : signature.Disjunction (max fixedOrder matrixOrder))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    star_9_06 existential disjunction fixed body =
      .sometimes existential
        (.disj disjunction (fixed.rename (fun v => .succ v)) body) := rfl

private def Formula.scopeCast
    (formula : Formula signature real apparent sourceOrder) :
    {targetOrder : Nat} → sourceOrder = targetOrder →
      Formula signature real apparent targetOrder
  | _, rfl => formula

private inductive Formula.ScopeRoot where
  | proposition
  | apply
  | neg
  | disj
  | always
  | incompleteScope
  | descriptionScope

private def Formula.scopeRoot :
    Formula signature real apparent order → Formula.ScopeRoot
  | .proposition _ => .proposition
  | .apply _ _ => .apply
  | .neg _ _ => .neg
  | .disj _ _ _ => .disj
  | .always _ _ => .always
  | .incompleteScope _ _ _ _ _ _ _ => .incompleteScope
  | .descriptionScope _ _ _ _ _ => .descriptionScope

private theorem Formula.scopeRoot_scopeCast
    (formula : Formula signature real apparent sourceOrder)
    (equality : sourceOrder = targetOrder) :
    (formula.scopeCast equality).scopeRoot = formula.scopeRoot := by
  cases equality
  rfl

private def Formula.scopeTreeSize :
    Formula signature real apparent order → Nat
  | .proposition _ => 1
  | .apply _ _ => 1
  | .neg _ body => Nat.succ body.scopeTreeSize
  | .disj _ left right => Nat.succ
      (left.scopeTreeSize + right.scopeTreeSize)
  | .always _ body => Nat.succ body.scopeTreeSize
  | .incompleteScope _ _ _ _ _ matrix continuation => Nat.succ
      (matrix.scopeTreeSize + continuation.scopeTreeSize)
  | .descriptionScope _ _ _ condition continuation => Nat.succ
      (condition.scopeTreeSize + continuation.scopeTreeSize)

private theorem scopeNatNeSuccSucc (number : Nat) :
    number ≠ number.succ.succ :=
  Nat.rec (motive := fun current => current ≠ current.succ.succ)
    (fun equality => Nat.noConfusion equality)
    (fun _ induction equality => induction (Nat.succ.inj equality)) number

private theorem Formula.scopeNeTwoNegations
    (outerNegation innerNegation : signature.Negation order)
    (body : Formula signature real apparent order) :
    body ≠ .neg outerNegation (.neg innerNegation body) := by
  intro equality
  have sizeEquality := congrArg Formula.scopeTreeSize equality
  exact scopeNatNeSuccSucc body.scopeTreeSize sizeEquality

theorem star_9_01_scope_impossible
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula.neg existential.outerNegation
        (.always existential.universal body) ≠
      star_9_01 existential existential.matrixNegation body := by
  unfold star_9_01 Formula.sometimes
  intro equality
  have alwaysEquality := (Formula.neg.inj equality).2
  have bodyEquality := (Formula.always.inj alwaysEquality).2
  exact Formula.scopeNeTwoNegations existential.matrixNegation
    existential.matrixNegation body bodyEquality

theorem star_9_02_scope_impossible
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula.neg existential.outerNegation
        (.sometimes existential body) ≠
      star_9_02 existential.universal existential.matrixNegation body := by
  intro equality
  have rootEquality := congrArg Formula.scopeRoot equality
  unfold star_9_02 at rootEquality
  cases rootEquality

theorem star_9_03_scope_impossible
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (max matrixOrder fixedOrder))
    (scopeDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    star_9_03 scopeUniversal scopeDisjunction body fixed ≠
      Formula.scopeCast
        (.disj outerDisjunction (.always matrixUniversal body) fixed)
        (bindOrderMaxRight matrixOrder fixedOrder argument) := by
  intro equality
  have rootEquality := congrArg Formula.scopeRoot equality
  rw [Formula.scopeRoot_scopeCast] at rootEquality
  unfold star_9_03 at rootEquality
  cases rootEquality

theorem star_9_04_scope_impossible
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (scopeDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    star_9_04 scopeUniversal scopeDisjunction fixed body ≠
      Formula.scopeCast
        (.disj outerDisjunction fixed (.always matrixUniversal body))
        (bindOrderMaxLeft fixedOrder matrixOrder argument) := by
  intro equality
  have rootEquality := congrArg Formula.scopeRoot equality
  rw [Formula.scopeRoot_scopeCast] at rootEquality
  unfold star_9_04 at rootEquality
  cases rootEquality

theorem star_9_05_scope_impossible
    (matrixExistential : ExistentialVocabulary signature argument matrixOrder)
    (scopeExistential : ExistentialVocabulary signature argument
      (max matrixOrder fixedOrder))
    (scopeDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    star_9_05 scopeExistential scopeDisjunction body fixed ≠
      Formula.scopeCast
        (.disj outerDisjunction (.sometimes matrixExistential body) fixed)
        (bindOrderMaxRight matrixOrder fixedOrder argument) := by
  intro equality
  have rootEquality := congrArg Formula.scopeRoot equality
  rw [Formula.scopeRoot_scopeCast] at rootEquality
  unfold star_9_05 Formula.sometimes at rootEquality
  cases rootEquality

theorem star_9_06_scope_impossible
    (matrixExistential : ExistentialVocabulary signature argument matrixOrder)
    (scopeExistential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (scopeDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    star_9_06 scopeExistential scopeDisjunction fixed body ≠
      Formula.scopeCast
        (.disj outerDisjunction fixed (.sometimes matrixExistential body))
        (bindOrderMaxLeft fixedOrder matrixOrder argument) := by
  intro equality
  have rootEquality := congrArg Formula.scopeRoot equality
  rw [Formula.scopeRoot_scopeCast] at rootEquality
  unfold star_9_06 Formula.sometimes at rootEquality
  cases rootEquality

theorem star_9_07_unfold
    (existential : ExistentialVocabulary signature rightSort matrixOrder)
    (universal : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real
      (rightSort :: leftSort :: apparent) matrixOrder) :
    star_9_07 existential universal disjunction phi psi =
      .always universal (.sometimes existential
        (Eq.mp (congrArg (Formula signature real
          (rightSort :: leftSort :: apparent)) (natMaxSelf matrixOrder))
          (.disj
            (Eq.mp (congrArg signature.Disjunction
              (natMaxSelf matrixOrder).symm) disjunction)
            phi psi))) := rfl

theorem star_9_08_unfold
    (existential : ExistentialVocabulary signature rightSort matrixOrder)
    (universal : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (disjunction : signature.Disjunction matrixOrder)
    (psi phi : Formula signature real
      (rightSort :: leftSort :: apparent) matrixOrder) :
    star_9_08 existential universal disjunction psi phi =
      .always universal (.sometimes existential
        (Eq.mp (congrArg (Formula signature real
          (rightSort :: leftSort :: apparent)) (natMaxSelf matrixOrder))
          (.disj
            (Eq.mp (congrArg signature.Disjunction
              (natMaxSelf matrixOrder).symm) disjunction)
            psi phi))) := rfl

def star_10_01
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent (bindOrder matrixOrder argument) :=
  Formula.sometimes existential body

theorem star_10_01_unfold
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    star_10_01 existential body =
      .neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation body)) := rfl

def membership
    (term : Term signature realCtx apparent .individual)
    (classTerm : Term signature realCtx apparent (classSort order excess)) :
    Formula signature realCtx apparent order :=
  applyUnary classTerm term

structure IdentityVocabulary (signature : Signature) (sort : RSort)
    (order excess : Nat) where
  negation : signature.Negation order
  disjunction : signature.Disjunction order
  universal : signature.Universal (.function [sort] order excess) order

def mixedImplication (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature realCtx apparent leftOrder)
    (right : Formula signature realCtx apparent rightOrder) :
    Formula signature realCtx apparent (max leftOrder rightOrder) :=
  .disj disjunction (.neg negation left) right

theorem mixedImplication_unfold
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature realCtx apparent leftOrder)
    (right : Formula signature realCtx apparent rightOrder) :
    mixedImplication negation disjunction left right =
      .disj disjunction (.neg negation left) right := rfl

def star_11_1_formula
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort (bindOrder matrixOrder leftSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort) matrixOrder))
    (body : Formula signature realCtx
      (leftSort :: rightSort :: apparent) matrixOrder)
    (left : Term signature realCtx apparent leftSort)
    (right : Term signature realCtx apparent rightSort) :
    Formula signature realCtx apparent
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort) matrixOrder) :=
  mixedImplication negation disjunction (body.always₂ inner outer)
    (body.instantiate₂ left right)

def star_11_07_formula
    (leftInner : signature.Universal leftSort matrixOrder)
    (rightOuter : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (rightInner : signature.Universal rightSort matrixOrder)
    (leftOuter : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort)
        (bindOrder (bindOrder matrixOrder rightSort) leftSort)))
    (body : Formula signature realCtx
      (leftSort :: rightSort :: apparent) matrixOrder) :
    Formula signature realCtx apparent
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort)
        (bindOrder (bindOrder matrixOrder rightSort) leftSort)) :=
  mixedImplication negation disjunction
    (body.always₂ leftInner rightOuter)
    (body.swapHeads.always₂ rightInner leftOuter)

def implication (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    Formula signature realCtx apparent order :=
  Eq.mp (congrArg (Formula signature realCtx apparent) (natMaxSelf order))
    (mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
        disjunction)
      left right)

def sameDisjunction (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    Formula signature realCtx apparent order :=
  Eq.mp (congrArg (Formula signature realCtx apparent) (natMaxSelf order))
    (.disj
      (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
        disjunction)
      left right)

theorem sameDisjunction_unfold
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    sameDisjunction disjunction left right =
      Eq.mp (congrArg (Formula signature realCtx apparent) (natMaxSelf order))
        (.disj
          (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
            disjunction)
          left right) := rfl

def mixedConjunction
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature realCtx apparent leftOrder)
    (right : Formula signature realCtx apparent rightOrder) :
    Formula signature realCtx apparent (max leftOrder rightOrder) :=
  .neg outerNegation
    (.disj disjunction (.neg leftNegation left) (.neg rightNegation right))

theorem mixedConjunction_unfold
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (left : Formula signature realCtx apparent leftOrder)
    (right : Formula signature realCtx apparent rightOrder) :
    mixedConjunction leftNegation rightNegation outerNegation disjunction
        left right =
      .neg outerNegation
        (.disj disjunction (.neg leftNegation left) (.neg rightNegation right)) :=
  rfl

def conjunction (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    Formula signature realCtx apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation left) (.neg negation right))

theorem conjunction_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    conjunction negation disjunction left right =
      .neg negation
        (sameDisjunction disjunction
          (.neg negation left) (.neg negation right)) := rfl

def equivalence (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    Formula signature realCtx apparent order :=
  conjunction negation disjunction
    (implication negation disjunction left right)
    (implication negation disjunction right left)

theorem equivalence_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    equivalence negation disjunction left right =
      conjunction negation disjunction
        (implication negation disjunction left right)
        (implication negation disjunction right left) := rfl

example
    (universal : signature.Universal sort matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder sort))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder sort) matrixOrder))
    (phiX : Formula signature realCtx (sort :: apparent) matrixOrder)
    (phiY : Formula signature realCtx apparent matrixOrder) :
    Formula signature realCtx apparent
      (max (bindOrder matrixOrder sort) matrixOrder) :=
  mixedImplication negation disjunction (.always universal phiX) phiY

example
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort (bindOrder matrixOrder leftSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort) matrixOrder))
    (body : Formula signature realCtx
      (leftSort :: rightSort :: apparent) matrixOrder)
    (z : Term signature realCtx apparent leftSort)
    (w : Term signature realCtx apparent rightSort) :
    Formula signature realCtx apparent
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort) matrixOrder) :=
  star_11_1_formula inner outer negation disjunction body z w

example
    (leftInner : signature.Universal leftSort matrixOrder)
    (rightOuter : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (rightInner : signature.Universal rightSort matrixOrder)
    (leftOuter : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort)
        (bindOrder (bindOrder matrixOrder rightSort) leftSort)))
    (body : Formula signature realCtx
      (leftSort :: rightSort :: apparent) matrixOrder) :
    Formula signature realCtx apparent
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort)
        (bindOrder (bindOrder matrixOrder rightSort) leftSort)) :=
  star_11_07_formula leftInner rightOuter rightInner leftOuter
    negation disjunction body

def star_13_01
    (vocabulary : IdentityVocabulary signature sort order excess)
    (left right : Term signature realCtx apparent sort) :
    Formula signature realCtx apparent
      (bindOrder order (.function [sort] order excess)) :=
  let predicate : Term signature realCtx
      (.function [sort] order excess :: apparent)
      (.function [sort] order excess) := .apparent .zero
  .always vocabulary.universal
    (implication vocabulary.negation vocabulary.disjunction
      (applyUnary predicate left.weaken)
      (applyUnary predicate right.weaken))

def star_20_01
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (matrix : Formula signature realCtx (.individual :: apparent) resultOrder)
    (continuation : Formula signature realCtx
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature realCtx apparent
      (bindOrder (max (bindOrder resultOrder .individual) scopeOrder)
        (classSort resultOrder 0)) :=
  let predicateSort := classSort resultOrder 0
  let predicate : Term signature realCtx
      (.individual :: predicateSort :: apparent) predicateSort :=
    .apparent (.succ .zero)
  let x : Term signature realCtx
      (.individual :: predicateSort :: apparent) .individual := .apparent .zero
  let matrixUnderPredicate : Formula signature realCtx
      (.individual :: predicateSort :: apparent) resultOrder :=
    matrix.rename (liftRenaming (fun v => .succ v))
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction
          (applyUnary predicate x) matrixUnderPredicate))
      continuation)

theorem star_20_01_unfold
    (existential : ExistentialVocabulary signature (classSort resultOrder 0)
      (max (bindOrder resultOrder .individual) scopeOrder))
    (universal : signature.Universal .individual resultOrder)
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation (bindOrder resultOrder .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder resultOrder .individual) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder resultOrder .individual) scopeOrder))
    (matrix : Formula signature realCtx (.individual :: apparent) resultOrder)
    (continuation : Formula signature realCtx
      (classSort resultOrder 0 :: apparent) scopeOrder) :
    star_20_01 existential universal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          (.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (matrix.rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

def star_20_02
    (predicate : Term signature realCtx apparent (classSort resultOrder 0))
    (x : Term signature realCtx apparent .individual) :
    Formula signature realCtx apparent resultOrder :=
  applyUnary predicate x

theorem star_20_02_unfold
    (predicate : Term signature realCtx apparent (classSort resultOrder 0))
    (x : Term signature realCtx apparent .individual) :
    star_20_02 predicate x = applyUnary predicate x := rfl

def star_21_01
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (matrix : Formula signature realCtx
      (.individual :: .individual :: apparent) resultOrder)
    (continuation : Formula signature realCtx
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature realCtx apparent
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)) :=
  let relation : Term signature realCtx
      (.individual :: .individual :: relationSort resultOrder 0 :: apparent)
      (relationSort resultOrder 0) := .apparent (.succ (.succ .zero))
  let left : Term signature realCtx
      (.individual :: .individual :: relationSort resultOrder 0 :: apparent)
      .individual := .apparent .zero
  let right : Term signature realCtx
      (.individual :: .individual :: relationSort resultOrder 0 :: apparent)
      .individual := .apparent (.succ .zero)
  let matrixUnderRelation : Formula signature realCtx
      (.individual :: .individual :: relationSort resultOrder 0 :: apparent)
      resultOrder := matrix.rename (liftRenamingN [.individual, .individual]
        (fun v => .succ v))
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      ((equivalence equivalenceNegation equivalenceDisjunction
        (applyBinary relation left right) matrixUnderRelation).always₂
          leftUniversal rightUniversal)
      continuation)

theorem star_21_01_unfold
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (matrix : Formula signature realCtx
      (.individual :: .individual :: apparent) resultOrder)
    (continuation : Formula signature realCtx
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    star_21_01 existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          ((equivalence equivalenceNegation equivalenceDisjunction
            (applyBinary (.apparent (.succ (.succ .zero))) (.apparent .zero)
              (.apparent (.succ .zero)))
            (matrix.rename (liftRenamingN [.individual, .individual]
              (fun v => .succ v)))).always₂ leftUniversal rightUniversal)
          continuation) := rfl

def star_14_01
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder))
    (universal : signature.Universal sort (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)))
    (identityVocabulary : IdentityVocabulary signature sort identityBaseOrder
      identityExcess)
    (equivalenceNegation : signature.Negation (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)))
    (equivalenceDisjunction : signature.Disjunction (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)))
    (leftNegation : signature.Negation (bindOrder (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)) sort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder))
    (condition : Formula signature realCtx (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature realCtx (sort :: apparent) scopeOrder) :
    Formula signature realCtx apparent
      (bindOrder (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder) sort) :=
  let x : Term signature realCtx (sort :: sort :: apparent) sort := .apparent .zero
  let b : Term signature realCtx (sort :: sort :: apparent) sort :=
    .apparent (.succ .zero)
  let conditionUnderB : Formula signature realCtx
      (sort :: sort :: apparent) (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) :=
    condition.rename (liftRenaming (fun v => .succ v))
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction
      (.always universal
        (equivalence equivalenceNegation equivalenceDisjunction conditionUnderB
          (star_13_01 (order := identityBaseOrder)
            (excess := identityExcess) identityVocabulary x b)))
      continuation)

theorem star_14_01_unfold
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder))
    (universal : signature.Universal sort (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)))
    (identityVocabulary : IdentityVocabulary signature sort identityBaseOrder
      identityExcess)
    (equivalenceNegation : signature.Negation (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)))
    (equivalenceDisjunction : signature.Disjunction (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)))
    (leftNegation : signature.Negation (bindOrder (bindOrder identityBaseOrder
      (.function [sort] identityBaseOrder identityExcess)) sort))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)) sort) scopeOrder))
    (condition : Formula signature realCtx (sort :: apparent)
      (bindOrder identityBaseOrder
        (.function [sort] identityBaseOrder identityExcess)))
    (continuation : Formula signature realCtx (sort :: apparent) scopeOrder) :
    star_14_01 existential universal identityVocabulary equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction condition continuation =
      .sometimes existential
        (mixedConjunction leftNegation rightNegation outerNegation
          conjunctionDisjunction
          (.always universal
            (equivalence equivalenceNegation equivalenceDisjunction
              (condition.rename (liftRenaming (fun v => .succ v)))
              (star_13_01 (order := identityBaseOrder)
                (excess := identityExcess) identityVocabulary (.apparent .zero)
                (.apparent (.succ .zero)))))
          continuation) := rfl

def star_14_02
    (existential : ExistentialVocabulary signature sort uniquenessOrder)
    (uniquenessMatrix :
      Formula signature realCtx (sort :: apparent) uniquenessOrder) :
    Formula signature realCtx apparent (bindOrder uniquenessOrder sort) :=
  .sometimes existential uniquenessMatrix

def star_14_descriptionIdentity
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort) (bindOrder continuationIdentityBaseOrder
          (.function [sort] continuationIdentityBaseOrder
            continuationIdentityExcess))))
    (universal : signature.Universal sort
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (conditionIdentity : IdentityVocabulary signature sort
      conditionIdentityBaseOrder conditionIdentityExcess)
    (conditionEquivalenceNegation : signature.Negation
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (conditionEquivalenceDisjunction : signature.Disjunction
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (uniquenessNegation : signature.Negation
      (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort))
    (continuationIdentity : IdentityVocabulary signature sort
      continuationIdentityBaseOrder continuationIdentityExcess)
    (continuationIdentityNegation : signature.Negation
      (bindOrder continuationIdentityBaseOrder
        (.function [sort] continuationIdentityBaseOrder
          continuationIdentityExcess)))
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort) (bindOrder continuationIdentityBaseOrder
          (.function [sort] continuationIdentityBaseOrder
            continuationIdentityExcess))))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort) (bindOrder continuationIdentityBaseOrder
          (.function [sort] continuationIdentityBaseOrder
            continuationIdentityExcess))))
    (condition : Formula signature realCtx (sort :: apparent)
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (term : Term signature realCtx apparent sort) :
    Formula signature realCtx apparent
      (bindOrder
        (max (bindOrder (bindOrder conditionIdentityBaseOrder
          (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
          sort) (bindOrder continuationIdentityBaseOrder
            (.function [sort] continuationIdentityBaseOrder
              continuationIdentityExcess))) sort) :=
  star_14_01 existential universal conditionIdentity
    conditionEquivalenceNegation conditionEquivalenceDisjunction
    uniquenessNegation continuationIdentityNegation outerNegation
    conjunctionDisjunction condition
    (star_13_01 continuationIdentity (.apparent .zero) term.weaken)

theorem star_14_descriptionIdentity_unfold
    (existential : ExistentialVocabulary signature sort
      (max (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort) (bindOrder continuationIdentityBaseOrder
          (.function [sort] continuationIdentityBaseOrder
            continuationIdentityExcess))))
    (universal : signature.Universal sort
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (conditionIdentity : IdentityVocabulary signature sort
      conditionIdentityBaseOrder conditionIdentityExcess)
    (conditionEquivalenceNegation : signature.Negation
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (conditionEquivalenceDisjunction : signature.Disjunction
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (uniquenessNegation : signature.Negation
      (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort))
    (continuationIdentity : IdentityVocabulary signature sort
      continuationIdentityBaseOrder continuationIdentityExcess)
    (continuationIdentityNegation : signature.Negation
      (bindOrder continuationIdentityBaseOrder
        (.function [sort] continuationIdentityBaseOrder
          continuationIdentityExcess)))
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort) (bindOrder continuationIdentityBaseOrder
          (.function [sort] continuationIdentityBaseOrder
            continuationIdentityExcess))))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess))
        sort) (bindOrder continuationIdentityBaseOrder
          (.function [sort] continuationIdentityBaseOrder
            continuationIdentityExcess))))
    (condition : Formula signature realCtx (sort :: apparent)
      (bindOrder conditionIdentityBaseOrder
        (.function [sort] conditionIdentityBaseOrder conditionIdentityExcess)))
    (term : Term signature realCtx apparent sort) :
    star_14_descriptionIdentity existential universal conditionIdentity
        conditionEquivalenceNegation conditionEquivalenceDisjunction
        uniquenessNegation continuationIdentity continuationIdentityNegation
        outerNegation
        conjunctionDisjunction condition term =
      star_14_01 existential universal conditionIdentity
        conditionEquivalenceNegation conditionEquivalenceDisjunction
        uniquenessNegation continuationIdentityNegation outerNegation
        conjunctionDisjunction condition
        (star_13_01 continuationIdentity (.apparent .zero) term.weaken) := rfl

def unaryReducibilityMatrix
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [argument] order) :
    Formula signature real
      [.function [argument] order 0]
      (bindOrder order argument) :=
  let phiWithFunction : Formula signature real
      [argument, .function [argument] order 0] order :=
    phi.rename (liftRenamingN [argument]
      (emptyRenaming (target := [.function [argument] order 0])))
  let function : Term signature real
      [argument, .function [argument] order 0]
      (.function [argument] order 0) := .apparent (.succ .zero)
  let x : Term signature real
      [argument, .function [argument] order 0] argument := .apparent .zero
  .always universal
    (equivalence negation disjunction phiWithFunction
      (applyUnary function x))

def star_12_1_formula
    (existential : ExistentialVocabulary signature
      (.function [argument] order 0) (bindOrder order argument))
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [argument] order) :
    Formula signature real []
      (bindOrder (bindOrder order argument)
        (.function [argument] order 0)) :=
  .sometimes existential
    (unaryReducibilityMatrix universal negation disjunction phi)

def binaryReducibilityMatrix
    (leftUniversal : signature.Universal leftSort order)
    (rightUniversal : signature.Universal rightSort
      (bindOrder order leftSort))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [leftSort, rightSort] order) :
    Formula signature real
      [.function [leftSort, rightSort] order 0]
      (bindOrder (bindOrder order leftSort) rightSort) :=
  let phiWithFunction : Formula signature real
      [leftSort, rightSort, .function [leftSort, rightSort] order 0] order :=
    phi.rename (liftRenamingN [leftSort, rightSort]
      (emptyRenaming
        (target := [.function [leftSort, rightSort] order 0])))
  let function : Term signature real
      [leftSort, rightSort, .function [leftSort, rightSort] order 0]
      (.function [leftSort, rightSort] order 0) :=
    .apparent (.succ (.succ .zero))
  let left : Term signature real
      [leftSort, rightSort, .function [leftSort, rightSort] order 0]
      leftSort := .apparent .zero
  let right : Term signature real
      [leftSort, rightSort, .function [leftSort, rightSort] order 0]
      rightSort := .apparent (.succ .zero)
  (equivalence negation disjunction phiWithFunction
    (applyBinary function left right)).always₂ leftUniversal rightUniversal

def star_12_11_formula
    (existential : ExistentialVocabulary signature
      (.function [leftSort, rightSort] order 0)
      (bindOrder (bindOrder order leftSort) rightSort))
    (leftUniversal : signature.Universal leftSort order)
    (rightUniversal : signature.Universal rightSort
      (bindOrder order leftSort))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [leftSort, rightSort] order) :
    Formula signature real []
      (bindOrder (bindOrder (bindOrder order leftSort) rightSort)
        (.function [leftSort, rightSort] order 0)) :=
  .sometimes existential
    (binaryReducibilityMatrix leftUniversal rightUniversal
      negation disjunction phi)

inductive Claim (signature : Signature) (real : Context) where
  | assertion {order : Nat} (formula : Formula signature real [] order)
  | significance {argument : RSort} {order : Nat}
      (matrix : Formula signature real [argument] order)
  | functionExistence {argument : RSort} {order : Nat}
      (matrix : Formula signature real [argument] order)

structure ClaimReading (signature : Signature) (real : Context) where
  printed : String
  parsed : Claim signature real

def UnaryReducibility
    {real : Context} {argument : RSort} {order : Nat}
    (_phi : Formula signature real [argument] order) :=
  { _function : Term signature real [] (.function [argument] order 0) //
    RSort.Predicative (.function [argument] order 0) }

def BinaryReducibility
    {real : Context} {leftSort rightSort : RSort} {order : Nat}
    (_phi : Formula signature real [leftSort, rightSort] order) :=
  { _function : Term signature real []
      (.function [leftSort, rightSort] order 0) //
    RSort.Predicative (.function [leftSort, rightSort] order 0) }

theorem Formula.disj_normalizeSameOrder
    {leftOrder rightOrder order : Nat}
    (leftEq : leftOrder = order)
    (rightEq : rightOrder = order)
    (disjunction : signature.Disjunction order)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    let resultEq := natMaxCongr leftEq rightEq
    Eq.mp (congrArg (Formula signature real apparent) resultEq)
        (.disj
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          left right) =
      sameDisjunction disjunction
        (Eq.mp (congrArg (Formula signature real apparent) leftEq) left)
        (Eq.mp (congrArg (Formula signature real apparent) rightEq) right) := by
  cases leftEq
  cases rightEq
  rfl

theorem mixedImplication_normalizeSameOrder
    {leftOrder rightOrder order : Nat}
    (leftEq : leftOrder = order)
    (rightEq : rightOrder = order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    let resultEq := natMaxCongr leftEq rightEq
    Eq.mp (congrArg (Formula signature real apparent) resultEq)
        (mixedImplication
          (Eq.mp (congrArg signature.Negation leftEq.symm) negation)
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          left right) =
      implication negation disjunction
        (Eq.mp (congrArg (Formula signature real apparent) leftEq) left)
        (Eq.mp (congrArg (Formula signature real apparent) rightEq) right) := by
  cases leftEq
  cases rightEq
  rfl

def Term.weakenReal
    (term : Term signature realCtx appCtx sort) :
    Term signature (fresh :: realCtx) appCtx sort :=
  match term with
  | .real v => .real (.succ v)
  | .apparent v => .apparent v
  | .symbol payload => .symbol payload

def Arguments.weakenReal
    (arguments : Arguments signature realCtx appCtx sorts) :
    Arguments signature (fresh :: realCtx) appCtx sorts :=
  match arguments with
  | .nil => .nil
  | .cons term tail => .cons term.weakenReal tail.weakenReal

def Formula.weakenReal
    (formula : Formula signature realCtx appCtx order) :
    Formula signature (fresh :: realCtx) appCtx order :=
  match formula with
  | .proposition term => .proposition term.weakenReal
  | .apply function arguments => .apply function.weakenReal arguments.weakenReal
  | .neg meaning body => .neg meaning body.weakenReal
  | .disj meaning left right => .disj meaning left.weakenReal right.weakenReal
  | .always meaning body => .always meaning body.weakenReal
  | .incompleteScope kind parameters resultOrder excess scopeOrder matrix continuation =>
      .incompleteScope kind parameters resultOrder excess scopeOrder
        matrix.weakenReal continuation.weakenReal
  | .descriptionScope sort conditionOrder scopeOrder condition continuation =>
      .descriptionScope sort conditionOrder scopeOrder
        condition.weakenReal continuation.weakenReal

@[simp] theorem Formula.substitute_cast
    (h : sourceOrder = targetOrder)
    (formula : Formula signature realCtx source sourceOrder)
    (sigma : Substitution signature realCtx source target) :
    (Eq.mp (congrArg (Formula signature realCtx source) h) formula).substitute sigma =
      Eq.mp (congrArg (Formula signature realCtx target) h)
        (formula.substitute sigma) := by
  cases h
  rfl

@[simp] theorem Formula.weakenReal_cast
    (h : sourceOrder = targetOrder)
    (formula : Formula signature realCtx apparent sourceOrder) :
    (Eq.mp (congrArg (Formula signature realCtx apparent) h) formula).weakenReal =
      Eq.mp (congrArg (Formula signature (fresh :: realCtx) apparent) h)
        formula.weakenReal := by
  cases h
  rfl

def star_9_34_formula
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order)
    (phi : Formula signature real [argument] order) :
    Formula signature real [] (bindOrder order argument) :=
  .always universal
    (implication negation disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))

inductive ImplicationNegation (signature : Signature) (real : Context) :
    {order : Nat} → signature.Negation order →
      Formula signature real [] order →
      Formula signature real [] order → Type where
  | star_1_01
      (negation : signature.Negation order)
      (formula : Formula signature real [] order) :
      ImplicationNegation signature real negation formula
        (.neg negation formula)
  | star_9_01
      (surfaceNegation : signature.Negation
        (bindOrder matrixOrder argument))
      (universal : signature.Universal argument matrixOrder)
      (existential : ExistentialVocabulary signature argument matrixOrder)
      (matrixNegation : signature.Negation matrixOrder)
      (body : Formula signature real [argument] matrixOrder) :
      ImplicationNegation signature real surfaceNegation
        (.always universal body)
        (star_9_01 existential matrixNegation body)
  | star_9_02
      (surfaceNegation : signature.Negation
        (bindOrder matrixOrder argument))
      (existential : ExistentialVocabulary signature argument matrixOrder)
      (universal : signature.Universal argument matrixOrder)
      (matrixNegation : signature.Negation matrixOrder)
      (body : Formula signature real [argument] matrixOrder) :
      ImplicationNegation signature real surfaceNegation
        (.sometimes existential body)
        (star_9_02 universal matrixNegation body)

def implicationScopeHead :
    Renaming (head :: apparent) (head :: tail :: apparent)
  | _, .zero => .zero
  | _, .succ v => .succ (.succ v)

inductive ImplicationDisjunction (signature : Signature) (real : Context) :
    {apparent : Context} →
    {leftOrder rightOrder resultOrder : Nat} →
    Formula signature real apparent leftOrder →
    Formula signature real apparent rightOrder →
    Formula signature real apparent resultOrder → Type where
  | star_1_01
      (disjunction : signature.Disjunction (max leftOrder rightOrder))
      (left : Formula signature real apparent leftOrder)
      (right : Formula signature real apparent rightOrder) :
      ImplicationDisjunction signature real left right
        (.disj disjunction left right)
  | star_1_01_same
      (disjunction : signature.Disjunction order)
      (left right : Formula signature real apparent order) :
      ImplicationDisjunction signature real left right
        (sameDisjunction disjunction left right)
  | star_9_03
      (matrixUniversal : signature.Universal argument matrixOrder)
      (scopeUniversal : signature.Universal argument resultOrder)
      (body : Formula signature real (argument :: apparent) matrixOrder)
      (fixed : Formula signature real apparent fixedOrder)
      (result : Formula signature real (argument :: apparent) resultOrder)
      (reading : ImplicationDisjunction signature real body
        (fixed.rename (fun v => .succ v)) result) :
      ImplicationDisjunction signature real
        (.always matrixUniversal body) fixed
        (.always scopeUniversal result)
  | star_9_04
      (matrixUniversal : signature.Universal argument matrixOrder)
      (scopeUniversal : signature.Universal argument resultOrder)
      (fixed : Formula signature real apparent fixedOrder)
      (body : Formula signature real (argument :: apparent) matrixOrder)
      (result : Formula signature real (argument :: apparent) resultOrder)
      (reading : ImplicationDisjunction signature real
        (fixed.rename (fun v => .succ v)) body result) :
      ImplicationDisjunction signature real fixed
        (.always matrixUniversal body)
        (.always scopeUniversal result)
  | star_9_05
      (matrixExistential : ExistentialVocabulary signature argument matrixOrder)
      (scopeExistential : ExistentialVocabulary signature argument resultOrder)
      (body : Formula signature real (argument :: apparent) matrixOrder)
      (fixed : Formula signature real apparent fixedOrder)
      (result : Formula signature real (argument :: apparent) resultOrder)
      (reading : ImplicationDisjunction signature real body
        (fixed.rename (fun v => .succ v)) result) :
      ImplicationDisjunction signature real
        (.sometimes matrixExistential body) fixed
        (.sometimes scopeExistential result)
  | star_9_06
      (matrixExistential : ExistentialVocabulary signature argument matrixOrder)
      (scopeExistential : ExistentialVocabulary signature argument resultOrder)
      (fixed : Formula signature real apparent fixedOrder)
      (body : Formula signature real (argument :: apparent) matrixOrder)
      (result : Formula signature real (argument :: apparent) resultOrder)
      (reading : ImplicationDisjunction signature real
        (fixed.rename (fun v => .succ v)) body result) :
      ImplicationDisjunction signature real fixed
        (.sometimes matrixExistential body)
        (.sometimes scopeExistential result)
  | star_9_07
      (leftUniversal : signature.Universal leftSort matrixOrder)
      (rightExistential : ExistentialVocabulary signature rightSort matrixOrder)
      (scopeUniversal : signature.Universal leftSort
        (bindOrder matrixOrder rightSort))
      (disjunction : signature.Disjunction matrixOrder)
      (leftBody : Formula signature real (leftSort :: apparent) matrixOrder)
      (rightBody : Formula signature real (rightSort :: apparent) matrixOrder) :
      ImplicationDisjunction signature real
        (.always leftUniversal leftBody)
        (.sometimes rightExistential rightBody)
        (star_9_07 rightExistential scopeUniversal disjunction
          (leftBody.rename (fun v => .succ v))
          (rightBody.rename implicationScopeHead))
  | star_9_08
      (leftExistential : ExistentialVocabulary signature leftSort matrixOrder)
      (rightUniversal : signature.Universal rightSort matrixOrder)
      (scopeUniversal : signature.Universal rightSort
        (bindOrder matrixOrder leftSort))
      (disjunction : signature.Disjunction matrixOrder)
      (leftBody : Formula signature real (leftSort :: apparent) matrixOrder)
      (rightBody : Formula signature real (rightSort :: apparent) matrixOrder) :
      ImplicationDisjunction signature real
        (.sometimes leftExistential leftBody)
        (.always rightUniversal rightBody)
        (star_9_08 leftExistential scopeUniversal disjunction
          (leftBody.rename implicationScopeHead)
          (rightBody.rename (fun v => .succ v)))

class ImplicationReading
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (p : Formula signature real [] leftOrder)
    (formula : Formula signature real [] formulaOrder)
    (q : outParam (Formula signature real [] rightOrder)) where
  negated : Formula signature real [] leftOrder
  negationDefinition :
    ImplicationNegation signature real negation p negated
  disjunctionDefinition :
    ImplicationDisjunction signature real negated q formula

instance mixedImplicationReading
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (p : Formula signature real [] leftOrder)
    (q : Formula signature real [] rightOrder) :
    ImplicationReading negation disjunction p
      (mixedImplication negation disjunction p q) q where
  negated := .neg negation p
  negationDefinition := .star_1_01 negation p
  disjunctionDefinition := .star_1_01 disjunction (.neg negation p) q

instance (priority := 1100) nestedMixedImplicationReading
    (innerNegation : signature.Negation leftOrder)
    (innerDisjunction : signature.Disjunction (max leftOrder middleOrder))
    (outerNegation : signature.Negation (max leftOrder middleOrder))
    (outerDisjunction : signature.Disjunction
      (max (max leftOrder middleOrder) rightOrder))
    (p : Formula signature real [] leftOrder)
    (q : Formula signature real [] middleOrder)
    (r : Formula signature real [] rightOrder) :
    ImplicationReading outerNegation outerDisjunction
      (mixedImplication innerNegation innerDisjunction p q)
      (mixedImplication outerNegation outerDisjunction
        (.disj innerDisjunction (.neg innerNegation p) q) r) r :=
  mixedImplicationReading outerNegation outerDisjunction
    (mixedImplication innerNegation innerDisjunction p q) r

class Star1_6Reading
    {pOrder qOrder rOrder : Nat} {formulaOrder : outParam Nat}
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (canonicalOuterNegation : signature.Negation (max qOrder rOrder))
    (canonicalConsequenceNegation : signature.Negation (max pOrder qOrder))
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (canonicalConsequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (canonicalOuterDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (formula : outParam (Formula signature real [] formulaOrder)) where
  qrFormulaOrder : Nat
  pqFormulaOrder : Nat
  prFormulaOrder : Nat
  consequenceFormulaOrder : Nat
  qNegated : Formula signature real [] qOrder
  qrFormula : Formula signature real [] qrFormulaOrder
  pqFormula : Formula signature real [] pqFormulaOrder
  prFormula : Formula signature real [] prFormulaOrder
  consequenceNegated : Formula signature real [] pqFormulaOrder
  consequenceFormula : Formula signature real [] consequenceFormulaOrder
  qrNegated : Formula signature real [] qrFormulaOrder
  consequenceNegation : signature.Negation pqFormulaOrder
  outerNegation : signature.Negation qrFormulaOrder
  qNegationDefinition :
    ImplicationNegation signature real qNegation q qNegated
  qrDisjunctionDefinition :
    ImplicationDisjunction signature real qNegated r qrFormula
  pqDisjunctionDefinition :
    ImplicationDisjunction signature real p q pqFormula
  prDisjunctionDefinition :
    ImplicationDisjunction signature real p r prFormula
  consequenceNegationDefinition :
    ImplicationNegation signature real consequenceNegation pqFormula
      consequenceNegated
  consequenceDisjunctionDefinition :
    ImplicationDisjunction signature real consequenceNegated prFormula
      consequenceFormula
  outerNegationDefinition :
    ImplicationNegation signature real outerNegation qrFormula qrNegated
  outerDisjunctionDefinition :
    ImplicationDisjunction signature real qrNegated consequenceFormula formula

instance star1_6MixedReading
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction (max qOrder rOrder))
    (outerNegation : signature.Negation (max qOrder rOrder))
    (consequenceNegation : signature.Negation (max pOrder qOrder))
    (pqDisjunction : signature.Disjunction (max pOrder qOrder))
    (prDisjunction : signature.Disjunction (max pOrder rOrder))
    (consequenceDisjunction : signature.Disjunction
      (max (max pOrder qOrder) (max pOrder rOrder)))
    (outerDisjunction : signature.Disjunction
      (max (max qOrder rOrder)
        (max (max pOrder qOrder) (max pOrder rOrder))))
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder) :
    Star1_6Reading qNegation qrDisjunction outerNegation
      consequenceNegation pqDisjunction prDisjunction
      consequenceDisjunction outerDisjunction p q r
      (mixedImplication outerNegation outerDisjunction
        (mixedImplication qNegation qrDisjunction q r)
      (mixedImplication consequenceNegation consequenceDisjunction
          (.disj pqDisjunction p q) (.disj prDisjunction p r))) where
  qrFormulaOrder := max qOrder rOrder
  pqFormulaOrder := max pOrder qOrder
  prFormulaOrder := max pOrder rOrder
  consequenceFormulaOrder := max (max pOrder qOrder) (max pOrder rOrder)
  qNegated := .neg qNegation q
  qrFormula := mixedImplication qNegation qrDisjunction q r
  pqFormula := .disj pqDisjunction p q
  prFormula := .disj prDisjunction p r
  consequenceNegated := .neg consequenceNegation (.disj pqDisjunction p q)
  consequenceFormula := mixedImplication consequenceNegation
    consequenceDisjunction (.disj pqDisjunction p q)
      (.disj prDisjunction p r)
  qrNegated := .neg outerNegation
    (mixedImplication qNegation qrDisjunction q r)
  consequenceNegation := consequenceNegation
  outerNegation := outerNegation
  qNegationDefinition := .star_1_01 qNegation q
  qrDisjunctionDefinition := .star_1_01 qrDisjunction
    (.neg qNegation q) r
  pqDisjunctionDefinition := .star_1_01 pqDisjunction p q
  prDisjunctionDefinition := .star_1_01 prDisjunction p r
  consequenceNegationDefinition := .star_1_01 consequenceNegation
    (.disj pqDisjunction p q)
  consequenceDisjunctionDefinition := .star_1_01 consequenceDisjunction
    (.neg consequenceNegation (.disj pqDisjunction p q))
    (.disj prDisjunction p r)
  outerNegationDefinition := .star_1_01 outerNegation
    (mixedImplication qNegation qrDisjunction q r)
  outerDisjunctionDefinition := .star_1_01 outerDisjunction
    (.neg outerNegation (mixedImplication qNegation qrDisjunction q r))
    (mixedImplication consequenceNegation consequenceDisjunction
      (.disj pqDisjunction p q) (.disj prDisjunction p r))

inductive Derivation {signature : Signature} :
    {real : Context} → Claim signature real → Prop where
  | star_1_1 {pOrder qOrder : Nat}
      {p : Formula signature [] [] pOrder}
      {q : Formula signature [] [] qOrder}
      (negation : signature.Negation pOrder)
      (disjunction : signature.Disjunction (max pOrder qOrder)) :
      Derivation (.assertion p) →
      Derivation (.assertion (mixedImplication negation disjunction p q)) →
      Derivation (.assertion q)
  | star_1_11 {real : Context} {realSort : RSort} {pOrder qOrder : Nat}
      {p : Formula signature (realSort :: real) [] pOrder}
      {q : Formula signature (realSort :: real) [] qOrder}
      (negation : signature.Negation pOrder)
      (disjunction : signature.Disjunction (max pOrder qOrder)) :
      Derivation (.assertion p) →
      Derivation (.assertion (mixedImplication negation disjunction p q)) →
      Derivation (.assertion q)
  | star_1_2 {order : Nat} (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (p : Formula signature real [] order) :
      Derivation (.assertion
        (implication negation disjunction (sameDisjunction disjunction p p) p))
  | star_1_3 {pOrder qOrder : Nat}
      (qNegation : signature.Negation qOrder)
      (innerDisjunction : signature.Disjunction (max pOrder qOrder))
      (outerDisjunction : signature.Disjunction
        (max qOrder (max pOrder qOrder)))
      (p : Formula signature real [] pOrder)
      (q : Formula signature real [] qOrder) :
      Derivation (.assertion (mixedImplication qNegation outerDisjunction q
        (.disj innerDisjunction p q)))
  | star_1_4 {pOrder qOrder : Nat}
      (antecedentNegation : signature.Negation (max pOrder qOrder))
      (leftDisjunction : signature.Disjunction (max pOrder qOrder))
      (rightDisjunction : signature.Disjunction (max qOrder pOrder))
      (outerDisjunction : signature.Disjunction
        (max (max pOrder qOrder) (max qOrder pOrder)))
      (p : Formula signature real [] pOrder)
      (q : Formula signature real [] qOrder) :
      Derivation (.assertion
        (mixedImplication antecedentNegation outerDisjunction
          (.disj leftDisjunction p q) (.disj rightDisjunction q p)))
  | star_1_5 {pOrder qOrder rOrder : Nat}
      (antecedentNegation : signature.Negation
        (max pOrder (max qOrder rOrder)))
      (qrDisjunction : signature.Disjunction (max qOrder rOrder))
      (leftDisjunction : signature.Disjunction
        (max pOrder (max qOrder rOrder)))
      (prDisjunction : signature.Disjunction (max pOrder rOrder))
      (rightDisjunction : signature.Disjunction
        (max qOrder (max pOrder rOrder)))
      (outerDisjunction : signature.Disjunction
        (max (max pOrder (max qOrder rOrder))
          (max qOrder (max pOrder rOrder))))
      (p : Formula signature real [] pOrder)
      (q : Formula signature real [] qOrder)
      (r : Formula signature real [] rOrder) :
      Derivation (.assertion
        (mixedImplication antecedentNegation outerDisjunction
          (.disj leftDisjunction p (.disj qrDisjunction q r))
          (.disj rightDisjunction q (.disj prDisjunction p r))))
  | star_1_6 {pOrder qOrder rOrder : Nat}
      (qNegation : signature.Negation qOrder)
      (qrDisjunction : signature.Disjunction (max qOrder rOrder))
      (outerNegation : signature.Negation (max qOrder rOrder))
      (pqNegation : signature.Negation (max pOrder qOrder))
      (pqDisjunction : signature.Disjunction (max pOrder qOrder))
      (prDisjunction : signature.Disjunction (max pOrder rOrder))
      (innerDisjunction : signature.Disjunction
        (max (max pOrder qOrder) (max pOrder rOrder)))
      (outerDisjunction : signature.Disjunction
        (max (max qOrder rOrder)
          (max (max pOrder qOrder) (max pOrder rOrder))))
      (p : Formula signature real [] pOrder)
      (q : Formula signature real [] qOrder)
      (r : Formula signature real [] rOrder)
      {formula : Formula signature real [] formulaOrder}
      [reading : Star1_6Reading qNegation qrDisjunction outerNegation
        pqNegation pqDisjunction prDisjunction innerDisjunction
        outerDisjunction p q r formula] :
      Derivation (.assertion formula)
  | star_9_1 {argument : RSort} {matrixOrder : Nat}
      (existential : ExistentialVocabulary signature argument matrixOrder)
      (negation : signature.Negation matrixOrder)
      (disjunction : signature.Disjunction
        (max matrixOrder (bindOrder matrixOrder argument)))
      (body : Formula signature real [argument] matrixOrder)
      (value : Term signature real [] argument) :
      Derivation (.assertion (mixedImplication negation disjunction
        (body.instantiate value) (.sometimes existential body)))
  | star_9_11 {argument : RSort} {matrixOrder : Nat}
      (existential : ExistentialVocabulary signature argument matrixOrder)
      (negation : signature.Negation matrixOrder)
      (matrixDisjunction : signature.Disjunction matrixOrder)
      (disjunction : signature.Disjunction
        (max matrixOrder (bindOrder matrixOrder argument)))
      (body : Formula signature real [argument] matrixOrder)
      (x y : Term signature real [] argument) :
      Derivation (.assertion (mixedImplication negation disjunction
        (sameDisjunction matrixDisjunction (body.instantiate x) (body.instantiate y))
        (.sometimes existential body)))

  | star_9_12 {leftOrder rightOrder implicationOrder : Nat}
      {p : Formula signature real [] leftOrder}
      {q : Formula signature real [] rightOrder}
      {implicationFormula : Formula signature real [] implicationOrder}
      (negation : signature.Negation leftOrder)
      (disjunction : signature.Disjunction (max leftOrder rightOrder))
      (premissLine : Derivation (.assertion p))
      (implicationLine : Derivation (.assertion implicationFormula))
      [ImplicationReading negation disjunction p implicationFormula q] :
      Derivation (.assertion q)
  | star_9_13 {argument : RSort} {matrixOrder : Nat}
      (universal : signature.Universal argument matrixOrder)
      (body : Formula signature real [argument] matrixOrder) :
      Derivation (.assertion
        (body.weakenReal.instantiate
          (.real (.zero : Var (argument :: real) argument)))) →
      Derivation (.assertion (.always universal body))
  | star_10_1 {argument : RSort} {matrixOrder : Nat}
      (universal : signature.Universal argument matrixOrder)
      (negation : signature.Negation (bindOrder matrixOrder argument))
      (disjunction : signature.Disjunction
        (max (bindOrder matrixOrder argument) matrixOrder))
      (body : Formula signature real [argument] matrixOrder)
      (value : Term signature real [] argument) :
      Derivation (.assertion (mixedImplication negation disjunction
        (.always universal body) (body.instantiate value)))
  | star_10_11 {argument : RSort} {matrixOrder : Nat}
      (universal : signature.Universal argument matrixOrder)
      (body : Formula signature real [argument] matrixOrder) :
      Derivation (.assertion
        (body.weakenReal.instantiate
          (.real (.zero : Var (argument :: real) argument)))) →
      Derivation (.assertion (.always universal body))
  | star_10_121 {argument : RSort} {matrixOrder : Nat}
      (body : Formula signature real [argument] matrixOrder) :
      Derivation (.significance body)
  | star_10_122 {argument : RSort} {matrixOrder : Nat}
      (body : Formula signature real [argument] matrixOrder) :
      Derivation (.functionExistence body)
  | star_11_07 {leftSort rightSort : RSort} {matrixOrder : Nat}
      (leftInner : signature.Universal leftSort matrixOrder)
      (rightOuter : signature.Universal rightSort
        (bindOrder matrixOrder leftSort))
      (rightInner : signature.Universal rightSort matrixOrder)
      (leftOuter : signature.Universal leftSort
        (bindOrder matrixOrder rightSort))
      (negation : signature.Negation
        (bindOrder (bindOrder matrixOrder leftSort) rightSort))
      (disjunction : signature.Disjunction
        (max (bindOrder (bindOrder matrixOrder leftSort) rightSort)
          (bindOrder (bindOrder matrixOrder rightSort) leftSort)))
      (body : Formula signature real [leftSort, rightSort] matrixOrder) :
      Derivation (.assertion (star_11_07_formula leftInner rightOuter
        rightInner leftOuter negation disjunction body))
  | star_11_1 {leftSort rightSort : RSort} {matrixOrder : Nat}
      (inner : signature.Universal leftSort matrixOrder)
      (outer : signature.Universal rightSort
        (bindOrder matrixOrder leftSort))
      (negation : signature.Negation
        (bindOrder (bindOrder matrixOrder leftSort) rightSort))
      (disjunction : signature.Disjunction
        (max (bindOrder (bindOrder matrixOrder leftSort) rightSort) matrixOrder))
      (body : Formula signature real [leftSort, rightSort] matrixOrder)
      (left : Term signature real [] leftSort)
      (right : Term signature real [] rightSort) :
      Derivation (.assertion (star_11_1_formula inner outer negation
        disjunction body left right))
  | star_11_11 {leftSort rightSort : RSort} {matrixOrder : Nat}
      (inner : signature.Universal leftSort matrixOrder)
      (outer : signature.Universal rightSort
        (bindOrder matrixOrder leftSort))
      (body : Formula signature real [leftSort, rightSort] matrixOrder) :
      (∀ left : Term signature real [] leftSort,
        ∀ right : Term signature real [] rightSort,
          Derivation (.assertion (body.instantiate₂ left right))) →
      Derivation (.assertion (body.always₂ inner outer))
  | star_12_1 {argument : RSort} {order : Nat}
      (existential : ExistentialVocabulary signature
        (.function [argument] order 0) (bindOrder order argument))
      (universal : signature.Universal argument order)
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (phi : Formula signature real [argument] order) :
      Derivation (.assertion
        (star_12_1_formula existential universal negation disjunction phi))
  | star_12_11 {leftSort rightSort : RSort} {order : Nat}
      (existential : ExistentialVocabulary signature
        (.function [leftSort, rightSort] order 0)
        (bindOrder (bindOrder order leftSort) rightSort))
      (leftUniversal : signature.Universal leftSort order)
      (rightUniversal : signature.Universal rightSort
        (bindOrder order leftSort))
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (phi : Formula signature real [leftSort, rightSort] order) :
      Derivation (.assertion (star_12_11_formula existential leftUniversal
        rightUniversal negation disjunction phi))

notation:45 "⊢ᵣ " formula =>
  PM.RamifiedSyntax.Derivation (PM.RamifiedSyntax.Claim.assertion formula)

theorem Derivation.castAssertion
    {left right : Formula signature real [] order}
    (equality : left = right) :
    Derivation (.assertion right) → Derivation (.assertion left) :=
  fun derivation => Eq.rec (motive := fun formula _ =>
      @Derivation signature real (@Claim.assertion signature real order formula))
    derivation equality.symm

private theorem Derivation.uncastAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) equality) formula)) →
      Derivation (.assertion formula) := by
  cases equality
  exact fun derivation => derivation

private theorem Derivation.castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

theorem Derivation.star_1_1_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature [] [] order}
    (line1 : Derivation (.assertion p))
    (line2 : Derivation (.assertion
      (implication negation disjunction p q))) :
    Derivation (.assertion q) := by
  let equality := natMaxSelf order
  apply Derivation.star_1_1 negation
    (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
    line1
  exact Derivation.uncastAssertionOrder equality
    (mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction) p q)
    (Derivation.castAssertion
      (mixedImplication_normalizeSameOrder rfl rfl
        negation disjunction p q)
      line2)

theorem Derivation.star_1_11_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature (realSort :: real) [] order}
    (line1 : Derivation (.assertion p))
    (line2 : Derivation (.assertion
      (implication negation disjunction p q))) :
    Derivation (.assertion q) := by
  let equality := natMaxSelf order
  apply Derivation.star_1_11 negation
    (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
    line1
  exact Derivation.uncastAssertionOrder equality
    (mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction) p q)
    (Derivation.castAssertion
      (mixedImplication_normalizeSameOrder rfl rfl
        negation disjunction p q)
      line2)

theorem star_1_3_normalizeSameOrder
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    let pairEq := natMaxSelf order
    let resultEq := natMaxCongr rfl pairEq
    Eq.mp (congrArg (Formula signature real []) resultEq)
        (mixedImplication negation
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          q
          (.disj
            (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
            p q)) =
      implication negation disjunction q
        (sameDisjunction disjunction p q) := by
  exact mixedImplication_normalizeSameOrder rfl (natMaxSelf order)
    negation disjunction q
    (.disj
      (Eq.mp (congrArg signature.Disjunction
        (natMaxSelf order).symm) disjunction)
      p q)

theorem Derivation.star_1_3_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    Derivation (.assertion (implication negation disjunction q
      (sameDisjunction disjunction p q))) := by
  let pairEq := natMaxSelf order
  let resultEq := natMaxCongr rfl pairEq
  let innerDisjunction :=
    Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let rawFormula := mixedImplication negation outerDisjunction q
    (.disj innerDisjunction p q)
  have rawLine : Derivation (.assertion rawFormula) :=
    Derivation.star_1_3 negation innerDisjunction outerDisjunction p q
  have castLine : Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) resultEq) rawFormula)) :=
    Derivation.castAssertionOrder resultEq rawFormula rawLine
  exact Derivation.castAssertion
    (star_1_3_normalizeSameOrder negation disjunction p q).symm castLine

theorem star_1_4_normalizeSameOrder
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    let pairEq := natMaxSelf order
    let resultEq := natMaxCongr pairEq pairEq
    Eq.mp (congrArg (Formula signature real []) resultEq)
        (mixedImplication
          (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          (.disj
            (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
            p q)
          (.disj
            (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
            q p)) =
      implication negation disjunction
        (sameDisjunction disjunction p q)
        (sameDisjunction disjunction q p) := by
  let pairEq := natMaxSelf order
  let left := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p q
  let right := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q p
  exact Eq.trans
    (mixedImplication_normalizeSameOrder pairEq pairEq
      negation disjunction left right)
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) pairEq) right))
        (Formula.disj_normalizeSameOrder rfl rfl disjunction p q))
      (congrArg (implication negation disjunction
          (sameDisjunction disjunction p q))
        (Formula.disj_normalizeSameOrder rfl rfl disjunction q p)))

theorem Derivation.star_1_4_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    Derivation (.assertion (implication negation disjunction
      (sameDisjunction disjunction p q)
      (sameDisjunction disjunction q p))) := by
  let pairEq := natMaxSelf order
  let resultEq := natMaxCongr pairEq pairEq
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation pairEq.symm) negation
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let rawFormula := mixedImplication pairNegation outerDisjunction
    (.disj pairDisjunction p q) (.disj pairDisjunction q p)
  have rawLine : Derivation (.assertion rawFormula) :=
    Derivation.star_1_4 pairNegation pairDisjunction pairDisjunction
      outerDisjunction p q
  have castLine : Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) resultEq) rawFormula)) :=
    Derivation.castAssertionOrder resultEq rawFormula rawLine
  exact Derivation.castAssertion
    (star_1_4_normalizeSameOrder negation disjunction p q).symm castLine

theorem star_1_5_normalizeSameOrder
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    let pairEq := natMaxSelf order
    let nestedEq := natMaxCongr rfl pairEq
    let resultEq := natMaxCongr nestedEq nestedEq
    Eq.mp (congrArg (Formula signature real []) resultEq)
        (mixedImplication
          (Eq.mp (congrArg signature.Negation nestedEq.symm) negation)
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          (.disj
            (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction)
            p
            (.disj
              (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
              q r))
          (.disj
            (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction)
            q
            (.disj
              (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
              p r))) =
      implication negation disjunction
        (sameDisjunction disjunction p (sameDisjunction disjunction q r))
        (sameDisjunction disjunction q (sameDisjunction disjunction p r)) := by
  let pairEq := natMaxSelf order
  let nestedEq := natMaxCongr rfl pairEq
  let qr := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q r
  let pr := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p r
  let left := Formula.disj
    (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction) p qr
  let right := Formula.disj
    (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction) q pr
  have qrEq := Formula.disj_normalizeSameOrder rfl rfl disjunction q r
  have prEq := Formula.disj_normalizeSameOrder rfl rfl disjunction p r
  have leftStep := Formula.disj_normalizeSameOrder
    rfl pairEq disjunction p qr
  have rightStep := Formula.disj_normalizeSameOrder
    rfl pairEq disjunction q pr
  have leftEq := Eq.trans leftStep
    (congrArg (sameDisjunction disjunction p) qrEq)
  have rightEq := Eq.trans rightStep
    (congrArg (sameDisjunction disjunction q) prEq)
  exact Eq.trans
    (mixedImplication_normalizeSameOrder nestedEq nestedEq
      negation disjunction left right)
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) nestedEq) right)) leftEq)
      (congrArg (implication negation disjunction
          (sameDisjunction disjunction p (sameDisjunction disjunction q r)))
        rightEq))

theorem Derivation.star_1_5_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Derivation (.assertion (implication negation disjunction
      (sameDisjunction disjunction p (sameDisjunction disjunction q r))
      (sameDisjunction disjunction q (sameDisjunction disjunction p r)))) := by
  let pairEq := natMaxSelf order
  let nestedEq := natMaxCongr rfl pairEq
  let resultEq := natMaxCongr nestedEq nestedEq
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction
  let nestedDisjunction :=
    Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction
  let nestedNegation :=
    Eq.mp (congrArg signature.Negation nestedEq.symm) negation
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let rawFormula := mixedImplication nestedNegation outerDisjunction
    (.disj nestedDisjunction p (.disj pairDisjunction q r))
    (.disj nestedDisjunction q (.disj pairDisjunction p r))
  have rawLine : Derivation (.assertion rawFormula) :=
    Derivation.star_1_5 nestedNegation pairDisjunction nestedDisjunction
      pairDisjunction nestedDisjunction outerDisjunction p q r
  have castLine : Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) resultEq) rawFormula)) :=
    Derivation.castAssertionOrder resultEq rawFormula rawLine
  exact Derivation.castAssertion
    (star_1_5_normalizeSameOrder negation disjunction p q r).symm castLine

theorem star_1_6_normalizeSameOrder
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    let pairEq := natMaxSelf order
    let consequentEq := natMaxCongr pairEq pairEq
    let resultEq := natMaxCongr pairEq consequentEq
    Eq.mp (congrArg (Formula signature real []) resultEq)
        (mixedImplication
          (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          (mixedImplication negation
            (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
            q r)
          (mixedImplication
            (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
            (Eq.mp (congrArg signature.Disjunction consequentEq.symm)
              disjunction)
            (.disj
              (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
              p q)
            (.disj
              (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
              p r))) =
      implication negation disjunction
        (implication negation disjunction q r)
        (implication negation disjunction
          (sameDisjunction disjunction p q)
          (sameDisjunction disjunction p r)) := by
  let pairEq := natMaxSelf order
  let consequentEq := natMaxCongr pairEq pairEq
  let antecedent := mixedImplication negation
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q r
  let pq := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p q
  let pr := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p r
  let consequent := mixedImplication
    (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
    (Eq.mp (congrArg signature.Disjunction consequentEq.symm) disjunction)
    pq pr
  have antecedentEq := mixedImplication_normalizeSameOrder
    rfl rfl negation disjunction q r
  have pqEq := Formula.disj_normalizeSameOrder rfl rfl disjunction p q
  have prEq := Formula.disj_normalizeSameOrder rfl rfl disjunction p r
  have consequentStep := mixedImplication_normalizeSameOrder
    pairEq pairEq negation disjunction pq pr
  have consequentEq' := Eq.trans consequentStep
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) pairEq) pr)) pqEq)
      (congrArg (implication negation disjunction
          (sameDisjunction disjunction p q)) prEq))
  exact Eq.trans
    (mixedImplication_normalizeSameOrder pairEq consequentEq
      negation disjunction antecedent consequent)
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) consequentEq) consequent))
        antecedentEq)
      (congrArg (implication negation disjunction
          (implication negation disjunction q r)) consequentEq'))

theorem Derivation.star_1_6_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Derivation (.assertion (implication negation disjunction
      (implication negation disjunction q r)
      (implication negation disjunction
        (sameDisjunction disjunction p q)
        (sameDisjunction disjunction p r)))) := by
  let pairEq := natMaxSelf order
  let consequentEq := natMaxCongr pairEq pairEq
  let resultEq := natMaxCongr pairEq consequentEq
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation pairEq.symm) negation
  let consequentDisjunction :=
    Eq.mp (congrArg signature.Disjunction consequentEq.symm) disjunction
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let antecedent := mixedImplication negation pairDisjunction q r
  let consequent := mixedImplication pairNegation consequentDisjunction
    (.disj pairDisjunction p q) (.disj pairDisjunction p r)
  let rawFormula := mixedImplication pairNegation outerDisjunction
    antecedent consequent
  have rawLine : Derivation (.assertion rawFormula) :=
    Derivation.star_1_6 negation pairDisjunction pairNegation pairNegation
      pairDisjunction pairDisjunction consequentDisjunction outerDisjunction
      p q r
  have castLine : Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) resultEq) rawFormula)) :=
    Derivation.castAssertionOrder resultEq rawFormula rawLine
  exact Derivation.castAssertion
    (star_1_6_normalizeSameOrder negation disjunction p q r).symm castLine

theorem Derivation.star_9_12_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature real [] order}
    (line1 : Derivation (.assertion p))
    (line2 : Derivation (.assertion
      (implication negation disjunction p q))) :
    Derivation (.assertion q) := by
  let mixedDisjunction :=
    Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction
  have line3 : Derivation (.assertion
      (mixedImplication negation mixedDisjunction p q)) :=
    Derivation.uncastAssertionOrder (natMaxSelf order)
    (mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction)
      p q) line2
  exact Derivation.star_9_12 negation mixedDisjunction line1 line3

abbrev IsIdentitySubstitution (sigma : Substitution signature realCtx ctx ctx) : Prop :=
  ∀ {sort : RSort} (v : Var ctx sort), sigma v = .apparent v

theorem Term.substitute_eq_self
    {sigma : Substitution signature realCtx ctx ctx}
    (identity : IsIdentitySubstitution sigma)
    (term : Term signature realCtx ctx sort) :
    term.substitute sigma = term := by
  cases term with
  | real v => rfl
  | apparent v => exact identity v
  | symbol payload => rfl

theorem Arguments.substitute_eq_self
    {sigma : Substitution signature realCtx ctx ctx}
    (identity : IsIdentitySubstitution sigma)
    (arguments : Arguments signature realCtx ctx sorts) :
    arguments.substitute sigma = arguments := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.substitute_eq_self identity, ih]

theorem liftSubstitution_eq_self
    {sigma : Substitution signature realCtx ctx ctx}
    (identity : IsIdentitySubstitution sigma) :
    IsIdentitySubstitution (liftSubstitution (sort := binder) sigma) := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v =>
      show (sigma v).weaken = Term.apparent v.succ
      exact congrArg Term.weaken (identity v)

theorem liftSubstitutionN_eq_self
    (binders : List RSort)
    {sigma : Substitution signature realCtx ctx ctx}
    (identity : IsIdentitySubstitution sigma) :
    IsIdentitySubstitution (liftSubstitutionN binders sigma) := by
  induction binders with
  | nil => exact identity
  | cons binder rest ih => exact liftSubstitution_eq_self ih

theorem Formula.substitute_eq_self
    (formula : Formula signature realCtx ctx order)
    {sigma : Substitution signature realCtx ctx ctx}
    (identity : IsIdentitySubstitution sigma) :
    formula.substitute sigma = formula := by
  induction formula with
  | proposition term =>
      show Formula.proposition _ = _; rw [Term.substitute_eq_self identity]
  | apply function arguments =>
      show Formula.apply _ _ = _
      rw [Term.substitute_eq_self identity, Arguments.substitute_eq_self identity]
  | neg meaning body ih => show Formula.neg _ _ = _; rw [ih identity]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = _; rw [leftIH identity, rightIH identity]
  | always meaning body ih =>
      show Formula.always _ _ = _; rw [ih (liftSubstitution_eq_self identity)]
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ = _
      rw [matrixIH (liftSubstitutionN_eq_self parameters identity),
        continuationIH (liftSubstitution_eq_self identity)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ = _
      rw [conditionIH (liftSubstitution_eq_self identity),
        continuationIH (liftSubstitution_eq_self identity)]

theorem Term.weakenReal_rename
    (rho : Renaming source target)
    (term : Term signature realCtx source sort) :
    (term.rename rho).weakenReal (fresh := fresh) = term.weakenReal.rename rho := by
  cases term <;> rfl

theorem Arguments.weakenReal_rename
    (rho : Renaming source target)
    (arguments : Arguments signature realCtx source sorts) :
    (arguments.rename rho).weakenReal (fresh := fresh) =
      arguments.weakenReal.rename rho := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.weakenReal_rename, ih]

theorem Formula.weakenReal_rename
    (formula : Formula signature realCtx source order)
    (rho : Renaming source target) :
    (formula.rename rho).weakenReal (fresh := fresh) =
      formula.weakenReal.rename rho := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.weakenReal_rename]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.weakenReal_rename, Arguments.weakenReal_rename]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH, rightIH]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      rw [ih]
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ = Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH, continuationIH]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ = Formula.descriptionScope _ _ _ _ _
      rw [conditionIH, continuationIH]

@[simp] theorem implication_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx source order)
    (sigma : Substitution signature realCtx source target) :
    (implication negation disjunction left right).substitute sigma =
      implication negation disjunction (left.substitute sigma)
        (right.substitute sigma) :=
  Eq.trans
    (Formula.substitute_cast (natMaxSelf order) _ sigma)
    (show Eq.mp (congrArg (Formula signature realCtx target) (natMaxSelf order))
          ((mixedImplication negation
            (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction)
            left right).substitute sigma) = _ from rfl)

@[simp] theorem implication_weakenReal
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    (implication negation disjunction left right).weakenReal (fresh := fresh) =
      implication negation disjunction left.weakenReal right.weakenReal :=
  Eq.trans
    (Formula.weakenReal_cast (natMaxSelf order) _)
    (show Eq.mp
          (congrArg (Formula signature (fresh :: realCtx) apparent) (natMaxSelf order))
          ((mixedImplication negation
            (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction)
            left right).weakenReal) = _ from rfl)

@[simp] theorem sameDisjunction_substitute
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx source order)
    (sigma : Substitution signature realCtx source target) :
    (sameDisjunction disjunction left right).substitute sigma =
      sameDisjunction disjunction (left.substitute sigma)
        (right.substitute sigma) :=
  Eq.trans
    (Formula.substitute_cast (natMaxSelf order) _ sigma)
    (show Eq.mp (congrArg (Formula signature realCtx target) (natMaxSelf order))
          ((Formula.disj
            (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction)
            left right).substitute sigma) = _ from rfl)

@[simp] theorem sameDisjunction_weakenReal
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    (sameDisjunction disjunction left right).weakenReal (fresh := fresh) =
      sameDisjunction disjunction left.weakenReal right.weakenReal :=
  Eq.trans
    (Formula.weakenReal_cast (natMaxSelf order) _)
    (show Eq.mp
          (congrArg (Formula signature (fresh :: realCtx) apparent) (natMaxSelf order))
          ((Formula.disj
            (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction)
            left right).weakenReal) = _ from rfl)

@[simp] theorem Formula.closed_weakenReal_instantiate
    (p : Formula signature real [] order)
    (argument : RSort) (value : Term signature (argument :: real) [] argument) :
    ((p.rename (fun v => .succ v) : Formula signature real [argument] order).weakenReal
        (fresh := argument)).instantiate value
      = p.weakenReal := by
  rw [Formula.weakenReal_rename, Formula.instantiate, Formula.rename_substitute]
  exact Formula.substitute_eq_self _ (fun v => nomatch v)

@[simp] theorem Formula.closed_weakenReal_instantiateSubstitution
    (p : Formula signature real [] order)
    (argument : RSort) (value : Term signature (argument :: real) [] argument) :
    ((p.rename (fun v => .succ v) : Formula signature real [argument] order).weakenReal
        (fresh := argument)).substitute (instantiateSubstitution value) =
      p.weakenReal := by
  exact Formula.closed_weakenReal_instantiate p argument value

theorem star_9_34_instantiation_eq
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0)
    (value : Term signature (argument :: real) [] argument) :
    (implication negation disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)).weakenReal.instantiate value =
      implication negation disjunction
        (phi.weakenReal.substitute (instantiateSubstitution value))
        (sameDisjunction disjunction p.weakenReal
          (phi.weakenReal.substitute (instantiateSubstitution value))) :=
  Eq.trans
    (congrArg (fun formula => formula.instantiate value)
      (implication_weakenReal negation disjunction phi
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)))
    (Eq.trans
      (implication_substitute negation disjunction phi.weakenReal
        (sameDisjunction disjunction
          (p.rename (fun v => .succ v)).weakenReal phi.weakenReal)
        (instantiateSubstitution value))
      (congrArg (implication negation disjunction
          (phi.weakenReal.substitute (instantiateSubstitution value)))
        (Eq.trans
          (sameDisjunction_substitute disjunction
            (p.rename (fun v => .succ v)).weakenReal phi.weakenReal
            (instantiateSubstitution value))
          (congrArg (fun left => sameDisjunction disjunction left
              (phi.weakenReal.substitute (instantiateSubstitution value)))
            (Formula.closed_weakenReal_instantiateSubstitution p argument value)))))

theorem star_9_34
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ star_9_34_formula universal negation disjunction p phi :=
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  let rawLine := Derivation.star_1_3_same negation disjunction p.weakenReal
    (phi.weakenReal.substitute (instantiateSubstitution value))
  let line1 :
      ⊢ᵣ implication negation disjunction
        (phi.weakenReal.substitute (instantiateSubstitution value))
        (sameDisjunction disjunction p.weakenReal
          (phi.weakenReal.substitute (instantiateSubstitution value))) :=
    Derivation.castAssertion (by rfl) rawLine
  let formulaEq := star_9_34_instantiation_eq negation disjunction p phi value
  Derivation.star_9_13 universal
    (implication negation disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))
    (Derivation.castAssertion formulaEq line1)

def star_10_1_reading
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) : ClaimReading signature real where
  printed := "⊢ : (x).φx .⊃ .φy"
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal body) (body.instantiate value))

def star_12_1_reading
    (existential : ExistentialVocabulary signature
      (.function [argument] order 0) (bindOrder order argument))
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [argument] order) :
    ClaimReading signature real where
  printed := "⊢ : (∃f) : φx .≡ₓ. f!x  Pp."
  parsed := .assertion
    (star_12_1_formula existential universal negation disjunction phi)

def star_12_11_reading
    (existential : ExistentialVocabulary signature
      (.function [leftSort, rightSort] order 0)
      (bindOrder (bindOrder order leftSort) rightSort))
    (leftUniversal : signature.Universal leftSort order)
    (rightUniversal : signature.Universal rightSort
      (bindOrder order leftSort))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [leftSort, rightSort] order) :
    ClaimReading signature real where
  printed := "⊢ : (∃f) : φ(x,y) .≡ₓ,ᵧ. f!(x,y)  Pp."
  parsed := .assertion (star_12_11_formula existential leftUniversal
    rightUniversal negation disjunction phi)

end PM.RamifiedSyntax

-- PM-CONTEXT-LOCAL Principia/Syntax/Printed.lean
namespace PM

structure PrintedFormula where
  source : String
  deriving DecidableEq, Repr

def pmPrinted (source : String) : PrintedFormula := ⟨source⟩

structure ElementaryReading (Γ : RealContext) where
  printed : PrintedFormula
  parsed : Elementary Γ
  scopeReading : String
  deriving Repr

end PM

-- PM-CONTEXT-LOCAL Principia/Deduction/Star2Ramified.lean
namespace PM.RamifiedSyntax

section

variable {signature : Signature} {real : Context} {order : Nat}
variable (negation : signature.Negation order)
variable (disjunction : signature.Disjunction order)

local prefix:max "∼ᵣ" => Formula.neg negation
local infixr:55 " ∨ᵣ " => sameDisjunction disjunction
local infixr:54 " ⊃ᵣ " => implication negation disjunction

private theorem detach {p q : Formula signature real [] order} :
    (⊢ᵣ p) → (⊢ᵣ (p ⊃ᵣ q)) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons realSort real => exact Derivation.star_1_11_same negation disjunction

theorem star_2_01 (p : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ ∼ᵣ p) ⊃ᵣ ∼ᵣ p) :=
  Derivation.star_1_2 negation disjunction (∼ᵣ p)

theorem star_2_02 (p q : Formula signature real [] order) :
    ⊢ᵣ (q ⊃ᵣ (p ⊃ᵣ q)) :=
  Derivation.star_1_3_same negation disjunction (∼ᵣ p) q

theorem star_2_03 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ ∼ᵣ q) ⊃ᵣ (q ⊃ᵣ ∼ᵣ p)) :=
  Derivation.star_1_4_same negation disjunction (∼ᵣ p) (∼ᵣ q)

theorem star_2_04 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ (q ⊃ᵣ (p ⊃ᵣ r))) :=
  Derivation.star_1_5_same negation disjunction (∼ᵣ p) (∼ᵣ q) r

class Star2_05Reading
    {vocabularyOrder pOrder qOrder rOrder : Nat}
    {formulaOrder : outParam Nat}
    (negation : signature.Negation vocabularyOrder)
    (disjunction : signature.Disjunction vocabularyOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (formula : outParam (Formula signature real [] formulaOrder)) where
  pNegated : Formula signature real [] pOrder
  pNegation : signature.Negation pOrder
  pNegationDefinition :
    ImplicationNegation signature real pNegation p pNegated
  primitiveQNegation : signature.Negation qOrder
  primitiveQRDisjunction : signature.Disjunction (max qOrder rOrder)
  primitiveOuterNegation : signature.Negation (max qOrder rOrder)
  primitiveConsequenceNegation : signature.Negation (max pOrder qOrder)
  primitivePQDisjunction : signature.Disjunction (max pOrder qOrder)
  primitivePRDisjunction : signature.Disjunction (max pOrder rOrder)
  primitiveConsequenceDisjunction : signature.Disjunction
    (max (max pOrder qOrder) (max pOrder rOrder))
  primitiveOuterDisjunction : signature.Disjunction
    (max (max qOrder rOrder)
      (max (max pOrder qOrder) (max pOrder rOrder)))
  sumReading : Star1_6Reading primitiveQNegation primitiveQRDisjunction
    primitiveOuterNegation primitiveConsequenceNegation
    primitivePQDisjunction primitivePRDisjunction
    primitiveConsequenceDisjunction primitiveOuterDisjunction
    pNegated q r formula

instance star2_05SameReading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Star2_05Reading negation disjunction p q r
      (implication negation disjunction
        (implication negation disjunction q r)
        (implication negation disjunction
          (implication negation disjunction p q)
          (implication negation disjunction p r))) := by
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
      disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation (natMaxSelf order).symm) negation
  let consequenceEquality := natMaxCongr (natMaxSelf order) (natMaxSelf order)
  let consequenceDisjunction :=
    Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      disjunction
  let resultEquality := natMaxCongr (natMaxSelf order) consequenceEquality
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEquality.symm) disjunction
  refine {
    pNegated := .neg negation p
    pNegation := negation
    pNegationDefinition := .star_1_01 negation p
    primitiveQNegation := negation
    primitiveQRDisjunction := pairDisjunction
    primitiveOuterNegation := pairNegation
    primitiveConsequenceNegation := pairNegation
    primitivePQDisjunction := pairDisjunction
    primitivePRDisjunction := pairDisjunction
    primitiveConsequenceDisjunction := consequenceDisjunction
    primitiveOuterDisjunction := outerDisjunction
    sumReading := ?_
  }
  exact {
    qrFormulaOrder := order
    pqFormulaOrder := order
    prFormulaOrder := order
    consequenceFormulaOrder := order
    qNegated := .neg negation q
    qrFormula := implication negation disjunction q r
    pqFormula := implication negation disjunction p q
    prFormula := implication negation disjunction p r
    consequenceNegated := .neg negation
      (implication negation disjunction p q)
    consequenceFormula := implication negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction p r)
    qrNegated := .neg negation (implication negation disjunction q r)
    consequenceNegation := negation
    outerNegation := negation
    qNegationDefinition := .star_1_01 negation q
    qrDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation q) r
    pqDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation p) q
    prDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation p) r
    consequenceNegationDefinition := .star_1_01 negation
      (implication negation disjunction p q)
    consequenceDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation (implication negation disjunction p q))
      (implication negation disjunction p r)
    outerNegationDefinition := .star_1_01 negation
      (implication negation disjunction q r)
    outerDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation (implication negation disjunction q r))
      (implication negation disjunction
        (implication negation disjunction p q)
        (implication negation disjunction p r))
  }

@[reducible] def star2_05ReadingOfSameOrderComponents
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r pNegated qNegated pqFormula qrFormula prFormula :
      Formula signature real [] order)
    (pNegationDefinition :
      ImplicationNegation signature real negation p pNegated)
    (qNegationDefinition :
      ImplicationNegation signature real negation q qNegated)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula) :
    Star2_05Reading negation disjunction p q r
      (implication negation disjunction qrFormula
        (implication negation disjunction pqFormula prFormula)) := by
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
      disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation (natMaxSelf order).symm) negation
  let consequenceEquality := natMaxCongr (natMaxSelf order) (natMaxSelf order)
  let consequenceDisjunction :=
    Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      disjunction
  let resultEquality := natMaxCongr (natMaxSelf order) consequenceEquality
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEquality.symm) disjunction
  refine {
    pNegated := pNegated
    pNegation := negation
    pNegationDefinition := pNegationDefinition
    primitiveQNegation := negation
    primitiveQRDisjunction := pairDisjunction
    primitiveOuterNegation := pairNegation
    primitiveConsequenceNegation := pairNegation
    primitivePQDisjunction := pairDisjunction
    primitivePRDisjunction := pairDisjunction
    primitiveConsequenceDisjunction := consequenceDisjunction
    primitiveOuterDisjunction := outerDisjunction
    sumReading := ?_
  }
  exact {
    qrFormulaOrder := order
    pqFormulaOrder := order
    prFormulaOrder := order
    consequenceFormulaOrder := order
    qNegated := qNegated
    qrFormula := qrFormula
    pqFormula := pqFormula
    prFormula := prFormula
    consequenceNegated := .neg negation pqFormula
    consequenceFormula := implication negation disjunction pqFormula prFormula
    qrNegated := .neg negation qrFormula
    consequenceNegation := negation
    outerNegation := negation
    qNegationDefinition := qNegationDefinition
    qrDisjunctionDefinition := qrDisjunctionDefinition
    pqDisjunctionDefinition := pqDisjunctionDefinition
    prDisjunctionDefinition := prDisjunctionDefinition
    consequenceNegationDefinition := .star_1_01 negation pqFormula
    consequenceDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation pqFormula) prFormula
    outerNegationDefinition := .star_1_01 negation qrFormula
    outerDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation qrFormula)
      (implication negation disjunction pqFormula prFormula)
  }

theorem star_2_05
    {pOrder qOrder rOrder formulaOrder : Nat}
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    {formula : Formula signature real [] formulaOrder}
    [reading : Star2_05Reading negation disjunction p q r formula] :
    ⊢ᵣ formula := by
  exact Derivation.star_1_6 reading.primitiveQNegation
    reading.primitiveQRDisjunction reading.primitiveOuterNegation
    reading.primitiveConsequenceNegation reading.primitivePQDisjunction
    reading.primitivePRDisjunction reading.primitiveConsequenceDisjunction
    reading.primitiveOuterDisjunction reading.pNegated q r
    (reading := reading.sumReading)

example {signature : Signature} {real : Context}
    (universal : signature.Universal .individual 1)
    (negation : signature.Negation 1)
    (disjunction : signature.Disjunction 1)
    (p q : Formula signature real [] 1)
    (body : Formula signature real [.individual] 1)
    (hQR : ⊢ᵣ star_9_04 universal disjunction (.neg negation q) body)
    (hPQ : ⊢ᵣ implication negation disjunction p q) :
    ⊢ᵣ star_9_04 universal disjunction (.neg negation p) body := by
  let r : Formula signature real [] 1 := .always universal body
  let pNegated : Formula signature real [] 1 := .neg negation p
  let qNegated : Formula signature real [] 1 := .neg negation q
  let pqFormula : Formula signature real [] 1 :=
    implication negation disjunction p q
  let qrFormula : Formula signature real [] 1 :=
    star_9_04 universal disjunction qNegated body
  let prFormula : Formula signature real [] 1 :=
    star_9_04 universal disjunction pNegated body
  have pNegationDefinition :
      ImplicationNegation signature real negation p pNegated :=
    ImplicationNegation.star_1_01 negation p
  have qNegationDefinition :
      ImplicationNegation signature real negation q qNegated :=
    ImplicationNegation.star_1_01 negation q
  have pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula :=
    ImplicationDisjunction.star_1_01_same disjunction pNegated q
  have qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula := by
    apply ImplicationDisjunction.star_9_04 universal universal
    exact ImplicationDisjunction.star_1_01_same disjunction
      (qNegated.rename (fun v => .succ v)) body
  have prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula := by
    apply ImplicationDisjunction.star_9_04 universal universal
    exact ImplicationDisjunction.star_1_01_same disjunction
      (pNegated.rename (fun v => .succ v)) body
  let syllReading := star2_05ReadingOfSameOrderComponents
    negation disjunction p q r pNegated qNegated pqFormula qrFormula prFormula
    pNegationDefinition qNegationDefinition pqDisjunctionDefinition
    qrDisjunctionDefinition prDisjunctionDefinition
  have syll := star_2_05 negation disjunction p q r
    (reading := syllReading)
  have line1 := detach negation disjunction hQR syll
  exact Derivation.star_9_12_same negation disjunction hPQ line1

theorem star_2_06 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((q ⊃ᵣ r) ⊃ᵣ (p ⊃ᵣ r))) :=
  detach negation disjunction (star_2_05 negation disjunction p q r)
    (star_2_04 negation disjunction (q ⊃ᵣ r) (p ⊃ᵣ q) (p ⊃ᵣ r))

theorem star_2_07 (p : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ (p ∨ᵣ p)) :=
  Derivation.star_1_3_same negation disjunction p p

theorem star_2_08 (p : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ p) :=
  detach negation disjunction (star_2_07 negation disjunction p)
    (detach negation disjunction
      (Derivation.star_1_2 negation disjunction p)
      (star_2_05 negation disjunction p (p ∨ᵣ p) p))

theorem star_2_1 (p : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ∨ᵣ p) :=
  star_2_08 negation disjunction p

theorem star_2_11 (p : Formula signature real [] order) :
    ⊢ᵣ (p ∨ᵣ ∼ᵣ p) :=
  detach negation disjunction (star_2_1 negation disjunction p)
    (Derivation.star_1_4_same negation disjunction (∼ᵣ p) p)

theorem star_2_12 (p : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ ∼ᵣ (∼ᵣ p)) :=
  star_2_11 negation disjunction (∼ᵣ p)

theorem star_2_13 (p : Formula signature real [] order) :
    ⊢ᵣ (p ∨ᵣ ∼ᵣ (∼ᵣ (∼ᵣ p))) := by
  have line1 := Derivation.star_1_6_same negation disjunction p (∼ᵣ p)
    (∼ᵣ (∼ᵣ (∼ᵣ p)))
  have line2 := detach negation disjunction
    (star_2_12 negation disjunction (∼ᵣ p)) line1
  exact detach negation disjunction (star_2_11 negation disjunction p) line2

theorem star_2_14 (p : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (∼ᵣ p) ⊃ᵣ p) := by
  have line1 := Derivation.star_1_4_same negation disjunction p
    (∼ᵣ (∼ᵣ (∼ᵣ p)))
  exact detach negation disjunction (star_2_13 negation disjunction p) line1

theorem star_2_15 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ (∼ᵣ q ⊃ᵣ p)) := by
  have line1 := star_2_05 negation disjunction (∼ᵣ p) q (∼ᵣ (∼ᵣ q))
  have line2 := star_2_12 negation disjunction q
  have line3 := detach negation disjunction line2 line1
  have line4 := star_2_03 negation disjunction (∼ᵣ p) (∼ᵣ q)
  have line5 := star_2_05 negation disjunction (∼ᵣ q) (∼ᵣ (∼ᵣ p)) p
  have line6 := detach negation disjunction (star_2_14 negation disjunction p) line5
  have line7 := star_2_05 negation disjunction (∼ᵣ p ⊃ᵣ q)
    (∼ᵣ p ⊃ᵣ ∼ᵣ (∼ᵣ q)) (∼ᵣ q ⊃ᵣ ∼ᵣ (∼ᵣ p))
  have line8 := detach negation disjunction line4 line7
  have line9 := detach negation disjunction line3 line8
  have line10 := star_2_05 negation disjunction (∼ᵣ p ⊃ᵣ q)
    (∼ᵣ q ⊃ᵣ ∼ᵣ (∼ᵣ p)) (∼ᵣ q ⊃ᵣ p)
  have line11 := detach negation disjunction line6 line10
  exact detach negation disjunction line9 line11

theorem star_2_16 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ (∼ᵣ q ⊃ᵣ ∼ᵣ p)) := by
  have line1 := detach negation disjunction (star_2_12 negation disjunction q)
    (star_2_05 negation disjunction p q (∼ᵣ (∼ᵣ q)))
  have line2 := star_2_03 negation disjunction p (∼ᵣ q)
  have syll := detach negation disjunction line1
    (star_2_06 negation disjunction (p ⊃ᵣ q)
      (p ⊃ᵣ ∼ᵣ (∼ᵣ q)) (∼ᵣ q ⊃ᵣ ∼ᵣ p))
  exact detach negation disjunction line2 syll

theorem star_2_17 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ q ⊃ᵣ ∼ᵣ p) ⊃ᵣ (p ⊃ᵣ q)) := by
  have line1 := star_2_03 negation disjunction (∼ᵣ q) p
  have line2 := detach negation disjunction (star_2_14 negation disjunction q)
    (star_2_05 negation disjunction p (∼ᵣ (∼ᵣ q)) q)
  have syll := detach negation disjunction line1
    (star_2_06 negation disjunction (∼ᵣ q ⊃ᵣ ∼ᵣ p)
      (p ⊃ᵣ ∼ᵣ (∼ᵣ q)) (p ⊃ᵣ q))
  exact detach negation disjunction line2 syll

theorem star_2_18 (p : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ p) ⊃ᵣ p) := by
  have line1 := detach negation disjunction (star_2_12 negation disjunction p)
    (star_2_05 negation disjunction (∼ᵣ p) p (∼ᵣ (∼ᵣ p)))
  have line2 := star_2_01 negation disjunction (∼ᵣ p)
  have syll1 := detach negation disjunction line1
    (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ p)
      (∼ᵣ p ⊃ᵣ ∼ᵣ (∼ᵣ p)) (∼ᵣ (∼ᵣ p)))
  have line3 := detach negation disjunction line2 syll1
  have line4 := star_2_14 negation disjunction p
  have syll2 := detach negation disjunction line3
    (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ p) (∼ᵣ (∼ᵣ p)) p)
  exact detach negation disjunction line4 syll2

theorem star_2_2 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ (p ∨ᵣ q)) := by
  have line1 := Derivation.star_1_3_same negation disjunction q p
  have line2 := Derivation.star_1_4_same negation disjunction q p
  exact detach negation disjunction line1
    (detach negation disjunction line2
      (star_2_05 negation disjunction p (q ∨ᵣ p) (p ∨ᵣ q)))

theorem star_2_21 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ⊃ᵣ (p ⊃ᵣ q)) :=
  star_2_2 negation disjunction (∼ᵣ p) q

theorem star_2_24 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := by
  have comm := star_2_04 negation disjunction (∼ᵣ p) p q
  exact detach negation disjunction (star_2_21 negation disjunction p q) comm

theorem star_2_25 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ∨ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := by
  have line1 : ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ∨ᵣ (p ∨ᵣ q)) := star_2_1 negation disjunction (p ∨ᵣ q)
  have assoc := Derivation.star_1_5_same negation disjunction (∼ᵣ (p ∨ᵣ q)) p q
  exact detach negation disjunction line1 assoc

theorem star_2_26 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ∨ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) :=
  star_2_25 negation disjunction (∼ᵣ p) q

theorem star_2_27 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) :=
  star_2_26 negation disjunction p q

theorem star_2_3 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ r)) ⊃ᵣ (p ∨ᵣ (r ∨ᵣ q))) :=
  detach negation disjunction
    (Derivation.star_1_4_same negation disjunction q r)
    (Derivation.star_1_6_same negation disjunction p (q ∨ᵣ r) (r ∨ᵣ q))

theorem star_2_31 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ r)) :=
  detach negation disjunction
    (detach negation disjunction
      (star_2_3 negation disjunction p q r)
      (detach negation disjunction
        (Derivation.star_1_5_same negation disjunction p r q)
        (star_2_05 negation disjunction (p ∨ᵣ (q ∨ᵣ r)) (p ∨ᵣ (r ∨ᵣ q)) (r ∨ᵣ (p ∨ᵣ q)))))
    (detach negation disjunction
      (Derivation.star_1_4_same negation disjunction r (p ∨ᵣ q))
      (star_2_05 negation disjunction (p ∨ᵣ (q ∨ᵣ r)) (r ∨ᵣ (p ∨ᵣ q)) ((p ∨ᵣ q) ∨ᵣ r)))

theorem star_2_32 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ r))) :=
  detach negation disjunction
    (detach negation disjunction
      (Derivation.star_1_4_same negation disjunction (p ∨ᵣ q) r)
      (detach negation disjunction
        (Derivation.star_1_5_same negation disjunction r p q)
        (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (r ∨ᵣ (p ∨ᵣ q)) (p ∨ᵣ (r ∨ᵣ q)))))
    (detach negation disjunction
      (star_2_3 negation disjunction p r q)
      (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (p ∨ᵣ (r ∨ᵣ q)) (p ∨ᵣ (q ∨ᵣ r))))

def star_2_33 (p q r : Formula signature real [] order) :
    Formula signature real [] order :=
  (p ∨ᵣ q) ∨ᵣ r

theorem star_2_33_unfold (p q r : Formula signature real [] order) :
    star_2_33 disjunction p q r = ((p ∨ᵣ q) ∨ᵣ r) := rfl

theorem star_2_36 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p))) := by
  have perm : ⊢ᵣ ((p ∨ᵣ r) ⊃ᵣ (r ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p r
  have syll : ⊢ᵣ (((p ∨ᵣ r) ⊃ᵣ (r ∨ᵣ p)) ⊃ᵣ
      (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p)))) :=
    star_2_05 negation disjunction (p ∨ᵣ q) (p ∨ᵣ r) (r ∨ᵣ p)
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p))) :=
    detach negation disjunction perm syll
  have line2 : ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    Derivation.star_1_6_same negation disjunction p q r
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_05 negation disjunction (q ⊃ᵣ r) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p))))

theorem star_2_37 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))) := by
  have permIn : ⊢ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ q)) := Derivation.star_1_4_same negation disjunction q p
  have syll : ⊢ᵣ (((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ q)) ⊃ᵣ
      (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r)))) :=
    star_2_06 negation disjunction (q ∨ᵣ p) (p ∨ᵣ q) (p ∨ᵣ r)
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction permIn syll
  have sumStep : ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    Derivation.star_1_6_same negation disjunction p q r
  exact detach negation disjunction sumStep
    (detach negation disjunction line1
      (star_2_05 negation disjunction (q ⊃ᵣ r) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))))

theorem star_2_38 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))) := by
  have permIn : ⊢ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ q)) := Derivation.star_1_4_same negation disjunction q p
  have permOut : ⊢ᵣ ((p ∨ᵣ r) ⊃ᵣ (r ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p r
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction permIn (star_2_06 negation disjunction (q ∨ᵣ p) (p ∨ᵣ q) (p ∨ᵣ r))
  have line2 : ⊢ᵣ (((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))) :=
    detach negation disjunction permOut (star_2_05 negation disjunction (q ∨ᵣ p) (p ∨ᵣ r) (r ∨ᵣ p))
  have line3 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))) :=
    detach negation disjunction line2
      (detach negation disjunction line1
        (star_2_06 negation disjunction ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))))
  have sumStep : ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    Derivation.star_1_6_same negation disjunction p q r
  exact detach negation disjunction sumStep
    (detach negation disjunction line3
      (star_2_05 negation disjunction (q ⊃ᵣ r) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))))

theorem star_2_41 (p q : Formula signature real [] order) :
    ⊢ᵣ ((q ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ q)) := by
  have assoc : ⊢ᵣ ((q ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ q))) := Derivation.star_1_5_same negation disjunction q p q
  have taut : ⊢ᵣ ((q ∨ᵣ q) ⊃ᵣ q) := Derivation.star_1_2 negation disjunction q
  have line2 : ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ q)) :=
    detach negation disjunction taut (Derivation.star_1_6_same negation disjunction p (q ∨ᵣ q) q)
  exact detach negation disjunction assoc
    (detach negation disjunction line2
      (star_2_05 negation disjunction (q ∨ᵣ (p ∨ᵣ q)) (p ∨ᵣ (q ∨ᵣ q)) (p ∨ᵣ q)))

theorem star_2_4 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ q)) := by
  have assoc : ⊢ᵣ ((p ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ ((p ∨ᵣ p) ∨ᵣ q)) := star_2_31 negation disjunction p p q
  have taut : ⊢ᵣ ((p ∨ᵣ p) ⊃ᵣ p) := Derivation.star_1_2 negation disjunction p
  have lifted : ⊢ᵣ (((p ∨ᵣ p) ∨ᵣ q) ⊃ᵣ (p ∨ᵣ q)) :=
    detach negation disjunction taut (star_2_38 negation disjunction q (p ∨ᵣ p) p)
  exact detach negation disjunction assoc
    (detach negation disjunction lifted
      (star_2_05 negation disjunction (p ∨ᵣ (p ∨ᵣ q)) ((p ∨ᵣ p) ∨ᵣ q) (p ∨ᵣ q)))

theorem star_2_42 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ∨ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ q)) :=
  star_2_4 negation disjunction (∼ᵣ p) q

theorem star_2_43 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ q)) :=
  star_2_42 negation disjunction p q

theorem star_2_45 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ ∼ᵣ p) := by
  exact detach negation disjunction (star_2_2 negation disjunction p q) (star_2_16 negation disjunction p (p ∨ᵣ q))

theorem star_2_46 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ ∼ᵣ q) := by
  exact detach negation disjunction (Derivation.star_1_3_same negation disjunction p q)
    (star_2_16 negation disjunction q (p ∨ᵣ q))

theorem star_2_47 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ (∼ᵣ p ∨ᵣ q)) := by
  exact detach negation disjunction (star_2_45 negation disjunction p q)
    (detach negation disjunction (star_2_2 negation disjunction (∼ᵣ p) q)
      (star_2_05 negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ p) (∼ᵣ p ∨ᵣ q)))

theorem star_2_48 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ ∼ᵣ q)) := by
  exact detach negation disjunction (star_2_46 negation disjunction p q)
    (detach negation disjunction (Derivation.star_1_3_same negation disjunction p (∼ᵣ q))
      (star_2_05 negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ q) (p ∨ᵣ ∼ᵣ q)))

theorem star_2_49 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ (∼ᵣ p ∨ᵣ ∼ᵣ q)) := by
  exact detach negation disjunction (star_2_45 negation disjunction p q)
    (detach negation disjunction (star_2_2 negation disjunction (∼ᵣ p) (∼ᵣ q))
      (star_2_05 negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ p) (∼ᵣ p ∨ᵣ ∼ᵣ q)))

theorem star_2_5 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := by
  exact star_2_47 negation disjunction (∼ᵣ p) q

theorem star_2_51 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ ∼ᵣ q)) := by
  exact star_2_48 negation disjunction (∼ᵣ p) q

theorem star_2_52 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ ∼ᵣ q)) := by
  exact star_2_49 negation disjunction (∼ᵣ p) q

theorem star_2_521 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (q ⊃ᵣ p)) := by
  have line1 : ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ ∼ᵣ q)) :=
    star_2_52 negation disjunction p q
  have line2 : ⊢ᵣ ((∼ᵣ p ⊃ᵣ ∼ᵣ q) ⊃ᵣ (q ⊃ᵣ p)) :=
    star_2_17 negation disjunction q p
  have syll := star_2_05 negation disjunction
    (∼ᵣ (p ⊃ᵣ q)) (∼ᵣ p ⊃ᵣ ∼ᵣ q) (q ⊃ᵣ p)
  exact detach negation disjunction line1
    (detach negation disjunction line2 syll)

theorem star_2_53 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := by
  have lift : ⊢ᵣ ((p ⊃ᵣ ∼ᵣ (∼ᵣ p)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (∼ᵣ (∼ᵣ p) ∨ᵣ q))) :=
    star_2_38 negation disjunction q p (∼ᵣ (∼ᵣ p))
  exact detach negation disjunction (star_2_12 negation disjunction p) lift

theorem star_2_54 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ (p ∨ᵣ q)) := by
  have lift : ⊢ᵣ ((∼ᵣ (∼ᵣ p) ⊃ᵣ p) ⊃ᵣ ((∼ᵣ (∼ᵣ p) ∨ᵣ q) ⊃ᵣ (p ∨ᵣ q))) :=
    star_2_38 negation disjunction q (∼ᵣ (∼ᵣ p)) p
  exact detach negation disjunction (star_2_14 negation disjunction p) lift

theorem star_2_55 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_53 negation disjunction p q) (star_2_04 negation disjunction (p ∨ᵣ q) (∼ᵣ p) q)

theorem star_2_56 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ q ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ p)) := by
  have inst : ⊢ᵣ (∼ᵣ q ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ p)) := star_2_55 negation disjunction q p
  have perm : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p q
  have syll : ⊢ᵣ (((q ∨ᵣ p) ⊃ᵣ p) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ p)) :=
    detach negation disjunction perm (star_2_06 negation disjunction (p ∨ᵣ q) (q ∨ᵣ p) p)
  have lift : ⊢ᵣ ((∼ᵣ q ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ p)) ⊃ᵣ (∼ᵣ q ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ p))) :=
    detach negation disjunction syll
      (star_2_05 negation disjunction (∼ᵣ q) ((q ∨ᵣ p) ⊃ᵣ p) ((p ∨ᵣ q) ⊃ᵣ p))
  exact detach negation disjunction inst lift

theorem star_2_6 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) := by
  have line1 : ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ ((∼ᵣ p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ q))) :=
    star_2_38 negation disjunction q (∼ᵣ p) q
  have line2 : ⊢ᵣ (((∼ᵣ p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ q)) ⊃ᵣ ((∼ᵣ p ∨ᵣ q) ⊃ᵣ q)) :=
    detach negation disjunction (Derivation.star_1_2 negation disjunction q)
      (star_2_05 negation disjunction (∼ᵣ p ∨ᵣ q) (q ∨ᵣ q) q)
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ q) ((∼ᵣ p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ q)) ((∼ᵣ p ∨ᵣ q) ⊃ᵣ q)))

theorem star_2_61 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_6 negation disjunction p q)
    (star_2_04 negation disjunction (∼ᵣ p ⊃ᵣ q) (p ⊃ᵣ q) q)

theorem star_2_62 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_6 negation disjunction p q)
    (detach negation disjunction (star_2_53 negation disjunction p q)
      (star_2_06 negation disjunction (p ∨ᵣ q) (∼ᵣ p ⊃ᵣ q) ((p ⊃ᵣ q) ⊃ᵣ q)))

theorem star_2_621 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_62 negation disjunction p q)
    (star_2_04 negation disjunction (p ∨ᵣ q) (p ⊃ᵣ q) q)

theorem star_2_63 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((∼ᵣ p ∨ᵣ q) ⊃ᵣ q)) := by

  exact star_2_62 negation disjunction p q

theorem star_2_64 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ ∼ᵣ q) ⊃ᵣ p)) := by

  have s : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((∼ᵣ q ∨ᵣ p) ⊃ᵣ p)) :=
    detach negation disjunction (star_2_63 negation disjunction q p)
      (detach negation disjunction (Derivation.star_1_4_same negation disjunction p q)
        (star_2_06 negation disjunction (p ∨ᵣ q) (q ∨ᵣ p) ((∼ᵣ q ∨ᵣ p) ⊃ᵣ p)))

  have t : ⊢ᵣ (((∼ᵣ q ∨ᵣ p) ⊃ᵣ p) ⊃ᵣ ((p ∨ᵣ ∼ᵣ q) ⊃ᵣ p)) :=
    detach negation disjunction (Derivation.star_1_4_same negation disjunction p (∼ᵣ q))
      (star_2_06 negation disjunction (p ∨ᵣ ∼ᵣ q) (∼ᵣ q ∨ᵣ p) p)
  exact detach negation disjunction t
    (detach negation disjunction s
      (star_2_06 negation disjunction (p ∨ᵣ q) ((∼ᵣ q ∨ᵣ p) ⊃ᵣ p) ((p ∨ᵣ ∼ᵣ q) ⊃ᵣ p)))

theorem star_2_65 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((p ⊃ᵣ ∼ᵣ q) ⊃ᵣ ∼ᵣ p)) := by

  exact star_2_64 negation disjunction (∼ᵣ p) q

theorem star_2_67 (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ q)) := by

  have line1 : ⊢ᵣ ((((p ∨ᵣ q) ⊃ᵣ q)) ⊃ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q)) :=
    detach negation disjunction (star_2_54 negation disjunction p q)
      (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ q) (p ∨ᵣ q) q)
  have line2 : ⊢ᵣ (((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ q)) :=
    detach negation disjunction (star_2_24 negation disjunction p q)
      (star_2_06 negation disjunction p (∼ᵣ p ⊃ᵣ q) q)
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_06 negation disjunction ((p ∨ᵣ q) ⊃ᵣ q) ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q) (p ⊃ᵣ q)))

theorem star_2_68 (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ (p ∨ᵣ q)) := by

  have inst : ⊢ᵣ ((((∼ᵣ p) ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := star_2_67 negation disjunction (∼ᵣ p) q
  exact detach negation disjunction (star_2_54 negation disjunction p q)
    (detach negation disjunction inst
      (star_2_06 negation disjunction ((p ⊃ᵣ q) ⊃ᵣ q) (∼ᵣ p ⊃ᵣ q) (p ∨ᵣ q)))

theorem star_2_69 (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ ((q ⊃ᵣ p) ⊃ᵣ p)) := by

  have perm : ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ (q ∨ᵣ p)) :=
    detach negation disjunction (Derivation.star_1_4_same negation disjunction p q)
      (detach negation disjunction (star_2_68 negation disjunction p q)
        (star_2_06 negation disjunction ((p ⊃ᵣ q) ⊃ᵣ q) (p ∨ᵣ q) (q ∨ᵣ p)))
  exact detach negation disjunction (star_2_62 negation disjunction q p)
    (detach negation disjunction perm
      (star_2_06 negation disjunction ((p ⊃ᵣ q) ⊃ᵣ q) (q ∨ᵣ p) ((q ⊃ᵣ p) ⊃ᵣ p)))

theorem star_2_73 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))) := by
  have first : ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := star_2_621 negation disjunction p q
  have second : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))) :=
    star_2_38 negation disjunction r (p ∨ᵣ q) q
  have syll :
      ⊢ᵣ ((((p ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))) ⊃ᵣ
          (((p ⊃ᵣ q) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) ⊃ᵣ
            ((p ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))))) :=
    Derivation.star_1_6_same negation disjunction (∼ᵣ (p ⊃ᵣ q)) ((p ∨ᵣ q) ⊃ᵣ q)
      (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))
  exact detach negation disjunction first (detach negation disjunction second syll)

theorem star_2_74 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ p) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) := by
  have line1 := star_2_73 negation disjunction q p r
  have line2 := star_2_32 negation disjunction p q r
  have line3 := Derivation.star_1_5_same negation disjunction p q r
  have line4 := star_2_31 negation disjunction q p r
  have line5 := detach negation disjunction line2
    (detach negation disjunction line3
      (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (p ∨ᵣ (q ∨ᵣ r)) (q ∨ᵣ (p ∨ᵣ r))))
  have line6 := detach negation disjunction line5
    (detach negation disjunction line4
      (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (q ∨ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ∨ᵣ r)))
  have line7 :
      ⊢ᵣ ((((q ∨ᵣ p) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction line6
      (star_2_06 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) ((q ∨ᵣ p) ∨ᵣ r) (p ∨ᵣ r))
  have line8 := detach negation disjunction line1
    (detach negation disjunction line7
      (star_2_05 negation disjunction (q ⊃ᵣ p) (((q ∨ᵣ p) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))
        (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))))
  exact line8

theorem star_2_75 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ (p ∨ᵣ r))) := by
  have perm : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p q
  have fromDisj : ⊢ᵣ ((q ∨ᵣ p) ⊃ᵣ (∼ᵣ q ⊃ᵣ p)) := star_2_53 negation disjunction q p
  have hyp : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (∼ᵣ q ⊃ᵣ p)) :=
    detach negation disjunction perm
      (detach negation disjunction fromDisj
        (Derivation.star_1_6_same negation disjunction (∼ᵣ (p ∨ᵣ q)) (q ∨ᵣ p) (∼ᵣ q ⊃ᵣ p)))
  have shifted :
      ⊢ᵣ ((∼ᵣ q ⊃ᵣ p) ⊃ᵣ (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) :=
    star_2_74 negation disjunction p (∼ᵣ q) r
  have curried :
      ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction hyp
      (detach negation disjunction shifted
        (Derivation.star_1_6_same negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ q ⊃ᵣ p)
          (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))))
  have commuted :
      ⊢ᵣ (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction curried
      (Derivation.star_1_5_same negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ ((p ∨ᵣ ∼ᵣ q) ∨ᵣ r)) (p ∨ᵣ r))
  have assoc : ⊢ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∨ᵣ ∼ᵣ q) ∨ᵣ r)) :=
    star_2_31 negation disjunction p (∼ᵣ q) r
  have joined :
      ⊢ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction assoc
      (detach negation disjunction commuted
        (Derivation.star_1_6_same negation disjunction (∼ᵣ (p ∨ᵣ (q ⊃ᵣ r))) ((p ∨ᵣ ∼ᵣ q) ∨ᵣ r)
          ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))))
  exact detach negation disjunction joined
    (Derivation.star_1_5_same negation disjunction (∼ᵣ (p ∨ᵣ (q ⊃ᵣ r))) (∼ᵣ (p ∨ᵣ q)) (p ∨ᵣ r))

theorem star_2_76 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) := by
  exact detach negation disjunction (star_2_75 negation disjunction p q r)
    (star_2_04 negation disjunction (p ∨ᵣ q) (p ∨ᵣ (q ⊃ᵣ r)) (p ∨ᵣ r))

theorem star_2_77 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ r))) := by
  exact star_2_76 negation disjunction (∼ᵣ p) q r

theorem star_2_8 (q r s : Formula signature real [] order) :
    ⊢ᵣ ((q ∨ᵣ r) ⊃ᵣ ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s))) := by
  have perm : ⊢ᵣ ((q ∨ᵣ r) ⊃ᵣ (r ∨ᵣ q)) :=
    Derivation.star_1_4_same negation disjunction q r
  have permFlipped : ⊢ᵣ ((r ∨ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) :=
    detach negation disjunction perm
      (Derivation.star_1_4_same negation disjunction (∼ᵣ (q ∨ᵣ r)) (r ∨ᵣ q))
  have fiftyThree : ⊢ᵣ ((r ∨ᵣ q) ⊃ᵣ (∼ᵣ r ⊃ᵣ q)) := star_2_53 negation disjunction r q
  have sumFiftyThree :
      ⊢ᵣ (((r ∨ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) ⊃ᵣ ((∼ᵣ r ⊃ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r))) :=
    detach negation disjunction fiftyThree
      (star_2_38 negation disjunction (∼ᵣ (q ∨ᵣ r)) (r ∨ᵣ q) (∼ᵣ r ⊃ᵣ q))
  have line1 : ⊢ᵣ ((∼ᵣ r ⊃ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) :=
    detach negation disjunction permFlipped sumFiftyThree
  have line2 : ⊢ᵣ ((∼ᵣ r ⊃ᵣ q) ⊃ᵣ ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s))) :=
    star_2_38 negation disjunction s (∼ᵣ r) q
  have sumLine2 :
      ⊢ᵣ (((∼ᵣ r ⊃ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) ⊃ᵣ
        (((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)) ∨ᵣ ∼ᵣ (q ∨ᵣ r))) :=
    detach negation disjunction line2
      (star_2_38 negation disjunction (∼ᵣ (q ∨ᵣ r)) (∼ᵣ r ⊃ᵣ q) ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)))
  have line3 : ⊢ᵣ (((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) :=
    detach negation disjunction line1 sumLine2
  exact detach negation disjunction line3
    (Derivation.star_1_4_same negation disjunction
      ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)) (∼ᵣ (q ∨ᵣ r)))

theorem star_2_81 (p q r s : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ (r ⊃ᵣ s)) ⊃ᵣ
      ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))) := by
  have line1 :
      ⊢ᵣ ((q ⊃ᵣ (r ⊃ᵣ s)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ (r ⊃ᵣ s)))) :=
    Derivation.star_1_6_same negation disjunction p q (r ⊃ᵣ s)
  have line2 :
      ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ (r ⊃ᵣ s))) ⊃ᵣ
        ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))) :=
    detach negation disjunction (star_2_76 negation disjunction p r s)
      (star_2_05 negation disjunction (p ∨ᵣ q) (p ∨ᵣ (r ⊃ᵣ s)) ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_06 negation disjunction (q ⊃ᵣ (r ⊃ᵣ s)) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ (r ⊃ᵣ s)))
        ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))))

theorem star_2_82 (p q r s : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ s))) := by
  have compose : ∀ A B C : Formula signature real [] order, (⊢ᵣ (A ⊃ᵣ B)) →
      (⊢ᵣ (B ⊃ᵣ C)) → (⊢ᵣ (A ⊃ᵣ C)) := by
    intro A B C h₁ h₂
    exact detach negation disjunction h₁
      (detach negation disjunction h₂ (star_2_05 negation disjunction A B C))
  have printed :
      ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ r)) ⊃ᵣ
        ((p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ s)))) :=
    detach negation disjunction (star_2_8 negation disjunction q r s)
      (star_2_81 negation disjunction p (q ∨ᵣ r) (∼ᵣ r ∨ᵣ s) (q ∨ᵣ s))
  have antecedent : ⊢ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ r))) :=
    star_2_32 negation disjunction p q r
  have innerAntecedent :
      ⊢ᵣ (((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ (p ∨ᵣ (∼ᵣ r ∨ᵣ s))) :=
    star_2_32 negation disjunction p (∼ᵣ r) s
  have conclusion : ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ s)) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ s)) :=
    star_2_31 negation disjunction p q s
  have inner :
      ⊢ᵣ (((p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ s))) ⊃ᵣ
        (((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ s))) :=
    compose _ _ _
      (detach negation disjunction innerAntecedent
        (star_2_06 negation disjunction ((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) (p ∨ᵣ (∼ᵣ r ∨ᵣ s)) (p ∨ᵣ (q ∨ᵣ s))))
      (detach negation disjunction conclusion
        (star_2_05 negation disjunction ((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) (p ∨ᵣ (q ∨ᵣ s)) ((p ∨ᵣ q) ∨ᵣ s)))
  exact compose _ _ _ (compose _ _ _ antecedent printed) inner

theorem star_2_83 (p q r s : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ
      ((p ⊃ᵣ (r ⊃ᵣ s)) ⊃ᵣ (p ⊃ᵣ (q ⊃ᵣ s)))) := by
  have compose : ∀ A B C : Formula signature real [] order, (⊢ᵣ (A ⊃ᵣ B)) →
      (⊢ᵣ (B ⊃ᵣ C)) → (⊢ᵣ (A ⊃ᵣ C)) := by
    intro A B C h₁ h₂
    exact detach negation disjunction h₁
      (detach negation disjunction h₂ (star_2_05 negation disjunction A B C))
  have printed :
      ⊢ᵣ (((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ
        (((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s))) :=
    star_2_82 negation disjunction (∼ᵣ p) (∼ᵣ q) r s
  have antecedent :
      ⊢ᵣ ((∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ r)) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ r)) :=
    star_2_31 negation disjunction (∼ᵣ p) (∼ᵣ q) r
  have innerAntecedent :
      ⊢ᵣ ((∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s)) :=
    star_2_31 negation disjunction (∼ᵣ p) (∼ᵣ r) s
  have conclusion :
      ⊢ᵣ (((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s) ⊃ᵣ (∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ s))) :=
    star_2_32 negation disjunction (∼ᵣ p) (∼ᵣ q) s
  have inner :
      ⊢ᵣ ((((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s)) ⊃ᵣ
        ((∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ (∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ s)))) :=
    compose _ _ _
      (detach negation disjunction innerAntecedent
        (star_2_06 negation disjunction (∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s)
          ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s)))
      (detach negation disjunction conclusion
        (star_2_05 negation disjunction (∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s)
          (∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ s))))
  exact compose _ _ _ (compose _ _ _ antecedent printed) inner

theorem star_2_85 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (p ∨ᵣ (q ⊃ᵣ r))) := by
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ r) ⊃ᵣ (q ⊃ᵣ r)) :=
    detach negation disjunction (Derivation.star_1_3_same negation disjunction p q) (star_2_06 negation disjunction q (p ∨ᵣ q) r)
  have fiftyFive : ⊢ᵣ (∼ᵣ p ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ r)) := star_2_55 negation disjunction p r
  have syll :
      ⊢ᵣ (((p ∨ᵣ r) ⊃ᵣ r) ⊃ᵣ
        (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ r))) :=
    star_2_05 negation disjunction (p ∨ᵣ q) (p ∨ᵣ r) r
  have half :
      ⊢ᵣ (∼ᵣ p ⊃ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ r))) :=
    detach negation disjunction syll
      (detach negation disjunction fiftyFive
        (star_2_06 negation disjunction (∼ᵣ p) ((p ∨ᵣ r) ⊃ᵣ r)
          (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ r))))
  have line1' : ⊢ᵣ (∼ᵣ p ⊃ᵣ (((p ∨ᵣ q) ⊃ᵣ r) ⊃ᵣ (q ⊃ᵣ r))) :=
    detach negation disjunction line1
      (Derivation.star_1_3_same negation disjunction (∼ᵣ (∼ᵣ p)) (((p ∨ᵣ q) ⊃ᵣ r) ⊃ᵣ (q ⊃ᵣ r)))
  have line2 :
      ⊢ᵣ (∼ᵣ p ⊃ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (q ⊃ᵣ r))) :=
    detach negation disjunction line1'
      (detach negation disjunction half
        (star_2_83 negation disjunction (∼ᵣ p) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((p ∨ᵣ q) ⊃ᵣ r) (q ⊃ᵣ r)))
  have commuted :
      ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (∼ᵣ p ⊃ᵣ (q ⊃ᵣ r))) :=
    detach negation disjunction line2
      (star_2_04 negation disjunction (∼ᵣ p) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) (q ⊃ᵣ r))
  exact detach negation disjunction (star_2_54 negation disjunction p (q ⊃ᵣ r))
    (detach negation disjunction commuted
      (star_2_06 negation disjunction ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) (∼ᵣ p ⊃ᵣ (q ⊃ᵣ r))
        (p ∨ᵣ (q ⊃ᵣ r))))

theorem star_2_86 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ (q ⊃ᵣ r))) :=
  star_2_85 negation disjunction (∼ᵣ p) q r

end

namespace MixedOrder

structure NegationVocabulary (signature : Signature) (support : Type) where
  order : support → Nat
  meaning : ∀ item, signature.Negation (order item)

structure DisjunctionVocabulary (signature : Signature) (support : Type)
    (combine : support → support → support)
    (negation : NegationVocabulary signature support) where
  orderEquality : ∀ left right,
    max (negation.order left) (negation.order right) =
      negation.order (combine left right)
  meaning : ∀ left right,
    signature.Disjunction (negation.order (combine left right))

def normalizedDisjunction
    (equality : max leftOrder rightOrder = resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real [] leftOrder)
    (right : Formula signature real [] rightOrder) :
    Formula signature real [] resultOrder :=
  Eq.mp (congrArg (Formula signature real []) equality)
    (.disj
      (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
      left right)

theorem derive_star_1_2
    (selfEquality : max order order = order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ normalizedDisjunction selfEquality disjunction
      (.neg negation (normalizedDisjunction selfEquality disjunction p p)) p := by
  exact Derivation.castAssertion (by rfl)
    (Derivation.star_1_2 negation disjunction p)

theorem derive_star_1_3
    (innerEquality : max pOrder qOrder = innerOrder)
    (outerEquality : max qOrder innerOrder = outerOrder)
    (qNegation : signature.Negation qOrder)
    (innerDisjunction : signature.Disjunction innerOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg qNegation q)
      (normalizedDisjunction innerEquality innerDisjunction p q) := by
  cases innerEquality
  cases outerEquality
  exact Derivation.star_1_3 qNegation innerDisjunction outerDisjunction p q

theorem derive_star_1_4
    (leftEquality : max pOrder qOrder = leftOrder)
    (rightEquality : max qOrder pOrder = rightOrder)
    (outerEquality : max leftOrder rightOrder = outerOrder)
    (leftNegation : signature.Negation leftOrder)
    (leftDisjunction : signature.Disjunction leftOrder)
    (rightDisjunction : signature.Disjunction rightOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg leftNegation
        (normalizedDisjunction leftEquality leftDisjunction p q))
      (normalizedDisjunction rightEquality rightDisjunction q p) := by
  cases leftEquality
  cases rightEquality
  cases outerEquality
  exact Derivation.star_1_4 leftNegation leftDisjunction rightDisjunction
    outerDisjunction p q

theorem derive_star_1_5
    (qrEquality : max qOrder rOrder = qrOrder)
    (leftEquality : max pOrder qrOrder = leftOrder)
    (prEquality : max pOrder rOrder = prOrder)
    (rightEquality : max qOrder prOrder = rightOrder)
    (outerEquality : max leftOrder rightOrder = outerOrder)
    (leftNegation : signature.Negation leftOrder)
    (qrDisjunction : signature.Disjunction qrOrder)
    (leftDisjunction : signature.Disjunction leftOrder)
    (prDisjunction : signature.Disjunction prOrder)
    (rightDisjunction : signature.Disjunction rightOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg leftNegation
        (normalizedDisjunction leftEquality leftDisjunction p
          (normalizedDisjunction qrEquality qrDisjunction q r)))
      (normalizedDisjunction rightEquality rightDisjunction q
        (normalizedDisjunction prEquality prDisjunction p r)) := by
  cases qrEquality
  cases leftEquality
  cases prEquality
  cases rightEquality
  cases outerEquality
  exact Derivation.star_1_5 leftNegation qrDisjunction leftDisjunction
    prDisjunction rightDisjunction outerDisjunction p q r

theorem derive_star_1_6
    (qrEquality : max qOrder rOrder = qrOrder)
    (pqEquality : max pOrder qOrder = pqOrder)
    (prEquality : max pOrder rOrder = prOrder)
    (consequentEquality : max pqOrder prOrder = consequentOrder)
    (outerEquality : max qrOrder consequentOrder = outerOrder)
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction qrOrder)
    (qrNegation : signature.Negation qrOrder)
    (pqNegation : signature.Negation pqOrder)
    (pqDisjunction : signature.Disjunction pqOrder)
    (prDisjunction : signature.Disjunction prOrder)
    (consequentDisjunction : signature.Disjunction consequentOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg qrNegation
        (normalizedDisjunction qrEquality qrDisjunction
          (.neg qNegation q) r))
      (normalizedDisjunction consequentEquality consequentDisjunction
        (.neg pqNegation
          (normalizedDisjunction pqEquality pqDisjunction p q))
        (normalizedDisjunction prEquality prDisjunction p r)) := by
  cases qrEquality
  cases pqEquality
  cases prEquality
  cases consequentEquality
  cases outerEquality
  exact Derivation.star_1_6 qNegation qrDisjunction qrNegation pqNegation
    pqDisjunction prDisjunction consequentDisjunction outerDisjunction p q r

theorem detach
    (equality : max pOrder qOrder = resultOrder)
    (pNegation : signature.Negation pOrder)
    (disjunction : signature.Disjunction resultOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (line1 : ⊢ᵣ p)
    (line2 : ⊢ᵣ normalizedDisjunction equality disjunction
      (.neg pNegation p) q) : ⊢ᵣ q := by
  cases real with
  | nil =>
      cases equality
      exact Derivation.star_1_1 pNegation disjunction line1 line2
  | cons realSort real =>
      cases equality
      exact Derivation.star_1_11 pNegation disjunction line1 line2

def elementarySupport
    (combine : support → support → support)
    (constantSupport : String → support)
    (valuationSupport : PM.RealVar Γ .elementaryProposition → support) :
    PM.Elementary Γ → support
  | .constant name => constantSupport name
  | .var v => valuationSupport v
  | .neg proposition =>
      elementarySupport combine constantSupport valuationSupport proposition
  | .disj left right =>
      combine
        (elementarySupport combine constantSupport valuationSupport left)
        (elementarySupport combine constantSupport valuationSupport right)

def interpret
    (combine : support → support → support)
    (negation : NegationVocabulary signature support)
    (disjunction : DisjunctionVocabulary signature support combine negation)
    (constantSupport : String → support)
    (constantMeaning : ∀ name,
      Formula signature real [] (negation.order (constantSupport name)))
    (valuationSupport : PM.RealVar Γ .elementaryProposition → support)
    (valuation : ∀ v,
      Formula signature real [] (negation.order (valuationSupport v))) :
    (proposition : PM.Elementary Γ) →
      Formula signature real []
        (negation.order
          (elementarySupport combine constantSupport valuationSupport proposition))
  | .constant name => constantMeaning name
  | .var v => valuation v
  | .neg proposition =>
      .neg
        (negation.meaning
          (elementarySupport combine constantSupport valuationSupport proposition))
        (interpret combine negation disjunction constantSupport constantMeaning
          valuationSupport valuation proposition)
  | .disj left right =>
      normalizedDisjunction
        (disjunction.orderEquality
          (elementarySupport combine constantSupport valuationSupport left)
          (elementarySupport combine constantSupport valuationSupport right))
        (disjunction.meaning
          (elementarySupport combine constantSupport valuationSupport left)
          (elementarySupport combine constantSupport valuationSupport right))
        (interpret combine negation disjunction constantSupport constantMeaning
          valuationSupport valuation left)
        (interpret combine negation disjunction constantSupport constantMeaning
          valuationSupport valuation right)

theorem transport
    (combine : support → support → support)
    (negation : NegationVocabulary signature support)
    (disjunction : DisjunctionVocabulary signature support combine negation)
    (tautology : ∀ item
      (p : Formula signature real [] (negation.order item)),
      ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality (combine item item) item)
        (disjunction.meaning (combine item item) item)
        (.neg (negation.meaning (combine item item))
          (normalizedDisjunction (disjunction.orderEquality item item)
            (disjunction.meaning item item) p p)) p)
    (constantSupport : String → support)
    (constantMeaning : ∀ name,
      Formula signature real [] (negation.order (constantSupport name)))
    (valuationSupport : PM.RealVar Γ .elementaryProposition → support)
    (valuation : ∀ v,
      Formula signature real [] (negation.order (valuationSupport v)))
    {proposition : PM.Elementary Γ} (proof : PM.Derivation proposition) :
    ⊢ᵣ interpret combine negation disjunction constantSupport constantMeaning
      valuationSupport valuation proposition := by
  induction proof with
  | @star_1_1 p q hp hpq ihp ihpq =>
      let pSupport := elementarySupport combine constantSupport valuationSupport p
      let qSupport := elementarySupport combine constantSupport valuationSupport q
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation p
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation q
      have hp' := ihp valuationSupport valuation
      have hpq' := ihpq valuationSupport valuation
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality pSupport qSupport)
        (disjunction.meaning pSupport qSupport)
        (.neg (negation.meaning pSupport) pFormula) qFormula at hpq'
      exact detach (disjunction.orderEquality pSupport qSupport)
        (negation.meaning pSupport) (disjunction.meaning pSupport qSupport)
        pFormula qFormula hp' hpq'
  | @star_1_11 context p q _ hp hpq ihp ihpq =>
      let pSupport := elementarySupport combine constantSupport valuationSupport p
      let qSupport := elementarySupport combine constantSupport valuationSupport q
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation p
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation q
      have hp' := ihp valuationSupport valuation
      have hpq' := ihpq valuationSupport valuation
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality pSupport qSupport)
        (disjunction.meaning pSupport qSupport)
        (.neg (negation.meaning pSupport) pFormula) qFormula at hpq'
      exact detach (disjunction.orderEquality pSupport qSupport)
        (negation.meaning pSupport) (disjunction.meaning pSupport qSupport)
        pFormula qFormula hp' hpq'
  | star_1_2 proposition =>
      let item := elementarySupport combine constantSupport valuationSupport proposition
      let interpreted := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation proposition
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality (combine item item) item)
        (disjunction.meaning (combine item item) item)
        (.neg (negation.meaning (combine item item))
          (normalizedDisjunction (disjunction.orderEquality item item)
            (disjunction.meaning item item) interpreted interpreted)) interpreted
      exact tautology item interpreted
  | star_1_3 left right =>
      let leftSupport := elementarySupport combine constantSupport
        valuationSupport left
      let rightSupport := elementarySupport combine constantSupport
        valuationSupport right
      let leftFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let rightFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality rightSupport
          (combine leftSupport rightSupport))
        (disjunction.meaning rightSupport (combine leftSupport rightSupport))
        (.neg (negation.meaning rightSupport) rightFormula)
        (normalizedDisjunction
          (disjunction.orderEquality leftSupport rightSupport)
          (disjunction.meaning leftSupport rightSupport)
          leftFormula rightFormula)
      exact derive_star_1_3
        (disjunction.orderEquality leftSupport rightSupport)
        (disjunction.orderEquality rightSupport (combine leftSupport rightSupport))
        _ _ _ _ _
  | star_1_4 left right =>
      let leftSupport := elementarySupport combine constantSupport
        valuationSupport left
      let rightSupport := elementarySupport combine constantSupport
        valuationSupport right
      let leftFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let rightFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      let forwardSupport := combine leftSupport rightSupport
      let reverseSupport := combine rightSupport leftSupport
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality forwardSupport reverseSupport)
        (disjunction.meaning forwardSupport reverseSupport)
        (.neg (negation.meaning forwardSupport)
          (normalizedDisjunction
            (disjunction.orderEquality leftSupport rightSupport)
            (disjunction.meaning leftSupport rightSupport)
            leftFormula rightFormula))
        (normalizedDisjunction
          (disjunction.orderEquality rightSupport leftSupport)
          (disjunction.meaning rightSupport leftSupport)
          rightFormula leftFormula)
      exact derive_star_1_4
        (disjunction.orderEquality leftSupport rightSupport)
        (disjunction.orderEquality rightSupport leftSupport)
        (disjunction.orderEquality forwardSupport reverseSupport)
        _ _ _ _ _ _
  | star_1_5 left middle right =>
      let pSupport := elementarySupport combine constantSupport valuationSupport left
      let qSupport := elementarySupport combine constantSupport valuationSupport middle
      let rSupport := elementarySupport combine constantSupport valuationSupport right
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation middle
      let rFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      let qrSupport := combine qSupport rSupport
      let leftSideSupport := combine pSupport qrSupport
      let prSupport := combine pSupport rSupport
      let rightSideSupport := combine qSupport prSupport
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality leftSideSupport rightSideSupport)
        (disjunction.meaning leftSideSupport rightSideSupport)
        (.neg (negation.meaning leftSideSupport)
          (normalizedDisjunction
            (disjunction.orderEquality pSupport qrSupport)
            (disjunction.meaning pSupport qrSupport) pFormula
            (normalizedDisjunction
              (disjunction.orderEquality qSupport rSupport)
              (disjunction.meaning qSupport rSupport) qFormula rFormula)))
        (normalizedDisjunction
          (disjunction.orderEquality qSupport prSupport)
          (disjunction.meaning qSupport prSupport) qFormula
          (normalizedDisjunction
            (disjunction.orderEquality pSupport rSupport)
            (disjunction.meaning pSupport rSupport) pFormula rFormula))
      exact derive_star_1_5
        (disjunction.orderEquality qSupport rSupport)
        (disjunction.orderEquality pSupport qrSupport)
        (disjunction.orderEquality pSupport rSupport)
        (disjunction.orderEquality qSupport prSupport)
        (disjunction.orderEquality leftSideSupport rightSideSupport)
        _ _ _ _ _ _ _ _ _
  | star_1_6 left middle right =>
      let pSupport := elementarySupport combine constantSupport valuationSupport left
      let qSupport := elementarySupport combine constantSupport valuationSupport middle
      let rSupport := elementarySupport combine constantSupport valuationSupport right
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation middle
      let rFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      let qrSupport := combine qSupport rSupport
      let pqSupport := combine pSupport qSupport
      let prSupport := combine pSupport rSupport
      let consequentSupport := combine pqSupport prSupport
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality qrSupport consequentSupport)
        (disjunction.meaning qrSupport consequentSupport)
        (.neg (negation.meaning qrSupport)
          (normalizedDisjunction
            (disjunction.orderEquality qSupport rSupport)
            (disjunction.meaning qSupport rSupport)
            (.neg (negation.meaning qSupport) qFormula) rFormula))
        (normalizedDisjunction
          (disjunction.orderEquality pqSupport prSupport)
          (disjunction.meaning pqSupport prSupport)
          (.neg (negation.meaning pqSupport)
            (normalizedDisjunction
              (disjunction.orderEquality pSupport qSupport)
              (disjunction.meaning pSupport qSupport) pFormula qFormula))
          (normalizedDisjunction
            (disjunction.orderEquality pSupport rSupport)
            (disjunction.meaning pSupport rSupport) pFormula rFormula))
      exact derive_star_1_6
        (disjunction.orderEquality qSupport rSupport)
        (disjunction.orderEquality pSupport qSupport)
        (disjunction.orderEquality pSupport rSupport)
        (disjunction.orderEquality pqSupport prSupport)
        (disjunction.orderEquality qrSupport consequentSupport)
        _ _ _ _ _ _ _ _ _ _ _

private theorem maxZeroRight : ∀ order : Nat, max order 0 = order
  | 0 => rfl
  | Nat.succ _ => rfl

private theorem succLeSucc {left right : Nat} :
    left ≤ right → left.succ ≤ right.succ :=
  fun proof => Nat.le.rec
    (motive := fun right _ => left.succ ≤ right.succ)
    Nat.le.refl (fun _ induction => Nat.le.step induction) proof

private theorem predLePred {left right : Nat} (proof : left ≤ right) :
    left.pred ≤ right.pred := by
  induction proof with
  | refl => exact Nat.le.refl
  | @step right proof induction =>
      cases right with
      | zero => exact induction
      | succ right => exact Nat.le.step induction

private theorem leOfSuccLeSucc {left right : Nat}
    (proof : left.succ ≤ right.succ) : left ≤ right :=
  predLePred proof

private theorem maxSuccSucc (left right : Nat) :
    max left.succ right.succ = (max left right).succ := by
  unfold Max.max Nat.instMax maxOfLe
  change (if left.succ ≤ right.succ then right.succ else left.succ) =
    (if left ≤ right then right else left).succ
  by_cases ordering : left ≤ right
  · rw [if_pos ordering, if_pos (succLeSucc ordering)]
  · rw [if_neg ordering]
    have successorOrdering : ¬ left.succ ≤ right.succ :=
      fun proof => ordering (leOfSuccLeSucc proof)
    rw [if_neg successorOrdering]

theorem maxAssoc : ∀ left middle right : Nat,
    max (max left middle) right = max left (max middle right)
  | 0, middle, right => rfl
  | Nat.succ left, 0, right => rfl
  | Nat.succ left, Nat.succ middle, 0 =>
      Eq.trans (maxZeroRight (max left.succ middle.succ))
        (congrArg (max left.succ) (maxZeroRight middle.succ).symm)
  | Nat.succ left, Nat.succ middle, Nat.succ right => by
      rw [maxSuccSucc, maxSuccSucc, maxSuccSucc, maxSuccSucc]
      exact congrArg Nat.succ (maxAssoc left middle right)

theorem maxComm : ∀ left right : Nat, max left right = max right left
  | 0, 0 => rfl
  | 0, Nat.succ right => rfl
  | Nat.succ left, 0 => rfl
  | Nat.succ left, Nat.succ right => by
      rw [maxSuccSucc, maxSuccSucc]
      exact congrArg Nat.succ (maxComm left right)

theorem maxLeftAbsorb (left right : Nat) :
    max left (max left right) = max left right := by
  rw [← maxAssoc, natMaxSelf]

theorem maxRightAbsorb (left right : Nat) :
    max (max left right) right = max left right := by
  rw [maxAssoc, natMaxSelf]

theorem maxRightLeftAbsorb (left right : Nat) :
    max right (max left right) = max left right := by
  rw [maxComm right, maxRightAbsorb]

theorem maxLeftRightAbsorb (left right : Nat) :
    max (max left right) left = max left right := by
  rw [maxComm (max left right) left, maxLeftAbsorb]

inductive BinarySupport where
  | left
  | right
  | both

def BinarySupport.combine : BinarySupport → BinarySupport → BinarySupport
  | .left, .left => .left
  | .left, .right => .both
  | .left, .both => .both
  | .right, .left => .both
  | .right, .right => .right
  | .right, .both => .both
  | .both, .left => .both
  | .both, .right => .both
  | .both, .both => .both

structure BinaryNegations (signature : Signature) where
  leftOrder : Nat
  rightOrder : Nat
  left : signature.Negation leftOrder
  right : signature.Negation rightOrder
  both : signature.Negation (max leftOrder rightOrder)

structure BinaryDisjunctions (signature : Signature)
    (negation : BinaryNegations signature) where
  left : signature.Disjunction negation.leftOrder
  right : signature.Disjunction negation.rightOrder
  both : signature.Disjunction (max negation.leftOrder negation.rightOrder)

def BinaryNegations.order (negation : BinaryNegations signature) :
    BinarySupport → Nat
  | .left => negation.leftOrder
  | .right => negation.rightOrder
  | .both => max negation.leftOrder negation.rightOrder

def BinaryNegations.meaning (negation : BinaryNegations signature) :
    ∀ item, signature.Negation (negation.order item)
  | .left => negation.left
  | .right => negation.right
  | .both => negation.both

def BinaryDisjunctions.meaning
    (disjunction : BinaryDisjunctions signature negation) :
    ∀ item, signature.Disjunction (negation.order item)
  | .left => disjunction.left
  | .right => disjunction.right
  | .both => disjunction.both

theorem binaryOrderCombine
    (negation : BinaryNegations signature)
    (leftSupport rightSupport : BinarySupport) :
    max (negation.order leftSupport) (negation.order rightSupport) =
      negation.order (leftSupport.combine rightSupport) := by
  cases leftSupport <;> cases rightSupport
  · exact natMaxSelf negation.leftOrder
  · rfl
  · exact maxLeftAbsorb negation.leftOrder negation.rightOrder
  · exact maxComm negation.rightOrder negation.leftOrder
  · exact natMaxSelf negation.rightOrder
  · exact maxRightLeftAbsorb negation.leftOrder negation.rightOrder
  · exact maxLeftRightAbsorb negation.leftOrder negation.rightOrder
  · exact maxRightAbsorb negation.leftOrder negation.rightOrder
  · exact natMaxSelf (max negation.leftOrder negation.rightOrder)

def BinaryNegations.toVocabulary (negation : BinaryNegations signature) :
    NegationVocabulary signature BinarySupport where
  order := negation.order
  meaning := negation.meaning

def BinaryDisjunctions.toVocabulary
    (disjunction : BinaryDisjunctions signature negation) :
    DisjunctionVocabulary signature BinarySupport BinarySupport.combine
      negation.toVocabulary where
  orderEquality := binaryOrderCombine negation
  meaning := fun leftSupport rightSupport =>
    disjunction.meaning (leftSupport.combine rightSupport)

theorem binaryTautology
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (item : BinarySupport)
    (p : Formula signature real [] (negation.order item)) :
    ⊢ᵣ normalizedDisjunction
      (binaryOrderCombine negation (item.combine item) item)
      (disjunction.meaning ((item.combine item).combine item))
      (.neg (negation.meaning (item.combine item))
        (normalizedDisjunction (binaryOrderCombine negation item item)
          (disjunction.meaning (item.combine item)) p p)) p := by
  cases item
  · exact derive_star_1_2 (natMaxSelf negation.leftOrder)
      negation.left disjunction.left p
  · exact derive_star_1_2 (natMaxSelf negation.rightOrder)
      negation.right disjunction.right p
  · exact derive_star_1_2
      (natMaxSelf (max negation.leftOrder negation.rightOrder))
      negation.both disjunction.both p

def binaryConstantSupport (_ : String) : BinarySupport := .left

def binaryValuationSupport :
    PM.RealVar [.elementaryProposition, .elementaryProposition]
      .elementaryProposition → BinarySupport
  | .zero => .left
  | .succ .zero => .right

def binaryValuation
    (negation : BinaryNegations signature)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    ∀ v : PM.RealVar [.elementaryProposition, .elementaryProposition]
      .elementaryProposition,
      Formula signature real [] (negation.order (binaryValuationSupport v))
  | .zero => p
  | .succ .zero => q

def binaryInterpret
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    (proposition : PM.Elementary
      [.elementaryProposition, .elementaryProposition]) :
    Formula signature real []
      (negation.order (elementarySupport BinarySupport.combine
        binaryConstantSupport binaryValuationSupport proposition)) :=
  interpret BinarySupport.combine negation.toVocabulary disjunction.toVocabulary
    binaryConstantSupport (fun _ => p) binaryValuationSupport
    (binaryValuation negation p q) proposition

theorem binaryTransport
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    {proposition : PM.Elementary
      [.elementaryProposition, .elementaryProposition]}
    (proof : PM.Derivation proposition) :
    ⊢ᵣ binaryInterpret negation disjunction p q proposition :=
  transport BinarySupport.combine negation.toVocabulary disjunction.toVocabulary
    (binaryTautology negation disjunction) binaryConstantSupport (fun _ => p)
    binaryValuationSupport (binaryValuation negation p q) proof

def binaryP : PM.Elementary [.elementaryProposition, .elementaryProposition] :=
  .var .zero

def binaryQ : PM.Elementary [.elementaryProposition, .elementaryProposition] :=
  .var (.succ .zero)

theorem maxSwapLeft (left middle right : Nat) :
    max left (max middle right) = max middle (max left right) := by
  exact Eq.trans (maxAssoc left middle right).symm
    (Eq.trans (congrArg (fun order => max order right) (maxComm left middle))
      (maxAssoc middle left right))

theorem maxThirdPair (left middle right : Nat) :
    max right (max left middle) = max left (max middle right) := by
  exact Eq.trans (maxSwapLeft right left middle)
    (congrArg (max left) (maxComm right middle))

theorem maxPairsSameLeft (left middle right : Nat) :
    max (max left middle) (max left right) =
      max left (max middle right) := by
  rw [maxAssoc, maxSwapLeft middle left right, maxLeftAbsorb]

theorem maxPairsSharedMiddle (left middle right : Nat) :
    max (max left middle) (max middle right) =
      max left (max middle right) := by
  rw [maxAssoc, maxLeftAbsorb]

theorem maxPairsSharedRight (left middle right : Nat) :
    max (max left right) (max middle right) =
      max left (max middle right) := by
  rw [maxAssoc, maxRightLeftAbsorb]

theorem maxMiddleFull (left middle right : Nat) :
    max middle (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxSwapLeft middle left, maxLeftAbsorb]

theorem maxRightFull (left middle right : Nat) :
    max right (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxSwapLeft right left, maxSwapLeft right middle, natMaxSelf]

theorem maxPairLeftFull (left middle right : Nat) :
    max (max left middle) (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxPairsSameLeft, maxLeftAbsorb]

theorem maxPairRightFull (left middle right : Nat) :
    max (max left right) (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxPairsSameLeft, maxRightLeftAbsorb]

theorem maxPairMiddleFull (left middle right : Nat) :
    max (max middle right) (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxComm (max middle right), maxRightAbsorb]

inductive TernarySupport where
  | p
  | q
  | r
  | pq
  | pr
  | qr
  | pqr

def TernarySupport.combine : TernarySupport → TernarySupport → TernarySupport
  | .p, .p => .p
  | .p, .q => .pq
  | .p, .r => .pr
  | .p, .pq => .pq
  | .p, .pr => .pr
  | .p, .qr => .pqr
  | .p, .pqr => .pqr
  | .q, .p => .pq
  | .q, .q => .q
  | .q, .r => .qr
  | .q, .pq => .pq
  | .q, .pr => .pqr
  | .q, .qr => .qr
  | .q, .pqr => .pqr
  | .r, .p => .pr
  | .r, .q => .qr
  | .r, .r => .r
  | .r, .pq => .pqr
  | .r, .pr => .pr
  | .r, .qr => .qr
  | .r, .pqr => .pqr
  | .pq, .p => .pq
  | .pq, .q => .pq
  | .pq, .r => .pqr
  | .pq, .pq => .pq
  | .pq, .pr => .pqr
  | .pq, .qr => .pqr
  | .pq, .pqr => .pqr
  | .pr, .p => .pr
  | .pr, .q => .pqr
  | .pr, .r => .pr
  | .pr, .pq => .pqr
  | .pr, .pr => .pr
  | .pr, .qr => .pqr
  | .pr, .pqr => .pqr
  | .qr, .p => .pqr
  | .qr, .q => .qr
  | .qr, .r => .qr
  | .qr, .pq => .pqr
  | .qr, .pr => .pqr
  | .qr, .qr => .qr
  | .qr, .pqr => .pqr
  | .pqr, .p => .pqr
  | .pqr, .q => .pqr
  | .pqr, .r => .pqr
  | .pqr, .pq => .pqr
  | .pqr, .pr => .pqr
  | .pqr, .qr => .pqr
  | .pqr, .pqr => .pqr

structure TernaryNegations (signature : Signature) where
  pOrder : Nat
  qOrder : Nat
  rOrder : Nat
  p : signature.Negation pOrder
  q : signature.Negation qOrder
  r : signature.Negation rOrder
  pq : signature.Negation (max pOrder qOrder)
  pr : signature.Negation (max pOrder rOrder)
  qr : signature.Negation (max qOrder rOrder)
  pqr : signature.Negation (max pOrder (max qOrder rOrder))

structure TernaryDisjunctions (signature : Signature)
    (negation : TernaryNegations signature) where
  p : signature.Disjunction negation.pOrder
  q : signature.Disjunction negation.qOrder
  r : signature.Disjunction negation.rOrder
  pq : signature.Disjunction (max negation.pOrder negation.qOrder)
  pr : signature.Disjunction (max negation.pOrder negation.rOrder)
  qr : signature.Disjunction (max negation.qOrder negation.rOrder)
  pqr : signature.Disjunction
    (max negation.pOrder (max negation.qOrder negation.rOrder))

def TernaryNegations.order (negation : TernaryNegations signature) :
    TernarySupport → Nat
  | .p => negation.pOrder
  | .q => negation.qOrder
  | .r => negation.rOrder
  | .pq => max negation.pOrder negation.qOrder
  | .pr => max negation.pOrder negation.rOrder
  | .qr => max negation.qOrder negation.rOrder
  | .pqr => max negation.pOrder (max negation.qOrder negation.rOrder)

def TernaryNegations.meaning (negation : TernaryNegations signature) :
    ∀ item, signature.Negation (negation.order item)
  | .p => negation.p
  | .q => negation.q
  | .r => negation.r
  | .pq => negation.pq
  | .pr => negation.pr
  | .qr => negation.qr
  | .pqr => negation.pqr

def TernaryDisjunctions.meaning
    (disjunction : TernaryDisjunctions signature negation) :
    ∀ item, signature.Disjunction (negation.order item)
  | .p => disjunction.p
  | .q => disjunction.q
  | .r => disjunction.r
  | .pq => disjunction.pq
  | .pr => disjunction.pr
  | .qr => disjunction.qr
  | .pqr => disjunction.pqr

theorem ternaryOrderCombine
    (negation : TernaryNegations signature) (left right : TernarySupport) :
    max (negation.order left) (negation.order right) =
      negation.order (left.combine right) := by
  cases left <;> cases right
  · exact natMaxSelf negation.pOrder
  · rfl
  · rfl
  · exact maxLeftAbsorb negation.pOrder negation.qOrder
  · exact maxLeftAbsorb negation.pOrder negation.rOrder
  · rfl
  · exact maxLeftAbsorb negation.pOrder (max negation.qOrder negation.rOrder)
  · exact maxComm negation.qOrder negation.pOrder
  · exact natMaxSelf negation.qOrder
  · rfl
  · exact maxRightLeftAbsorb negation.pOrder negation.qOrder
  · exact maxSwapLeft negation.qOrder negation.pOrder negation.rOrder
  · exact maxLeftAbsorb negation.qOrder negation.rOrder
  · exact maxMiddleFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxComm negation.rOrder negation.pOrder
  · exact maxComm negation.rOrder negation.qOrder
  · exact natMaxSelf negation.rOrder
  · exact maxThirdPair negation.pOrder negation.qOrder negation.rOrder
  · exact maxRightLeftAbsorb negation.pOrder negation.rOrder
  · exact maxRightLeftAbsorb negation.qOrder negation.rOrder
  · exact maxRightFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxLeftRightAbsorb negation.pOrder negation.qOrder
  · exact maxRightAbsorb negation.pOrder negation.qOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder negation.qOrder) negation.rOrder)
      (maxThirdPair negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf (max negation.pOrder negation.qOrder)
  · exact maxPairsSameLeft negation.pOrder negation.qOrder negation.rOrder
  · exact maxPairsSharedMiddle negation.pOrder negation.qOrder negation.rOrder
  · exact maxPairLeftFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxLeftRightAbsorb negation.pOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder negation.rOrder) negation.qOrder)
      (maxSwapLeft negation.qOrder negation.pOrder negation.rOrder)
  · exact maxRightAbsorb negation.pOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder negation.rOrder)
        (max negation.pOrder negation.qOrder))
      (maxPairsSameLeft negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf (max negation.pOrder negation.rOrder)
  · exact maxPairsSharedRight negation.pOrder negation.qOrder negation.rOrder
  · exact maxPairRightFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxComm (max negation.qOrder negation.rOrder) negation.pOrder
  · exact maxLeftRightAbsorb negation.qOrder negation.rOrder
  · exact maxRightAbsorb negation.qOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.qOrder negation.rOrder)
        (max negation.pOrder negation.qOrder))
      (maxPairsSharedMiddle negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.qOrder negation.rOrder)
        (max negation.pOrder negation.rOrder))
      (maxPairsSharedRight negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf (max negation.qOrder negation.rOrder)
  · exact maxPairMiddleFull negation.pOrder negation.qOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        negation.pOrder)
      (maxLeftAbsorb negation.pOrder (max negation.qOrder negation.rOrder))
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        negation.qOrder)
      (maxMiddleFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        negation.rOrder)
      (maxRightFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        (max negation.pOrder negation.qOrder))
      (maxPairLeftFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        (max negation.pOrder negation.rOrder))
      (maxPairRightFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        (max negation.qOrder negation.rOrder))
      (maxPairMiddleFull negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf
      (max negation.pOrder (max negation.qOrder negation.rOrder))

def TernaryNegations.toVocabulary (negation : TernaryNegations signature) :
    NegationVocabulary signature TernarySupport where
  order := negation.order
  meaning := negation.meaning

def TernaryDisjunctions.toVocabulary
    (disjunction : TernaryDisjunctions signature negation) :
    DisjunctionVocabulary signature TernarySupport TernarySupport.combine
      negation.toVocabulary where
  orderEquality := ternaryOrderCombine negation
  meaning := fun left right => disjunction.meaning (left.combine right)

theorem ternaryTautology
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (item : TernarySupport)
    (formula : Formula signature real [] (negation.order item)) :
    ⊢ᵣ normalizedDisjunction
      (ternaryOrderCombine negation (item.combine item) item)
      (disjunction.meaning ((item.combine item).combine item))
      (.neg (negation.meaning (item.combine item))
        (normalizedDisjunction (ternaryOrderCombine negation item item)
          (disjunction.meaning (item.combine item)) formula formula)) formula := by
  cases item
  · exact derive_star_1_2 (natMaxSelf negation.pOrder)
      negation.p disjunction.p formula
  · exact derive_star_1_2 (natMaxSelf negation.qOrder)
      negation.q disjunction.q formula
  · exact derive_star_1_2 (natMaxSelf negation.rOrder)
      negation.r disjunction.r formula
  · exact derive_star_1_2 (natMaxSelf (max negation.pOrder negation.qOrder))
      negation.pq disjunction.pq formula
  · exact derive_star_1_2 (natMaxSelf (max negation.pOrder negation.rOrder))
      negation.pr disjunction.pr formula
  · exact derive_star_1_2 (natMaxSelf (max negation.qOrder negation.rOrder))
      negation.qr disjunction.qr formula
  · exact derive_star_1_2
      (natMaxSelf (max negation.pOrder (max negation.qOrder negation.rOrder)))
      negation.pqr disjunction.pqr formula

def ternaryConstantSupport (_ : String) : TernarySupport := .p

def ternaryValuationSupport :
    PM.RealVar [.elementaryProposition, .elementaryProposition,
      .elementaryProposition] .elementaryProposition → TernarySupport
  | .zero => .p
  | .succ .zero => .q
  | .succ (.succ .zero) => .r

def ternaryValuation
    (negation : TernaryNegations signature)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder) :
    ∀ v : PM.RealVar [.elementaryProposition, .elementaryProposition,
      .elementaryProposition] .elementaryProposition,
      Formula signature real [] (negation.order (ternaryValuationSupport v))
  | .zero => p
  | .succ .zero => q
  | .succ (.succ .zero) => r

def ternaryInterpret
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (proposition : PM.Elementary [.elementaryProposition,
      .elementaryProposition, .elementaryProposition]) :
    Formula signature real []
      (negation.order (elementarySupport TernarySupport.combine
        ternaryConstantSupport ternaryValuationSupport proposition)) :=
  interpret TernarySupport.combine negation.toVocabulary
    disjunction.toVocabulary ternaryConstantSupport (fun _ => p)
    ternaryValuationSupport (ternaryValuation negation p q r) proposition

theorem ternaryTransport
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    {proposition : PM.Elementary [.elementaryProposition,
      .elementaryProposition, .elementaryProposition]}
    (proof : PM.Derivation proposition) :
    ⊢ᵣ ternaryInterpret negation disjunction p q r proposition :=
  transport TernarySupport.combine negation.toVocabulary
    disjunction.toVocabulary (ternaryTautology negation disjunction)
    ternaryConstantSupport (fun _ => p) ternaryValuationSupport
    (ternaryValuation negation p q r) proof

def ternaryP : PM.Elementary [.elementaryProposition, .elementaryProposition,
    .elementaryProposition] := .var .zero

def ternaryQ : PM.Elementary [.elementaryProposition, .elementaryProposition,
    .elementaryProposition] := .var (.succ .zero)

def ternaryR : PM.Elementary [.elementaryProposition, .elementaryProposition,
    .elementaryProposition] := .var (.succ (.succ .zero))

end MixedOrder

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_2_01
#print axioms PM.RamifiedSyntax.star_2_02
#print axioms PM.RamifiedSyntax.star_2_03
#print axioms PM.RamifiedSyntax.star_2_04
#print axioms PM.RamifiedSyntax.star_2_05
#print axioms PM.RamifiedSyntax.star_2_06
#print axioms PM.RamifiedSyntax.star_2_08
#print axioms PM.RamifiedSyntax.star_2_15
#print axioms PM.RamifiedSyntax.star_2_16
#print axioms PM.RamifiedSyntax.star_2_17
#print axioms PM.RamifiedSyntax.star_2_21
#print axioms PM.RamifiedSyntax.star_2_33
#print axioms PM.RamifiedSyntax.star_2_33_unfold

-- PM-CONTEXT-LOCAL Principia/Deduction/Star9Derived.lean
namespace PM.RamifiedSyntax

structure Star9Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String := "The parsed field is the eliminable ramified AST of the diplomatic formula."

abbrev Star9Assertion
    (formula : Formula signature real [] order) :=
  Derivation (.assertion formula)

def star_9_1_reading
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:φx.⊃.(∃z).φz  Pp"
  parsed := .assertion (mixedImplication negation disjunction
    (body.instantiate value) (.sometimes existential body))

theorem star_9_1
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Derivation (.assertion (mixedImplication negation disjunction
      (body.instantiate value) (.sometimes existential body))) := by
  have line1 := Derivation.star_9_1 existential negation disjunction body value
  exact line1

def star_9_11_reading
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (x y : Term signature real [] argument) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:φx∨φy.⊃.(∃z).φz  Pp"
  parsed := .assertion (mixedImplication negation disjunction
    (sameDisjunction matrixDisjunction (body.instantiate x)
      (body.instantiate y))
    (.sometimes existential body))

theorem star_9_11
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (x y : Term signature real [] argument) :
    Derivation (.assertion (mixedImplication negation disjunction
      (sameDisjunction matrixDisjunction (body.instantiate x)
        (body.instantiate y))
      (.sometimes existential body))) := by
  have line1 := Derivation.star_9_11 existential negation matrixDisjunction
    disjunction body x y
  exact line1

def star_9_12_reading
    (q : Formula signature real [] rightOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "What is implied by a true premiss is true. Pp."
  parsed := .assertion q

theorem star_9_12
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (p : Formula signature real [] leftOrder)
    (q : Formula signature real [] rightOrder)
    (line1 : Star9Assertion p)
    (line2 : Star9Assertion
      (mixedImplication negation disjunction p q)) :
    Derivation (.assertion q) := by
  have line3 := Derivation.star_9_12 negation disjunction line1 line2
  exact line3

def star_9_13_reading
    (universal : signature.Universal argument matrixOrder)
    (body : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "In any assertion containing a real variable, this real variable may\nbe turned into an apparent variable of which all possible values are asserted\nto satisfy the function in question. Pp."
  parsed := .assertion (.always universal body)

theorem star_9_13
    (universal : signature.Universal argument matrixOrder)
    (body : Formula signature real [argument] matrixOrder)
    (line1 : Star9Assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument)))) :
    Derivation (.assertion (.always universal body)) := by
  have line2 := Derivation.star_9_13 universal body line1
  exact line2

def star_9_14_reading
    (body : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "✱9·14. If \" φ x \" is significant, then if x is of the same type as a , \" φ a \" is significant, and vice versa. Pp. (Cf. note on *10·121, p. 146.)"
  parsed := .significance body

theorem star_9_14
    (body : Formula signature real [argument] matrixOrder) :
    Derivation (.significance body) := by
  have line1 := Derivation.star_10_121 body
  exact line1

def star_9_15_reading
    (body : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "✱9·15. If, for some a , there is a proposition φ a , then there is a function φ x̂ , and vice versa. Pp."
  parsed := .functionExistence body

theorem star_9_15
    (body : Formula signature real [argument] matrixOrder) :
    Derivation (.functionExistence body) := by
  have line1 := Derivation.star_10_122 body
  exact line1

private theorem lift_star_1_3_left
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction q.weakenReal
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
          q.weakenReal) :=
    Derivation.star_1_3_same negation disjunction
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
      q.weakenReal
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))).weakenReal.instantiate value =
      implication negation disjunction q.weakenReal
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value) q.weakenReal) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      Formula.instantiate, implication_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (q.rename (fun v => .succ v))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_2
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction phi phi) phi) := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value)
          (phi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value) :=
    Derivation.star_1_2 negation disjunction
      (phi.weakenReal.instantiate value)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi phi) phi).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value)
          (phi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi phi) phi)
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_4
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument))))
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
          p.weakenReal) :=
    Derivation.star_1_4_same negation disjunction p.weakenReal
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      (sameDisjunction disjunction phi (p.rename (fun v => .succ v))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_5
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument))))) :=
    Derivation.star_1_5_same negation disjunction p.weakenReal q.weakenReal
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction q.weakenReal (phi.weakenReal.instantiate value)))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value))) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_4_reverse
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)) := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal)
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value)) :=
    Derivation.star_1_4_same negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal)
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private def star_9_3x_slotInner : Renaming [argument] [argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

private def star_9_3x_slotOuter : Renaming [argument] [argument, argument]
  | _, .zero => .succ .zero
  | _, .succ v => nomatch v

private def star_9_3x_slotThird : Renaming [argument]
    [argument, argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

def star_9_32_reading (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .q . ⊃ : (x).φx .∨. q"
  parsed := .assertion (star_9_04 universal matrixDisjunction
    (.neg matrixNegation q)
    (sameDisjunction matrixDisjunction phi (q.rename (fun v => .succ v))))
  scopeReading := "The outer implication and the member `(x).φx ∨ q` are both read through the scoped definitions ✱9·04 and ✱9·03; unfolding yields PM's generalized elementary matrix."

def star_9_34_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal : signature.Universal argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(x).φx .⊃ : p .∨. (x).φx"
  parsed := .assertion (star_9_08 existential universal disjunction
    (.neg negation (phi.rename star_9_3x_slotInner))
    (sameDisjunction disjunction
      (p.rename (fun v => .succ (.succ v)))
      (phi.rename star_9_3x_slotOuter)))
  scopeReading := "The antecedent negation is ✱9·01, the disjunction of its existential expansion with the universal consequent is ✱9·08, and `p ∨ (x).φx` is ✱9·04. The resulting AST is `(z)(∃x).∼φx ∨ (p ∨ φz)`."

def star_9_36_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal : signature.Universal argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .p .∨. (x).φx : ⊃ : (x).φx .∨. p"
  parsed := .assertion (star_9_08 existential universal disjunction
    (.neg negation (sameDisjunction disjunction
      (p.rename (fun v => .succ (.succ v)))
      (phi.rename star_9_3x_slotInner)))
    (sameDisjunction disjunction
      (phi.rename star_9_3x_slotOuter)
      (p.rename (fun v => .succ (.succ v)))))
  scopeReading := "The antecedent `p ∨ (x).φx` and consequent `(x).φx ∨ p` are read by ✱9·04 and ✱9·03; ✱9·01 and ✱9·08 give the two-binder scoped implication AST."

def star_9_361_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(x).φx .∨. p : ⊃ : p .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
    (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)))

theorem star_9_361 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_361_reading universal negation disjunction p phi).parsed := by
  exact lift_star_1_4_reverse universal negation disjunction p phi

def star_9_4_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p : ∨ : q .∨. (x).φx : .⊃ : .q : ∨ : p .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))))

theorem star_9_4 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_4_reading universal negation disjunction p q phi).parsed := by
  exact lift_star_1_5 universal negation disjunction p q phi

def star_9_2_reading
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (y : Term signature real [] argument) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:(x).φx.⊃.φy"
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal phi) (phi.instantiate y))

theorem star_9_2
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (y : Term signature real [] argument) :
    Derivation (star_9_2_reading universal negation disjunction phi y).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction phi y
  exact line1

def star_9_3_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(x).φx .∨. (x).φx : ⊃ . (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi phi) phi))

theorem star_9_3 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_3_reading universal negation disjunction phi).parsed := by
  exact lift_star_1_2 universal negation disjunction phi

def star_9_23_reading {matrixOrder : Nat}
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction (bindOrder matrixOrder argument))
    (phi : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:(x).φx.⊃.(x).φx       [Id.✱9·13·21]"
  parsed := .assertion (implication negation disjunction
    (.always universal phi) (.always universal phi))

theorem star_9_23 {matrixOrder : Nat}
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction (bindOrder matrixOrder argument))
    (phi : Formula signature real [argument] matrixOrder) :
    Derivation (star_9_23_reading universal negation disjunction phi).parsed := by
  have line1 := star_2_08 negation disjunction (.always universal phi)
  exact line1

def star_9_24_reading (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:(∃x).φx.⊃.(∃x).φx     [Id.✱9·13·22]"
  parsed := .assertion (implication negation disjunction
    (.sometimes existential phi) (.sometimes existential phi))

theorem star_9_24 (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_24_reading existential negation disjunction phi).parsed := by
  have line1 := star_2_08 negation disjunction (.sometimes existential phi)
  exact line1

def star_9_25_reading {fixedOrder matrixOrder : Nat}
    (universal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (negation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (disjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:.(x).p∨φx.⊃:p.∨.(x).φx   [Id.✱9·23.(✱9·04)]"
  parsed := .assertion (implication negation disjunction
    (.always universal (.disj matrixDisjunction
      (p.rename (fun v => .succ v)) phi))
    (star_9_04 universal matrixDisjunction p phi))

theorem star_9_25 {fixedOrder matrixOrder : Nat}
    (universal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (negation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (disjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Derivation (star_9_25_reading universal matrixDisjunction negation disjunction p phi).parsed := by
  have line1 := star_9_23 universal negation disjunction
    (.disj matrixDisjunction
      (p.rename (fun v => .succ v)) phi)
  have line2 :
      Derivation (.assertion (implication negation disjunction
        (.always universal (.disj matrixDisjunction
          (p.rename (fun v => .succ v)) phi))
        (star_9_04 universal matrixDisjunction p phi))) := by
    rw [star_9_04_unfold]
    exact line1
  exact line2

theorem star_9_32 (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (scopeNegation : signature.Negation (bindOrder 0 argument))
    (scopeDisjunction : signature.Disjunction (bindOrder 0 argument))
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_32_reading universal matrixNegation matrixDisjunction
      q phi).parsed := by
  have line1 := lift_star_1_3_left universal matrixNegation
    matrixDisjunction q phi
  have line2 : Derivation (.assertion (.always universal
      (sameDisjunction matrixDisjunction
        ((Formula.neg matrixNegation q).rename (fun v => .succ v))
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v)))))) := by
    change Derivation (.assertion (.always universal
      (implication matrixNegation matrixDisjunction
        (q.rename (fun v => .succ v))
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v))))))
    exact line1
  have line3 : Derivation (.assertion (implication scopeNegation scopeDisjunction
      (.always universal (sameDisjunction matrixDisjunction
        ((Formula.neg matrixNegation q).rename (fun v => .succ v))
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v)))))
      (star_9_04 universal matrixDisjunction (.neg matrixNegation q)
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v)))))) := by
    exact star_9_25 universal matrixDisjunction scopeNegation
      scopeDisjunction (.neg matrixNegation q)
      (sameDisjunction matrixDisjunction phi
        (q.rename (fun v => .succ v)))
  have line4 := Derivation.star_9_12_same scopeNegation scopeDisjunction
    line2 line3
  exact line4

def star_9_41_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p : ∨ : (x).φx .∨. r : .⊃ : .(x).φx : ∨ : p ∨ r"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))))

theorem star_9_41 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_41_reading universal negation disjunction p r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction p.weakenReal r.weakenReal)) :=
    Derivation.star_1_5_same negation disjunction p.weakenReal
      (phi.weakenReal.instantiate value) r.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
        (sameDisjunction disjunction phi
          (sameDisjunction disjunction (p.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction p.weakenReal r.weakenReal)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
      (sameDisjunction disjunction phi
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  change ⊢ᵣ .always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v)))))
  exact line2

def star_9_42_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : (x).φx : ∨ : q ∨ r : .⊃ : .q : ∨ : (x).φx .∨. r"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))))

theorem star_9_42 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_42_reading universal negation disjunction q r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction q.weakenReal r.weakenReal))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal)) :=
    Derivation.star_1_5_same negation disjunction
      (phi.weakenReal.instantiate value) q.weakenReal r.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi
          (sameDisjunction disjunction (q.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction phi
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction q.weakenReal r.weakenReal))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (r.rename (fun v => .succ v))))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  change ⊢ᵣ .always universal (implication negation disjunction
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
  exact line2

def star_9_51_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p .⊃. (x).φx : ⊃ : .p ∨ r .⊃ .⊃ : (x).φx .∨. r"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction (p.rename (fun v => .succ v)) phi)
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v)))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))))

theorem star_9_51 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_51_reading universal negation disjunction p r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction p.weakenReal
          (phi.weakenReal.instantiate value))
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal r.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)) :=
    star_2_38 negation disjunction r.weakenReal p.weakenReal
      (phi.weakenReal.instantiate value)
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction (p.rename (fun v => .succ v)) phi)
        (implication negation disjunction
          (sameDisjunction disjunction (p.rename (fun v => .succ v))
            (r.rename (fun v => .succ v)))
          (sameDisjunction disjunction phi
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction p.weakenReal
          (phi.weakenReal.instantiate value))
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal r.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution]
    rfl
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction (p.rename (fun v => .succ v)) phi)
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_31_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal1 : signature.Universal argument
      (max 0 (bindOrder 0 argument)))
    (universal2 : signature.Universal argument
      (bindOrder (max 0 (bindOrder 0 argument)) argument))
    (negation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (scopeDisjunction : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(∃x).φx .∨. (∃x).φx : ⊃ . (∃x).φx"
  parsed := .assertion (.always universal2 (.always universal1
    (mixedImplication negation scopeDisjunction
      (sameDisjunction matrixDisjunction
        (phi.rename star_9_3x_slotOuter)
        (phi.rename star_9_3x_slotInner))
      (.sometimes existential (phi.rename star_9_3x_slotThird)))))
  scopeReading := "This is printed line (3). Two applications of ✱9·03·02 read its universal binders as negated existential antecedents; recursive ✱9·05·06 then reads `(∃x).φx ∨ (∃y).φy` as the nested scoped matrix. The former raw `Taut` AST is not retained."

def star_9_33_reading
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .q .⊃ : (∃x).φx .∨. q   [Proof as above]"
  parsed := .assertion (star_9_06 existential disjunction (.neg negation q)
    (sameDisjunction disjunction phi (q.rename (fun v => .succ v))))
  scopeReading := "The outer implication is first read by ✱1·01; ✱9·06 moves its closed negated premiss below the existential, while the displayed member `(∃x).φx ∨ q` is read there by ✱9·05."

theorem star_9_33
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (scopeDisjunction : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0)
    (value : Term signature real [] argument) :
    Derivation (star_9_33_reading existential negation disjunction
      q phi).parsed := by
  let body := implication negation disjunction
    (q.rename (fun v => .succ v))
    (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))
  have closedQ :
      (q.rename (fun v => .succ v)).substitute
          (instantiateSubstitution value) = q := by
    rw [Formula.rename_substitute]
    apply Formula.substitute_eq_self
    intro sort v
    exact nomatch v
  have bodyAtValue : body.instantiate value =
      implication negation disjunction q
        (sameDisjunction disjunction (phi.instantiate value) q) := by
    unfold body Formula.instantiate
    rw [implication_substitute, sameDisjunction_substitute, closedQ]
  have line1 := Derivation.star_1_3_same negation disjunction
    (phi.instantiate value) q
  have line2 : Derivation (.assertion (body.instantiate value)) :=
    Derivation.castAssertion bodyAtValue line1
  have line3 := Derivation.star_9_1 existential negation scopeDisjunction
    body value
  have line4 := Derivation.star_9_12 negation scopeDisjunction line2 line3
  change Derivation (.assertion (star_9_06 existential disjunction
    (.neg negation q)
    (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))))
  rw [star_9_06_unfold]
  change Derivation (.assertion (.sometimes existential body))
  exact line4

def star_9_35_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal : signature.Universal argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(∃x).φx .⊃ : p .∨. (∃x).φx   [Proof as above]"
  parsed := .assertion (star_9_07 existential universal disjunction
    (.neg negation (phi.rename star_9_3x_slotOuter))
    (sameDisjunction disjunction
      (p.rename (fun v => .succ (.succ v)))
      (phi.rename star_9_3x_slotInner)))
  scopeReading := "The antecedent negation is ✱9·02, `p ∨ (∃x).φx` is ✱9·06, and ✱9·07 combines the resulting universal and existential members. The raw higher-order `Add` tree is deliberately not used."

def star_9_5_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p ⊃ q .⊃ : .p .∨. (x).φx : ⊃ : q .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction (p.rename (fun v => .succ v))
      (q.rename (fun v => .succ v)))
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))))

theorem star_9_5 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_5_reading universal negation disjunction p q phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction p.weakenReal q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate value))) :=
    star_2_38 negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal q.weakenReal
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction (p.rename (fun v => .succ v))
          (q.rename (fun v => .succ v)))
        (implication negation disjunction
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
          (sameDisjunction disjunction
            (q.rename (fun v => .succ v)) phi))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction p.weakenReal q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate value))) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction (p.rename (fun v => .succ v))
        (q.rename (fun v => .succ v)))
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi)))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_52_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : (x).φx .⊃. q : ⊃ : .(x).φx .∨. r .⊃ . q ∨ r"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction phi (q.rename (fun v => .succ v)))
    (implication negation disjunction
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))))

theorem star_9_52 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_52_reading universal negation disjunction q r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value) q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)
          (sameDisjunction disjunction q.weakenReal r.weakenReal)) :=
    star_2_38 negation disjunction r.weakenReal
      (phi.weakenReal.instantiate value) q.weakenReal
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction phi
          (q.rename (fun v => .succ v)))
        (implication negation disjunction
          (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
          (sameDisjunction disjunction (q.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value) q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)
          (sameDisjunction disjunction q.weakenReal r.weakenReal)) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction phi (q.rename (fun v => .succ v)))
      (implication negation disjunction
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_61_reading
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "If φx̂ and ψx̂ are elementary functions of the same type, there is a function φx̂ ∨ ψx̂."
  parsed := .functionExistence (sameDisjunction disjunction phi psi)

theorem star_9_61
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (star_9_61_reading disjunction phi psi).parsed := by
  have line1 := Derivation.star_10_121 psi
  have line2 := Derivation.star_10_121 phi
  have line3 := Derivation.star_10_121
    (sameDisjunction disjunction phi psi)
  have line4 := Derivation.star_10_122
    (sameDisjunction disjunction phi psi)
  exact line4

inductive Star9_62Branch where
  | universal
  | existential

def star_9_62_matrix
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Formula signature real [leftArgument] (bindOrder 0 rightArgument) :=
  Star9_62Branch.casesOn branch
    (.always universal (sameDisjunction disjunction phi
      (psi.rename (fun v => .succ v))))
    (.sometimes existential (sameDisjunction disjunction phi
      (psi.rename (fun v => .succ v))))

def star_9_62_reading
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Star9Reading signature real where
  printed := PM.pmPrinted "If φ(x̂, ŷ) and ψẑ are elementary functions, and the x-argument to φ is of the same type as the argument to ψ, there are functions (y).φ(x̂,y).∨.ψx̂, (∃y).φ(x̂,y).∨.ψx̂."
  parsed := .functionExistence
    (star_9_62_matrix universal existential disjunction phi psi branch)

theorem star_9_62
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Derivation (star_9_62_reading universal existential disjunction
      phi psi branch).parsed := by
  have line1 := Derivation.star_10_121
    (star_9_62_matrix universal existential disjunction phi psi branch)
  have line2 := Derivation.star_10_122
    (star_9_62_matrix universal existential disjunction phi psi branch)
  exact line2

inductive Star9_63Branch where
  | universalUniversal
  | universalExistential
  | existentialUniversal
  | existentialExistential

def star_9_63_matrix
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Formula signature real [leftArgument] (bindOrder 0 rightArgument) :=
  Star9_63Branch.casesOn branch
    (sameDisjunction disjunction (.always universal phi) (.always universal psi))
    (sameDisjunction disjunction (.always universal phi) (.sometimes existential psi))
    (sameDisjunction disjunction (.sometimes existential phi) (.always universal psi))
    (sameDisjunction disjunction (.sometimes existential phi) (.sometimes existential psi))

def star_9_63_reading
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Star9Reading signature real where
  printed := PM.pmPrinted "If φ(x̂, ŷ), ψ(x̂, ŷ) are elementary functions of the same type, there are functions (y).φ(x̂,y).∨.(z).ψ(x̂,z), etc.  [Proof as above]"
  parsed := .functionExistence
    (star_9_63_matrix universal existential disjunction phi psi branch)

theorem star_9_63
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Derivation (star_9_63_reading universal existential disjunction
      phi psi branch).parsed := by
  have line1 := Derivation.star_10_121
    (star_9_63_matrix universal existential disjunction phi psi branch)
  have line2 := Derivation.star_10_122
    (star_9_63_matrix universal existential disjunction phi psi branch)
  exact line2

section Star922

variable {signature : Signature} {real : Context} {argument : RSort}

private def s9ComposeSubstitution
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    Substitution signature real source target :=
  fun v => (sigma v).substitute tau

private theorem Term.s9_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (term : Term signature real source sort) :
    (term.substitute sigma).substitute tau =
      term.substitute (s9ComposeSubstitution sigma tau) := by
  cases term <;> rfl

private theorem Arguments.s9_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (arguments : Arguments signature real source sorts) :
    (arguments.substitute sigma).substitute tau =
      arguments.substitute (s9ComposeSubstitution sigma tau) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.s9_substitute_substitute, ih]

private theorem Term.s9_weaken_substitute_lift
    (tau : Substitution signature real middle target)
    (term : Term signature real middle sort) :
    term.weaken.substitute (liftSubstitution (sort := binder) tau) =
      (term.substitute tau).weaken := by
  cases term <;> rfl

private theorem s9_lift_comp_pointwise
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binder :: source) sort),
      (liftSubstitution sigma v).substitute (liftSubstitution tau) =
        liftSubstitution (s9ComposeSubstitution sigma tau) v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact Term.s9_weaken_substitute_lift tau (sigma v)

private theorem s9_liftN_comp_pointwise
    (binders : List RSort)
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      (liftSubstitutionN binders sigma v).substitute
          (liftSubstitutionN binders tau) =
        liftSubstitutionN binders (s9ComposeSubstitution sigma tau) v := by
  induction binders with
  | nil =>
      intro sort v
      rfl
  | cons binder binders ih =>
      intro sort v
      cases v with
      | zero => rfl
      | succ v =>
          exact Eq.trans
            (Term.s9_weaken_substitute_lift (liftSubstitutionN binders tau)
              (liftSubstitutionN binders sigma v))
            (congrArg Term.weaken (ih v))

private theorem s9_lift_congr
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binder :: source) sort),
      liftSubstitution sigma v = liftSubstitution tau v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Term.weaken (pointwise v)

private theorem s9_liftN_congr
    (binders : List RSort)
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftSubstitutionN binders sigma v = liftSubstitutionN binders tau v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih => exact s9_lift_congr _ _ ih

private theorem Term.s9_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (term : Term signature real source sort) :
    term.substitute sigma = term.substitute tau := by
  cases term with
  | real v => rfl
  | apparent v => exact pointwise v
  | symbol payload => rfl

private theorem Arguments.s9_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (arguments : Arguments signature real source sorts) :
    arguments.substitute sigma = arguments.substitute tau := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.s9_substitute_of_pointwise sigma tau pointwise, ih]

private theorem Formula.s9_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (formula : Formula signature real source order) :
    formula.substitute sigma = formula.substitute tau := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.s9_substitute_of_pointwise sigma tau pointwise]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.s9_substitute_of_pointwise sigma tau pointwise,
        Arguments.s9_substitute_of_pointwise sigma tau pointwise]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      exact congrArg (Formula.neg meaning) (ih sigma tau pointwise)
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH sigma tau pointwise, rightIH sigma tau pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      exact congrArg (Formula.always meaning)
        (ih (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise))
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau)
          (s9_liftN_congr parameters sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise)]

private theorem Formula.s9_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (formula : Formula signature real source order) :
    (formula.substitute sigma).substitute tau =
      formula.substitute (s9ComposeSubstitution sigma tau) := by
  induction formula generalizing middle target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.s9_substitute_substitute]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.s9_substitute_substitute, Arguments.s9_substitute_substitute]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH, rightIH]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      have line1 := ih (liftSubstitution sigma) (liftSubstitution tau)
      have line2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) body
      exact congrArg (Formula.always meaning) (Eq.trans line1 line2)
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      have matrixLine1 := matrixIH (liftSubstitutionN parameters sigma)
        (liftSubstitutionN parameters tau)
      have matrixLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau))
        (liftSubstitutionN parameters (s9ComposeSubstitution sigma tau))
        (s9_liftN_comp_pointwise parameters sigma tau) matrix
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextMatrix => Formula.incompleteScope kind parameters
          resultOrder excess scopeOrder nextMatrix
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans matrixLine1 matrixLine2))
        (congrArg (Formula.incompleteScope kind parameters resultOrder excess
          scopeOrder
          (matrix.substitute
            (liftSubstitutionN parameters (s9ComposeSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      have conditionLine1 := conditionIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have conditionLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) condition
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextCondition => Formula.descriptionScope sort
          conditionOrder scopeOrder nextCondition
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans conditionLine1 conditionLine2))
        (congrArg (Formula.descriptionScope sort conditionOrder scopeOrder
          (condition.substitute
            (liftSubstitution (s9ComposeSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))
private def star_9_22_slotY : Renaming [argument] [argument, argument, argument]
  | _, .zero => .succ (.succ .zero)
  | _, .succ v => nomatch v

private def star_9_22_slotX : Renaming [argument] [argument, argument, argument]
  | _, .zero => .succ .zero
  | _, .succ v => nomatch v

private def star_9_22_slotZ : Renaming [argument] [argument, argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

def star_9_22_matrix
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real [argument, argument, argument] matrixOrder :=
  implication negation disjunction
    (implication negation disjunction
      (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX))
    (implication negation disjunction
      (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ))

private def star_9_22_matrixReal
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature (argument :: real) [argument, argument] matrixOrder :=
  (star_9_22_matrix negation disjunction phi psi).weakenReal.substitute
    (liftSubstitution (liftSubstitution
      (instantiateSubstitution
        (.real (.zero : Var (argument :: real) argument)))))

private def star_9_22_bodyY
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature (argument :: real) [argument] matrixOrder :=
  (star_9_22_matrixReal negation disjunction phi psi).substitute
    (liftSubstitution
      (instantiateSubstitution
        (.real (.zero : Var (argument :: real) argument))))

theorem star_9_22_matrix_all_real
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    (star_9_22_bodyY negation disjunction phi psi).instantiate
      (.real (.zero : Var (argument :: real) argument)) =
      implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero)))
        (implication negation disjunction
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero))) := by
  unfold star_9_22_bodyY star_9_22_matrixReal Formula.instantiate
  rw [Formula.s9_substitute_substitute, Formula.s9_substitute_substitute]
  unfold star_9_22_matrix
  rw [implication_weakenReal, implication_weakenReal,
    implication_weakenReal, Formula.weakenReal_rename,
    Formula.weakenReal_rename, Formula.weakenReal_rename,
    Formula.weakenReal_rename, implication_substitute,
    implication_substitute, implication_substitute,
    Formula.rename_substitute, Formula.rename_substitute,
    Formula.rename_substitute, Formula.rename_substitute]
  let z : Term signature (argument :: real) [] argument := .real .zero
  let sigmaZ : Substitution signature (argument :: real)
      [argument, argument, argument] [argument, argument] :=
    liftSubstitution (liftSubstitution (instantiateSubstitution z))
  let sigmaX : Substitution signature (argument :: real)
      [argument, argument] [argument] :=
    liftSubstitution (instantiateSubstitution z)
  let sigmaY : Substitution signature (argument :: real) [argument] [] :=
    instantiateSubstitution z
  let sigmaAll : Substitution signature (argument :: real)
      [argument, argument, argument] [] :=
    fun v => s9ComposeSubstitution sigmaZ
      (s9ComposeSubstitution sigmaX sigmaY) v
  have slotXPhi :
      phi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotX sigmaAll) =
        phi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have slotXPsi :
      psi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotX sigmaAll) =
        psi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have slotYPhi :
      phi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotY sigmaAll) =
        phi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have slotZPsi :
      psi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotZ sigmaAll) =
        psi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  rw [slotXPhi, slotXPsi, slotYPhi, slotZPsi]

private def star_9_22_bodyX
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature (argument :: real) [argument]
      (bindOrder matrixOrder argument) :=
  .sometimes existential (star_9_22_matrixReal negation disjunction phi psi)

def star_9_22_body
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real [argument]
      (bindOrder (bindOrder matrixOrder argument) argument) :=
  .sometimes existential1
    (.sometimes existential0 (star_9_22_matrix negation disjunction phi psi))

def star_9_22_consequent
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (bindOrder matrixOrder argument) argument) :=
  .always existential1.universal
    (.sometimes existential0
      (implication negation disjunction
        (phi.rename star_9_3x_slotOuter)
        (psi.rename star_9_3x_slotInner)))

theorem star_9_22_bodyX_at_z
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    (star_9_22_bodyX existential negation disjunction phi psi).instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      .sometimes existential (star_9_22_bodyY negation disjunction phi psi) := by
  rfl

theorem star_9_22_body_at_z
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    (star_9_22_body existential0 existential1 negation disjunction phi psi).weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      .sometimes existential1
        (star_9_22_bodyX existential0 negation disjunction phi psi) := by
  rfl

def star_9_22_reading
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:.(x).φx⊃ψx.⊃:.(∃x).φx.⊃.(∃x).ψx"
  parsed := .assertion (.always universal2
    (star_9_22_body existential0 existential1
      negation0 disjunction0 phi psi))
  scopeReading := "The parsed AST is printed line (4), which PM identifies with the displayed proposition by the eliminable scope definitions ✱9·06, ✱9·08, ✱9·07, ✱9·01, and ✱9·02."

private def star_9_22_fixedClosed : Renaming [] [argument, argument] :=
  fun v => nomatch v

def star_9_22_fixedMatrix
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real [argument, argument] 0 :=
  implication negation disjunction
    (p.rename star_9_22_fixedClosed)
    (implication negation disjunction
      (phi.rename star_9_3x_slotOuter)
      (psi.rename star_9_3x_slotInner))

private def star_9_22_fixedMatrixReal
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature (argument :: real) [argument] 0 :=
  (star_9_22_fixedMatrix negation disjunction p phi psi).weakenReal.substitute
    (liftSubstitution
      (instantiateSubstitution
        (.real (.zero : Var (argument :: real) argument))))

private def star_9_22_fixedBody
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature (argument :: real) [] (bindOrder 0 argument) :=
  .sometimes existential
    (star_9_22_fixedMatrixReal negation disjunction p phi psi)

def star_9_22_fixedConsequent
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real []
      (bindOrder (bindOrder 0 argument) argument) :=
  .always existential1.universal
    (.sometimes existential0
      (star_9_22_fixedMatrix negation disjunction p phi psi))

theorem star_9_22_fixedMatrix_all_real
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    (star_9_22_fixedMatrixReal negation disjunction p phi psi).instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      implication negation disjunction p.weakenReal
        (implication negation disjunction
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero))) := by
  unfold star_9_22_fixedMatrixReal Formula.instantiate
  rw [Formula.s9_substitute_substitute]
  unfold star_9_22_fixedMatrix
  rw [implication_weakenReal, implication_weakenReal,
    Formula.weakenReal_rename, Formula.weakenReal_rename,
    Formula.weakenReal_rename, implication_substitute,
    implication_substitute, Formula.rename_substitute,
    Formula.rename_substitute, Formula.rename_substitute]
  let z : Term signature (argument :: real) [] argument := .real .zero
  let sigmaOuter : Substitution signature (argument :: real)
      [argument, argument] [argument] :=
    liftSubstitution (instantiateSubstitution z)
  let sigmaInner : Substitution signature (argument :: real) [argument] [] :=
    instantiateSubstitution z
  let sigmaAll : Substitution signature (argument :: real)
      [argument, argument] [] :=
    fun v => s9ComposeSubstitution sigmaOuter sigmaInner v
  have fixedP :
      p.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_fixedClosed sigmaAll) =
        p.weakenReal := by
    apply Formula.substitute_eq_self
    intro sort v
    exact nomatch v
  have outerPhi :
      phi.weakenReal.substitute
          (substitutionAfterRenaming star_9_3x_slotOuter sigmaAll) =
        phi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have innerPsi :
      psi.weakenReal.substitute
          (substitutionAfterRenaming star_9_3x_slotInner sigmaAll) =
        psi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  rw [fixedP, outerPhi, innerPsi]

private theorem star_9_22_fixedBody_at_z
    (existential0 : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    ((Formula.sometimes existential0
        (star_9_22_fixedMatrix negation disjunction p phi psi)).weakenReal).instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      star_9_22_fixedBody existential0 negation disjunction p phi psi := by
  rfl

theorem star_9_22_under_fixed
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (disjunction01 : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0)
    (line1 : Derivation (.assertion
      (implication negation0 disjunction0 p.weakenReal
        (implication negation0 disjunction0
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero)))))) :
    Derivation (.assertion
      (star_9_22_fixedConsequent existential0 existential1 negation0
        disjunction0 p phi psi)) := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  have matrixLine : Derivation (.assertion
      ((star_9_22_fixedMatrixReal negation0 disjunction0 p phi psi).instantiate
        z)) :=
    Derivation.castAssertion
      (star_9_22_fixedMatrix_all_real negation0 disjunction0 p phi psi)
      line1
  have existentialLine : Derivation (.assertion
      (star_9_22_fixedBody existential0 negation0 disjunction0 p phi psi)) :=
    Derivation.star_9_12 negation0 disjunction01 matrixLine
      (Derivation.star_9_1 existential0 negation0 disjunction01
        (star_9_22_fixedMatrixReal negation0 disjunction0 p phi psi) z)
  exact Derivation.star_9_13 existential1.universal
    (.sometimes existential0
      (star_9_22_fixedMatrix negation0 disjunction0 p phi psi))
    (Derivation.castAssertion
      (star_9_22_fixedBody_at_z existential0 negation0
        disjunction0 p phi psi).symm existentialLine)

end Star922

private def star_9_21_renamingSubstitution
    {signature : Signature} {realCtx : Context}
    (rho : Renaming source target) :
    Substitution signature realCtx source target :=
  fun v => .apparent (rho v)

private theorem Term.star_9_21_rename_as_substitute
    (rho : Renaming source target)
    (term : Term signature realCtx source sort) :
    term.rename rho = term.substitute (star_9_21_renamingSubstitution rho) := by
  cases term <;> rfl

private theorem Arguments.star_9_21_rename_as_substitute
    (rho : Renaming source target)
    (arguments : Arguments signature realCtx source sorts) :
    arguments.rename rho =
      arguments.substitute (star_9_21_renamingSubstitution rho) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.star_9_21_rename_as_substitute, ih]

private theorem star_9_21_lift_renamingSubstitution
    {signature : Signature} {realCtx : Context}
    (rho : Renaming source target) :
    ∀ {sort} (v : Var (binder :: source) sort),
      star_9_21_renamingSubstitution (signature := signature)
          (realCtx := realCtx) (liftRenaming rho) v =
        liftSubstitution (star_9_21_renamingSubstitution
          (signature := signature) (realCtx := realCtx) rho) v := by
  intro sort v
  cases v <;> rfl

private theorem star_9_21_liftN_renamingSubstitution
    {signature : Signature} {realCtx : Context}
    (binders : List RSort) (rho : Renaming source target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      star_9_21_renamingSubstitution (signature := signature)
          (realCtx := realCtx) (liftRenamingN binders rho) v =
        liftSubstitutionN binders (star_9_21_renamingSubstitution
          (signature := signature) (realCtx := realCtx) rho) v := by
  induction binders with
  | nil =>
      intro sort v
      rfl
  | cons binder binders ih =>
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact congrArg Term.weaken (ih v)

private theorem Formula.star_9_21_rename_as_substitute
    (rho : Renaming source target)
    (formula : Formula signature realCtx source order) :
    formula.rename rho =
      formula.substitute (star_9_21_renamingSubstitution rho) := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.star_9_21_rename_as_substitute]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.star_9_21_rename_as_substitute,
        Arguments.star_9_21_rename_as_substitute]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      exact congrArg (Formula.neg meaning) (ih rho)
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH rho, rightIH rho]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      rw [ih (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho)]
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftRenamingN parameters rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenamingN parameters rho))
          (liftSubstitutionN parameters (star_9_21_renamingSubstitution rho))
          (star_9_21_liftN_renamingSubstitution parameters rho),
        continuationIH (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho),
        continuationIH (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho)]

private theorem Formula.star_9_21_rename_rename
    (rho : Renaming source middle)
    (tau : Renaming middle target)
    (formula : Formula signature realCtx source order) :
    (formula.rename rho).rename tau =
      formula.rename (fun v => tau (rho v)) := by
  rw [Formula.star_9_21_rename_as_substitute,
    Formula.rename_substitute,
    Formula.star_9_21_rename_as_substitute]
  apply Formula.s9_substitute_of_pointwise
  intro sort v
  rfl

private theorem Formula.star_9_21_rename_of_pointwise
    (rho tau : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = tau v)
    (formula : Formula signature realCtx source order) :
    formula.rename rho = formula.rename tau := by
  rw [Formula.star_9_21_rename_as_substitute,
    Formula.star_9_21_rename_as_substitute]
  apply Formula.s9_substitute_of_pointwise
  intro sort v
  exact congrArg Term.apparent (pointwise v)

private def star_9_21_slotX : Renaming [argument] [argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

private theorem Formula.star_9_21_slotX_rename
    (formula : Formula signature real [argument] order) :
    formula.rename (fun v => .succ (star_9_21_slotX v)) =
      formula.rename star_9_22_slotX := by
  apply Formula.star_9_21_rename_of_pointwise
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact nomatch v

private theorem star_9_21_fixed_rename
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    (Formula.neg negation (implication negation disjunction
      (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX))).rename
        (fun v => .succ v) =
      .neg negation (implication negation disjunction
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX)) := by
  rw [Formula.star_9_21_rename_as_substitute]
  change Formula.neg negation
    ((implication negation disjunction
      (phi.rename star_9_21_slotX)
      (psi.rename star_9_21_slotX)).substitute _) = _
  rw [implication_substitute]
  rw [← Formula.star_9_21_rename_as_substitute,
    ← Formula.star_9_21_rename_as_substitute]
  rw [Formula.star_9_21_rename_rename,
    Formula.star_9_21_rename_rename]
  rw [Formula.star_9_21_slotX_rename,
    Formula.star_9_21_slotX_rename]

private theorem Formula.star_9_22_implication_rename
    (rho : Renaming source target)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order) :
    (implication negation disjunction left right).rename rho =
      implication negation disjunction (left.rename rho) (right.rename rho) := by
  rw [Formula.star_9_21_rename_as_substitute]
  rw [implication_substitute]
  rw [← Formula.star_9_21_rename_as_substitute,
    ← Formula.star_9_21_rename_as_substitute]

private theorem star_9_22_premiss_scope_rename
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    ((Formula.neg negation (implication negation disjunction phi psi)).rename
        (liftRenaming (fun v => .succ v))).rename (fun v => .succ v) =
      Formula.neg negation (implication negation disjunction
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX)) := by
  rw [Formula.star_9_21_rename_rename]
  have renameEq :
      (Formula.neg negation (implication negation disjunction phi psi)).rename
          (fun v => (liftRenaming (fun v => .succ v) v).succ) =
        (Formula.neg negation (implication negation disjunction phi psi)).rename
          star_9_22_slotX :=
    Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) _
  rw [renameEq]
  change Formula.neg negation
    ((implication negation disjunction phi psi).rename star_9_22_slotX) = _
  rw [Formula.star_9_22_implication_rename]

private theorem star_9_22_consequent_scope_rename
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    (implication negation disjunction
      (phi.rename star_9_3x_slotOuter)
      (psi.rename star_9_3x_slotInner)).rename
        (liftRenaming (fun v => .succ v)) =
      implication negation disjunction
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ) := by
  rw [Formula.star_9_22_implication_rename]
  rw [Formula.star_9_21_rename_rename,
    Formula.star_9_21_rename_rename]
  have innerEq :
      phi.rename (fun v =>
        liftRenaming (fun v => .succ v) (star_9_3x_slotOuter v)) =
        phi.rename star_9_22_slotY :=
    Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) phi
  have outerEq :
      psi.rename (fun v =>
        liftRenaming (fun v => .succ v) (star_9_3x_slotInner v)) =
        psi.rename star_9_22_slotZ :=
    Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) psi
  rw [innerEq, outerEq]

private theorem star_9_22_consequent_eq_star_9_07
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi =
      star_9_07 existential0 existential1.universal disjunction0
        ((Formula.neg negation0 phi).rename (fun v => .succ v))
        (psi.rename implicationScopeHead) := by
  unfold star_9_22_consequent star_9_07 implication mixedImplication
  have phiRename :
      (Formula.neg negation0 phi).rename (fun v => .succ v) =
        Formula.neg negation0 (phi.rename star_9_3x_slotOuter) := by
    change Formula.neg negation0 (phi.rename (fun v => .succ v)) = _
    exact congrArg (Formula.neg negation0)
      (Formula.star_9_21_rename_of_pointwise _ _ (by
        intro sort v
        cases v with
        | zero => rfl
        | succ v => exact nomatch v) phi)
  have psiRename :
      psi.rename implicationScopeHead =
        psi.rename star_9_3x_slotInner := by
    exact Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) psi
  rw [phiRename, psiRename]

@[reducible] def star_9_22_implicationReading
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (negation1 : signature.Negation (bindOrder matrixOrder argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder (bindOrder matrixOrder argument) argument)))
    (phi psi : Formula signature real [argument] matrixOrder) :
    ImplicationReading negation1 disjunction12
      (.always existential0.universal
        (implication negation0 disjunction0 phi psi))
      (.always universal2
        (star_9_22_body existential0 existential1
          negation0 disjunction0 phi psi))
      (star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi) := by
  let premissMatrix := implication negation0 disjunction0 phi psi
  let negatedPremiss := star_9_01 existential0 negation0 premissMatrix
  refine {
    negated := negatedPremiss
    negationDefinition := ?_
    disjunctionDefinition := ?_
  }
  · exact ImplicationNegation.star_9_01 negation1
      existential0.universal existential0 negation0 premissMatrix
  · unfold negatedPremiss premissMatrix star_9_22_consequent
    unfold star_9_22_body
    apply ImplicationDisjunction.star_9_04
      existential1.universal universal2
    apply ImplicationDisjunction.star_9_05 existential0 existential1
    apply ImplicationDisjunction.star_9_06 existential0 existential0
    rw [star_9_22_premiss_scope_rename,
      star_9_22_consequent_scope_rename]
    unfold star_9_22_matrix
    exact ImplicationDisjunction.star_1_01_same disjunction0
      (.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX)))
      (implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ))

private def star_9_22_line6Left
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real [argument] (bindOrder matrixOrder argument) :=
  .sometimes existential0
    (.neg negation0
      (implication negation0 disjunction0
        (phi.rename star_9_3x_slotOuter)
        (psi.rename star_9_3x_slotOuter)))

private def star_9_22_line6Right
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real [argument] (bindOrder matrixOrder argument) :=
  .sometimes existential0
    (implication negation0 disjunction0
      (phi.rename star_9_3x_slotOuter)
      (psi.rename star_9_3x_slotInner))

private structure Star922PrintedDemonstration
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (negation1 : signature.Negation (bindOrder matrixOrder argument))
    (disjunction1 : signature.Disjunction (bindOrder matrixOrder argument))
    (disjunction11 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder matrixOrder argument)))
    (disjunction12 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder (bindOrder matrixOrder argument) argument)))
    (phi psi : Formula signature real [argument] matrixOrder) where
  line4 : Derivation (.assertion (.always universal2
    (star_9_22_body existential0 existential1
      negation0 disjunction0 phi psi)))
  line5 : ImplicationReading negation1 disjunction12
    (.always existential0.universal
      (implication negation0 disjunction0 phi psi))
    (.always universal2
      (star_9_22_body existential0 existential1
        negation0 disjunction0 phi psi))
    (star_9_22_consequent existential0 existential1
      negation0 disjunction0 phi psi)
  line6 : ImplicationDisjunction signature real
    (.sometimes existential1
      (star_9_22_line6Left existential0 negation0 disjunction0 phi psi))
    (.always existential1.universal
      (star_9_22_line6Right existential0 negation0 disjunction0 phi psi))
    (star_9_08 existential1 universal2 disjunction1
      ((star_9_22_line6Left existential0 negation0 disjunction0 phi psi).rename
        implicationScopeHead)
      ((star_9_22_line6Right existential0 negation0 disjunction0 phi psi).rename
        (fun v => .succ v)))
  line7 : ImplicationReading negation1 disjunction11
    (.sometimes existential0 phi)
    (star_9_22_consequent existential0 existential1
      negation0 disjunction0 phi psi)
    (.sometimes existential0 psi)

theorem star_9_22
    {matrixOrder : Nat}
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (disjunction01 : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (negation1 : signature.Negation (bindOrder matrixOrder argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder (bindOrder matrixOrder argument) argument)))
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (.assertion (.always universal2
      (star_9_22_body existential0 existential1 negation0 disjunction0 phi psi))) := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  let core := implication negation0 disjunction0
    (phi.weakenReal.instantiate z) (psi.weakenReal.instantiate z)
  have line1 : Derivation (.assertion
      ((star_9_22_bodyY negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_matrix_all_real negation0 disjunction0 phi psi)
      (star_2_08 negation0 disjunction0 core)
  have line2 : Derivation (.assertion
      ((star_9_22_bodyX existential0 negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_bodyX_at_z existential0 negation0 disjunction0 phi psi)
      (Derivation.star_9_12 negation0 disjunction01 line1
        (Derivation.star_9_1 existential0 negation0 disjunction01
          (star_9_22_bodyY negation0 disjunction0 phi psi) z))
  have line3 := Derivation.star_9_12 negation1 disjunction12 line2
    (Derivation.star_9_1 existential1 negation1 disjunction12
      (star_9_22_bodyX existential0 negation0 disjunction0 phi psi) z)
  have line4 := Derivation.star_9_13 universal2
    (star_9_22_body existential0 existential1 negation0 disjunction0 phi psi)
    (Derivation.castAssertion
      (star_9_22_body_at_z existential0 existential1 negation0 disjunction0 phi psi)
      line3)
  have line5 : ImplicationReading negation1 disjunction12
      (.always existential0.universal
        (implication negation0 disjunction0 phi psi))
      (.always universal2
        (star_9_22_body existential0 existential1
          negation0 disjunction0 phi psi))
      (star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi) := by
    let premissMatrix := implication negation0 disjunction0 phi psi
    let negatedPremiss := star_9_01 existential0 negation0 premissMatrix
    refine {
      negated := negatedPremiss
      negationDefinition := ?_
      disjunctionDefinition := ?_
    }
    · exact ImplicationNegation.star_9_01 negation1
        existential0.universal existential0 negation0 premissMatrix
    · unfold negatedPremiss premissMatrix star_9_22_consequent
      unfold star_9_22_body
      apply ImplicationDisjunction.star_9_04
        existential1.universal universal2
      apply ImplicationDisjunction.star_9_05 existential0 existential1
      apply ImplicationDisjunction.star_9_06 existential0 existential0
      rw [star_9_22_premiss_scope_rename,
        star_9_22_consequent_scope_rename]
      unfold star_9_22_matrix
      let left := Formula.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX))
      let right := implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ)
      exact ImplicationDisjunction.star_1_01_same disjunction0 left right
  let matrixBindMax :
      max matrixOrder (bindOrder matrixOrder argument) =
        bindOrder matrixOrder argument :=
    Eq.trans (bindOrderMaxLeft matrixOrder matrixOrder argument)
      (congrArg (fun order => bindOrder order argument)
        (natMaxSelf matrixOrder))
  let disjunction1 : signature.Disjunction
      (bindOrder matrixOrder argument) :=
    Eq.mp (congrArg signature.Disjunction matrixBindMax) disjunction01
  have line6 := ImplicationDisjunction.star_9_08
    existential1 existential1.universal universal2 disjunction1
    (star_9_22_line6Left existential0 negation0 disjunction0 phi psi)
    (star_9_22_line6Right existential0 negation0 disjunction0 phi psi)
  let disjunction11 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder matrixOrder argument)) :=
    Eq.mp (congrArg signature.Disjunction
      (natMaxSelf (bindOrder matrixOrder argument)).symm) disjunction1
  have line7 : ImplicationReading negation1 disjunction11
      (.sometimes existential0 phi)
      (star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi)
      (.sometimes existential0 psi) := by
    refine {
      negated := star_9_02 existential0.universal negation0 phi
      negationDefinition := ?_
      disjunctionDefinition := ?_
    }
    · exact ImplicationNegation.star_9_02 negation1 existential0
        existential0.universal negation0 phi
    · exact Eq.mp (congrArg
        (ImplicationDisjunction signature real
          (star_9_02 existential0.universal negation0 phi)
          (.sometimes existential0 psi))
        (star_9_22_consequent_eq_star_9_07 existential0 existential1
          negation0 disjunction0 phi psi).symm)
        (ImplicationDisjunction.star_9_07
          existential0.universal existential0 existential1.universal
          disjunction0 (.neg negation0 phi) psi)
  let printedDemonstration : Star922PrintedDemonstration existential0
      existential1 universal2 negation0 disjunction0 negation1
      disjunction1 disjunction11 disjunction12 phi psi := {
    line4 := line4
    line5 := line5
    line6 := line6
    line7 := line7
  }
  exact printedDemonstration.line4

private def star_9_21_line5Formula
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (bindOrder matrixOrder argument) argument) argument) :=
  .always universal2 (.sometimes existential1 (.sometimes existential0
    (sameDisjunction disjunction0
      ((Formula.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX))).rename
          (fun v => .succ v))
      (implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ)))))

private def star_9_21_line6Formula
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (bindOrder matrixOrder argument) argument) argument) :=
  .always universal2 (.sometimes existential1 (.sometimes existential0
    (sameDisjunction disjunction0
      ((Formula.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX))).rename
          (fun v => .succ v))
      (implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ)))))

def star_9_21_formula
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (bindOrder matrixOrder argument) argument) argument) :=
  .always universal2 (.sometimes existential1 (.sometimes existential0
    (sameDisjunction disjunction0
      ((Formula.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX))).rename
          (fun v => .succ v))
      (sameDisjunction disjunction0
        (.neg negation0 (phi.rename star_9_22_slotY))
        (psi.rename star_9_22_slotZ)))))

def star_9_21_reading
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:.(x).φx⊃ψx.⊃:.(x).φx.⊃.(x).ψx"
  parsed := .assertion (star_9_21_formula existential0 existential1
    universal2 negation0 disjunction0 phi psi)
  scopeReading := "The parsed AST is printed line (7): the three quantifiers are retained through the eliminable definitions ✱9·06 and ✱9·08, and bound-variable renaming is definitional in the de Bruijn syntax."

theorem star_9_21
    {matrixOrder : Nat}
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (disjunction01 : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (negation1 : signature.Negation (bindOrder matrixOrder argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder (bindOrder matrixOrder argument) argument)))
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (star_9_21_reading existential0 existential1 universal2
      negation0 disjunction0 phi psi).parsed := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  let core := implication negation0 disjunction0
    (phi.weakenReal.instantiate z) (psi.weakenReal.instantiate z)
  have line1 : Derivation (.assertion
      ((star_9_22_bodyY negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_matrix_all_real negation0 disjunction0 phi psi)
      (star_2_08 negation0 disjunction0 core)
  have line2 : Derivation (.assertion
      ((star_9_22_bodyX existential0 negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_bodyX_at_z existential0 negation0 disjunction0 phi psi)
      (Derivation.star_9_12 negation0 disjunction01 line1
        (Derivation.star_9_1 existential0 negation0 disjunction01
          (star_9_22_bodyY negation0 disjunction0 phi psi) z))
  have line3 := Derivation.star_9_12 negation1 disjunction12 line2
    (Derivation.star_9_1 existential1 negation1 disjunction12
      (star_9_22_bodyX existential0 negation0 disjunction0 phi psi) z)
  have line4 := Derivation.star_9_13 universal2
    (star_9_22_body existential0 existential1 negation0 disjunction0 phi psi)
    (Derivation.castAssertion
      (star_9_22_body_at_z existential0 existential1 negation0 disjunction0 phi psi)
      line3)
  have line5 : Derivation (.assertion (star_9_21_line5Formula existential0
      existential1 universal2 negation0 disjunction0 phi psi)) := by
    unfold star_9_21_line5Formula
    rw [star_9_21_fixed_rename]
    unfold star_9_22_body star_9_22_matrix at line4
    exact line4
  have line6 : Derivation (.assertion (star_9_21_line6Formula existential0
      existential1 universal2 negation0 disjunction0 phi psi)) := by
    unfold star_9_21_line5Formula at line5
    unfold star_9_21_line6Formula
    exact line5
  have line7 : Derivation (.assertion (star_9_21_formula existential0
      existential1 universal2 negation0 disjunction0 phi psi)) := by
    unfold star_9_21_formula
    unfold star_9_21_line6Formula at line6
    unfold implication mixedImplication at line6 ⊢
    exact line6
  exact line7

#print axioms star_9_1
#print axioms star_9_11
#print axioms star_9_12
#print axioms star_9_13
#print axioms star_9_14
#print axioms star_9_15
#print axioms star_9_22
#print axioms star_9_22_fixedMatrix_all_real
#print axioms star_9_22_under_fixed
#print axioms star_9_32
#print axioms star_9_2
#print axioms star_9_3
#print axioms star_9_4
#print axioms star_9_361
#print axioms star_9_23
#print axioms star_9_24
#print axioms star_9_25
#print axioms star_9_41
#print axioms star_9_42
#print axioms star_9_51
#print axioms star_9_21
#print axioms star_9_33
#print axioms star_9_5
#print axioms star_9_52
#print axioms star_9_61
#print axioms star_9_62
#print axioms star_9_63

end PM.RamifiedSyntax
