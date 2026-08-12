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

/-- Capture-free renamings of PM real variables.  These are deliberately
separate from `Renaming`: the latter changes apparent-variable binders,
whereas this operation changes only the ambient real-variable context. -/
abbrev RealRenaming (Γ Ξ : RealContext) :=
  {τ : RealType} → RealVar Γ τ → RealVar Ξ τ

/-- The audited diagonal instance used in the first application of ✱9·1 in
the proof of ✱9·3: the newly introduced real `y` and the displayed real `x`
are both read as `x`; older variables are shifted once. -/
def diagonalRealRenaming :
    RealRenaming (.elementaryProposition :: .elementaryProposition :: Γ)
      (.elementaryProposition :: Γ)
  | _, .zero => .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ predecessor) => .succ predecessor

/-- Simultaneous renaming of the ambient real variables, leaving all apparent
binders untouched. -/
def renameReal (ρ : RealRenaming Γ Ξ) : Apparent Γ Δ → Apparent Ξ Δ
  | .constant name => .constant name
  | .real v => .real (ρ v)
  | .bound v => .bound v
  | .neg proposition => .neg (renameReal ρ proposition)
  | .disj left right => .disj (renameReal ρ left) (renameReal ρ right)

/-- Weakening by one newly available real variable.  It never introduces an
apparent binder. -/
def weakenReal (proposition : Apparent Γ Δ) : Apparent (τ :: Γ) Δ :=
  renameReal (fun v => .succ v) proposition

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

/-- An apparent matrix with no apparent variables is syntactically an
elementary proposition.  This total erasure is used for the displayed
instances `φx` in ✱9·1 and ✱9·11. -/
def closedToElementary : Apparent Γ [] → Elementary Γ
  | .constant name => .constant name
  | .real v => .var v
  | .bound v => nomatch v
  | .neg proposition => .neg (closedToElementary proposition)
  | .disj left right => .disj (closedToElementary left) (closedToElementary right)

/-- Capture-free renamings of apparent variables. -/
abbrev Renaming (Δ Ξ : BoundContext) :=
  BoundVar Δ .elementaryProposition → BoundVar Ξ .elementaryProposition

/-- Lift a renaming through one binder. -/
def liftRenaming (ρ : Renaming Δ Ξ) :
    Renaming (.elementaryProposition :: Δ) (.elementaryProposition :: Ξ)
  | .zero => .zero
  | .succ v => .succ (ρ v)

/-- Embed a one-variable matrix under a new inner variable. The old head
variable becomes the outer variable (index one). -/
def outerVariableRenaming :
    Renaming (.elementaryProposition :: Δ)
      (.elementaryProposition :: .elementaryProposition :: Δ)
  | .zero => .succ .zero
  | .succ v => .succ (.succ v)

/-- Embed a one-variable matrix as the new inner variable. The old head stays
at index zero, while variables from the tail cross both binders. -/
def innerVariableRenaming :
    Renaming (.elementaryProposition :: Δ)
      (.elementaryProposition :: .elementaryProposition :: Δ)
  | .zero => .zero
  | .succ v => .succ (.succ v)

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

/-- The displayed elementary value of a one-place elementary function at a
specified real variable.  The result has no apparent variables; this is an
object-syntactic operation, not semantic application. -/
def atReal (body : Apparent Γ [.elementaryProposition])
    (x : RealVar Γ .elementaryProposition) : Elementary Γ :=
  closedToElementary (instantiate body (.real x))

/-- Abstract the leading real variable into the one apparent-variable matrix.
This is the precise context change needed by ✱9·13.  Other real variables
remain real and retain their de Bruijn positions. -/
def abstractHead : Elementary (.elementaryProposition :: Γ) →
    Apparent Γ [.elementaryProposition]
  | .constant name => .constant name
  | .var .zero => .bound .zero
  | .var (.succ v) => .real v
  | .neg proposition => .neg (abstractHead proposition)
  | .disj left right => .disj (abstractHead left) (abstractHead right)

/-- Open a one-place apparent matrix at the newly leading real variable.
Together with `abstractHead`, this provides the scope-certified real/apparent
bridge without treating a real-variable context as hypotheses. -/
def openHead : Apparent Γ [.elementaryProposition] →
    Elementary (.elementaryProposition :: Γ)
  | .constant name => .constant name
  | .real v => .var (.succ v)
  | .bound .zero => .var .zero
  | .bound (.succ v) => nomatch v
  | .neg proposition => .neg (openHead proposition)
  | .disj left right => .disj (openHead left) (openHead right)

/-- Metalinguistic value of a one-place elementary matrix at an explicitly
given elementary argument.  Unlike `Apparent.substitute`, this operation has
no remaining apparent binder and returns the conservative `Elementary`
syntax used by ✱1–✱5. -/
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

/-- The diagonal evaluation used in the first application of ✱9·1 in the
proof of ✱9·3. -/
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

/-- Instantiating the outer apparent slot at the leading real after embedding
a one-place matrix as the outer of two slots recovers its displayed elementary
value.  This is the capture-safe beta law used for the `φx` branch of the
higher ✱9·1 instance. -/
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

/-- The bivariate matrix `φx ∨ φy` used in the first application of ✱9·1
in the proof of ✱9·3.  The left occurrence opens the sole binder as the new
real variable `x`; the right occurrence retains it as the apparent variable
`y`.  Thus no substitution or identification of the two variables occurs. -/
def openHeadOrBound (φ : Apparent Γ [.elementaryProposition]) :
    Apparent (.elementaryProposition :: Γ) [.elementaryProposition] :=
  Apparent.ofElementary (openHead φ) ∨ₐ Apparent.weakenReal φ

@[simp] theorem openHeadOrBound_left
    (φ : Apparent Γ [.elementaryProposition]) :
    openHeadOrBound φ =
      Apparent.ofElementary (openHead φ) ∨ₐ Apparent.weakenReal φ := rfl

/-- Move one newly leading *real* variable into the leading apparent-variable
slot.  Unlike `abstractHead`, this operation works underneath an already
present apparent-variable context.  It is the scope-preserving bridge needed
when ✱9·13 is applied to a formula which is already of first order. -/
def abstractRealHead : Apparent (.elementaryProposition :: Γ) Δ →
    Apparent Γ (.elementaryProposition :: Δ)
  | .constant name => .constant name
  | .real .zero => .bound .zero
  | .real (.succ predecessor) => .real predecessor
  | .bound boundVariable => .bound (.succ boundVariable)
  | .neg proposition => .neg (abstractRealHead proposition)
  | .disj left right => .disj (abstractRealHead left) (abstractRealHead right)

/-- Inverse scope operation for `abstractRealHead`: the leading apparent
variable becomes the newly leading real variable, while all older apparent
variables retain their indices.  This is not a general substitution rule. -/
def openRealHead : Apparent Γ (.elementaryProposition :: Δ) →
    Apparent (.elementaryProposition :: Γ) Δ
  | .constant name => .constant name
  | .real realVariable => .real (.succ realVariable)
  | .bound .zero => .real .zero
  | .bound (.succ predecessor) => .bound predecessor
  | .neg proposition => .neg (openRealHead proposition)
  | .disj left right => .disj (openRealHead left) (openRealHead right)

/-- The beta law records the only alpha/scope conversion used by the
assigned 1→2 instance of ✱9·13.  It is structural and capture-free. -/
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

/-- Abstract a newly leading real variable when an apparent binder is already
open.  The existing inner binder remains index zero, while the abstracted
real becomes its outer neighbour at index one.  This is the capture-safe
scope change required by the `(x)(∃y)` step in ✱9·3. -/
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

/-- Inverse of `abstractRealOuter`.  It opens the outer apparent variable as
a leading real variable and deliberately leaves the pre-existing inner
binder at index zero. -/
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

/-- Opening a one-place matrix at a real variable and then placing that real
outside an existing binder is precisely apparent-variable weakening. -/
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

/-- A real-context weakening becomes the inner-variable embedding after that
new real is abstracted outside the already present apparent binder. -/
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

/-- ✱9·07 at one explicitly assigned matrix order.

`renameMatrix` and `disjMatrix` are supplied for that fixed order. The result
performs exactly two quantifier steps, with `x` outermost and `y` innermost. -/
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

/-- ✱9·08 at one explicitly assigned matrix order. The binders remain `x`
outside `y`; only the printed operand order in the matrix is reversed. -/
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

/-- First-order propositions: one quantified step over elementary matrices. -/
abbrev FirstOrder (Γ : RealContext) : BoundContext → Type :=
  Quantified (Apparent Γ)

/-- Propositions obtained by a second assigned quantifier step. -/
abbrev SecondOrder (Γ : RealContext) : BoundContext → Type :=
  Quantified (FirstOrder Γ)

/-- First-order formulae when they occur as matrices for one further assigned
quantifier.  The existing `FirstOrder` syntax represents only a quantified
atom; this separate, scoped layer supplies the same-order negation and
disjunction required to express mixed first-to-second-order formulae without
coercing them into `Apparent` or adding a judgement constructor. -/
inductive FirstOrderMatrix (Γ : RealContext) (Δ : BoundContext) where
  | quantified : FirstOrder Γ Δ → FirstOrderMatrix Γ Δ
  | neg : FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Δ
  | disj : FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Δ

namespace FirstOrderMatrix

prefix:max "∼₁ₘ" => neg
infixl:55 " ∨₁ₘ " => disj

/-- Conservative embedding of the already established first-order AST. -/
def ofFirstOrder (proposition : FirstOrder Γ Δ) : FirstOrderMatrix Γ Δ :=
  .quantified proposition

/-- The same-assigned-order matrix implication abbreviation. -/
def imp (p q : FirstOrderMatrix Γ Δ) : FirstOrderMatrix Γ Δ :=
  ∼₁ₘ p ∨₁ₘ q

infixr:54 " ⊃₁ₘ " => imp

/-- A single next-order quantifier over the explicit matrix language. -/
abbrev Quantified (Γ : RealContext) (Δ : BoundContext) :=
  PM.Quantified (FirstOrderMatrix Γ) Δ

end FirstOrderMatrix

namespace SecondOrder

/-- Capture-free renaming of ambient real variables below one explicit
second-order binder.  Apparent binders are preserved unchanged. -/
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

/-- PM's primitive idea `(x).φx`. -/
abbrev always (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := Quantified.always body

/-- PM's primitive idea `(∃x).φx`. -/
abbrev sometimes (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := Quantified.sometimes body

/-- Weakening of the ambient real-variable context beneath either primitive
binder.  This is required when the displayed instance `φx` remains free while
the existential conclusion `(∃z).φz` no longer depends on that real variable.
It is not a substitution rule and does not alter apparent-variable scope. -/
def weakenReal : FirstOrder Γ Δ → FirstOrder (τ :: Γ) Δ
  | Quantified.always body => Quantified.always (Apparent.weakenReal body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.weakenReal body)

/-- Capture-free renaming of real variables throughout a first-order
proposition.  It changes no apparent binder. -/
def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    FirstOrder Γ Δ → FirstOrder Ξ Δ
  | Quantified.always body => Quantified.always (Apparent.renameReal ρ body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.renameReal ρ body)

/-- Abstract a newly leading real variable under an existing first-order
proposition.  Its result has one additional apparent-variable slot; this is
the matrix on which the single assigned 1→2 use of ✱9·13 operates. -/
def abstractRealHead : FirstOrder (.elementaryProposition :: Γ) Δ →
    FirstOrder Γ (.elementaryProposition :: Δ)
  | Quantified.always body => Quantified.always (Apparent.abstractRealHead body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.abstractRealHead body)

/-- Open the leading apparent variable of a first-order matrix as a newly
leading real variable.  This is the inverse used to state the premise of the
printed ✱9·13 rule at the next assigned order. -/
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

/-- Abstract a leading real variable *outside* an already-open apparent
binder.  Each first-order constructor preserves its inner binder; the new
outer variable is inserted behind it by `Apparent.abstractRealOuter`. -/
def abstractRealOuter : FirstOrder (.elementaryProposition :: Γ) Δ →
    FirstOrder Γ (.elementaryProposition :: Δ)
  | Quantified.always body => Quantified.always (Apparent.abstractRealOuter body)
  | Quantified.sometimes body => Quantified.sometimes (Apparent.abstractRealOuter body)

/-- Inverse of `abstractRealOuter`, opening only the outer apparent variable
while retaining every inner first-order binder. -/
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

/-- Capture-free renaming beneath either primitive binder. -/
def rename (ρ : Apparent.Renaming Δ Ξ) : FirstOrder Γ Δ → FirstOrder Γ Ξ
  | Quantified.always body =>
      Quantified.always (Apparent.rename (Apparent.liftRenaming ρ) body)
  | Quantified.sometimes body =>
      Quantified.sometimes (Apparent.rename (Apparent.liftRenaming ρ) body)

/-- Capture-free substitution beneath either primitive binder. -/
def substitute (σ : Apparent.Substitution Γ Δ Ξ) :
    FirstOrder Γ Δ → FirstOrder Γ Ξ
  | Quantified.always body =>
      Quantified.always
        (Apparent.substitute (Apparent.liftSubstitution σ) body)
  | Quantified.sometimes body =>
      Quantified.sometimes
        (Apparent.substitute (Apparent.liftSubstitution σ) body)

/-- Instantiate the nearest apparent slot of a first-order matrix.  The
substitution is lifted through its existing quantifier, so its bound variable
remains capture-safe.  This is syntax only, not a quantifier inference. -/
def instantiate (body : FirstOrder Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : FirstOrder Γ Δ :=
  substitute (Apparent.instantiateSubstitution argument) body

/-- The displayed real-value specialization of `FirstOrder.instantiate`.
It is the syntax needed to state an instance of ✱9·1 whose matrix already
contains one first-order quantifier. -/
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

/-- A free apparent variable is significant in a quantified proposition when
its shifted occurrence is significant in the matrix. -/
def Significant (v : BoundVar Δ .elementaryProposition) :
    FirstOrder Γ Δ → Prop
  | Quantified.always body => Apparent.Significant (.succ v) body
  | Quantified.sometimes body => Apparent.Significant (.succ v) body

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

/-- Disjunction of a first-order proposition with an elementary proposition.
The binder is preserved and elementary disjunction is formed in its matrix;
the two branches are precisely ✱9·03 and ✱9·05. -/
def disjRightElementary : FirstOrder Γ Δ → Elementary Γ → FirstOrder Γ Δ
  | Quantified.always body, proposition =>
      always (body ∨ₐ Apparent.ofElementary proposition)
  | Quantified.sometimes body, proposition =>
      sometimes (body ∨ₐ Apparent.ofElementary proposition)

/-- Matrix-level ✱9·03/05.  Unlike the displayed elementary specialization,
the right operand may retain the surrounding apparent-variable context. -/
def disjRightMatrix : FirstOrder Γ Δ → Apparent Γ Δ → FirstOrder Γ Δ
  | Quantified.always body, proposition =>
      always (body ∨ₐ Apparent.weaken proposition)
  | Quantified.sometimes body, proposition =>
      sometimes (body ∨ₐ Apparent.weaken proposition)

/-- Disjunction of an elementary proposition with a first-order proposition.
Operand order is retained in the matrix; the two branches are precisely
✱9·04 and ✱9·06. -/
def disjElementaryLeft : Elementary Γ → FirstOrder Γ Δ → FirstOrder Γ Δ
  | proposition, Quantified.always body =>
      always (Apparent.ofElementary proposition ∨ₐ body)
  | proposition, Quantified.sometimes body =>
      sometimes (Apparent.ofElementary proposition ∨ₐ body)

/-- Matrix-level ✱9·04/06, preserving the left-to-right operand order under
the already-present binder. -/
def disjMatrixLeft : Apparent Γ Δ → FirstOrder Γ Δ → FirstOrder Γ Δ
  | proposition, Quantified.always body =>
      always (Apparent.weaken proposition ∨ₐ body)
  | proposition, Quantified.sometimes body =>
      sometimes (Apparent.weaken proposition ∨ₐ body)

/-- The printed mixed-order implication `p ⊃ P` at an assigned first order.
It is only the PM abbreviation `∼p ∨ P`; no elementary proposition is
silently coerced into a first-order proposition. -/
def impElementaryToFirst (proposition : Elementary Γ) :
    FirstOrder Γ Δ → FirstOrder Γ Δ :=
  disjElementaryLeft (Elementary.neg proposition)

/-- The exact normalized matrix form of a first-order-to-elementary
implication: `P ⊃ q` is `∼P ∨ q`.  It is syntax only; no inference rule is
claimed. -/
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

/-- ✱9·03 as a kernel reduction. -/
@[simp] theorem star_9_03_reduction
    (body : Apparent Γ (.elementaryProposition :: Δ))
    (proposition : Elementary Γ) :
    disjRightElementary (always body) proposition =
      always (body ∨ₐ Apparent.ofElementary proposition) := rfl

/-- ✱9·04 as a kernel reduction. -/
@[simp] theorem star_9_04_reduction
    (proposition : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    disjElementaryLeft proposition (always body) =
      always (Apparent.ofElementary proposition ∨ₐ body) := rfl

/-- ✱9·05 as a kernel reduction. -/
@[simp] theorem star_9_05_reduction
    (body : Apparent Γ (.elementaryProposition :: Δ))
    (proposition : Elementary Γ) :
    disjRightElementary (sometimes body) proposition =
      sometimes (body ∨ₐ Apparent.ofElementary proposition) := rfl

/-- ✱9·06 as a kernel reduction. -/
@[simp] theorem star_9_06_reduction
    (proposition : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    disjElementaryLeft proposition (sometimes body) =
      sometimes (Apparent.ofElementary proposition ∨ₐ body) := rfl

/-- The elementary-matrix specialization of ✱9·07. -/
def disjAlwaysSometimes
    (φ ψ : Apparent Γ (.elementaryProposition :: Δ)) : SecondOrder Γ Δ :=
  Quantified.disjAlwaysSometimes Apparent.rename Apparent.disj φ ψ

/-- The elementary-matrix specialization of ✱9·08. Arguments retain the
printed left-to-right order: existential body `ψ`, then universal body `φ`. -/
def disjSometimesAlways
    (ψ φ : Apparent Γ (.elementaryProposition :: Δ)) : SecondOrder Γ Δ :=
  Quantified.disjSometimesAlways Apparent.rename Apparent.disj ψ φ

/-- ✱9·07 as an exact kernel reduction. -/
@[simp] theorem star_9_07_reduction
    (φ ψ : Apparent Γ (.elementaryProposition :: Δ)) :
    disjAlwaysSometimes φ ψ =
      Quantified.always
        (Quantified.sometimes
          (Apparent.rename Apparent.outerVariableRenaming φ ∨ₐ
            Apparent.rename Apparent.innerVariableRenaming ψ)) := rfl

/-- ✱9·08 as an exact kernel reduction. -/
@[simp] theorem star_9_08_reduction
    (ψ φ : Apparent Γ (.elementaryProposition :: Δ)) :
    disjSometimesAlways ψ φ =
      Quantified.always
        (Quantified.sometimes
          (Apparent.rename Apparent.innerVariableRenaming ψ ∨ₐ
            Apparent.rename Apparent.outerVariableRenaming φ)) := rfl

end FirstOrder

namespace FirstOrderMatrix

/-- Real-context renaming preserves the assigned matrix order. -/
def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    FirstOrderMatrix Γ Δ → FirstOrderMatrix Ξ Δ
  | .quantified proposition => .quantified (FirstOrder.renameReal ρ proposition)
  | .neg proposition => .neg (renameReal ρ proposition)
  | .disj left right => .disj (renameReal ρ left) (renameReal ρ right)

/-- Capture-free apparent-variable renaming through same-order connectives. -/
def rename (ρ : Apparent.Renaming Δ Ξ) :
    FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Ξ
  | .quantified proposition => .quantified (FirstOrder.rename ρ proposition)
  | .neg proposition => .neg (rename ρ proposition)
  | .disj left right => .disj (rename ρ left) (rename ρ right)

def weaken (proposition : FirstOrderMatrix Γ Δ) :
    FirstOrderMatrix Γ (.elementaryProposition :: Δ) :=
  rename (fun v => .succ v) proposition

/-- Capture-free apparent-variable substitution through matrix connectives. -/
def substitute (σ : Apparent.Substitution Γ Δ Ξ) :
    FirstOrderMatrix Γ Δ → FirstOrderMatrix Γ Ξ
  | .quantified proposition => .quantified (FirstOrder.substitute σ proposition)
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

def instantiate (body : FirstOrderMatrix Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : FirstOrderMatrix Γ Δ :=
  substitute (Apparent.instantiateSubstitution argument) body

def atReal (body : FirstOrderMatrix Γ [.elementaryProposition])
    (x : RealVar Γ .elementaryProposition) : FirstOrderMatrix Γ [] :=
  instantiate body (.real x)

/-- Explicit embedding of the pre-existing second-order carrier into the
enriched matrix carrier.  It is structural and preserves each quantified
first-order atom verbatim. -/
def ofSecondOrder : SecondOrder Γ Δ → Quantified Γ Δ
  | PM.Quantified.always body => PM.Quantified.always (.quantified body)
  | PM.Quantified.sometimes body => PM.Quantified.sometimes (.quantified body)

@[simp] theorem instantiate_quantified
    (body : FirstOrder Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) :
    instantiate (.quantified body) argument =
      .quantified (FirstOrder.instantiate body argument) := rfl

/-- The mixed implication from an assigned first-order matrix to a quantified
next-order matrix, in its printed `∼P ∨ Q` normal form.  Since the outer
quantifier belongs to `Q`, the left matrix is weakened beneath precisely that
binder; no cross-order coercion is used. -/
def impToQuantified (premise : FirstOrderMatrix Γ Δ) :
    Quantified Γ Δ → Quantified Γ Δ
  | PM.Quantified.always body =>
      PM.Quantified.always (imp (weaken premise) body)
  | PM.Quantified.sometimes body =>
      PM.Quantified.sometimes (imp (weaken premise) body)

/-- The exact higher-order shape of ✱9·1 needed by line (3) of ✱9·21:
the displayed value of a first-order matrix implies its existential closure.
This is a syntax target only; it grants no assertion or inference rule. -/
def star_9_1_higher_target
    (body : FirstOrderMatrix Γ [.elementaryProposition])
    (value : RealVar Γ .elementaryProposition) : Quantified Γ [] :=
  impToQuantified (atReal body value) (PM.Quantified.sometimes body)

/-- The sole third assigned-order carrier needed when ✱9·13 closes a real
variable in an enriched order-two matrix. -/
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
