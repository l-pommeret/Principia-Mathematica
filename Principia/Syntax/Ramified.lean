namespace PM.RamifiedSyntax

/-- A kernel-only proof of idempotence, used in syntax casts.  The core
`Nat.max_self` theorem is currently proved through the simplifier and therefore
carries `propext`, even though this equality is computational. -/
theorem natMaxSelf (order : Nat) : max order order = order := by
  unfold Max.max Nat.instMax maxOfLe
  change (if order ≤ order then order else order) = order
  rw [if_pos (Nat.le_refl order)]

/-- If both inputs to `max` are identified with one order, its result is
identified with that order too.  This equality is assembled solely from the
given identifications and the kernel-only `natMaxSelf` proof. -/
theorem natMaxCongr
    {leftOrder rightOrder order : Nat}
    (leftEq : leftOrder = order)
    (rightEq : rightOrder = order) :
    max leftOrder rightOrder = order := by
  cases leftEq
  cases rightEq
  exact natMaxSelf _

/-!
# Pure ramified object syntax

This module supplies the intrinsically typed syntax needed from PM I, ✱9
onwards.  No constructor contains a Lean predicate or function.  Class and
relation abstractions, and descriptions, are incomplete symbols: their
numbered definitions expand contextually and they never become `Term`
constructors.
-/

universe u

/-- Ramified object sorts.  A propositional-function sort records its full
argument vector, the order of its values, and its excess over the predicative
order. -/
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

/-- Intrinsically sorted de Bruijn variables. -/
inductive Var : Context → RSort → Type where
  | zero : Var (sort :: context) sort
  | succ : Var context sort → Var (other :: context) sort

/-- Pure leaves and explicitly ordered logical meanings. -/
structure Signature where
  Symbol : RSort → Type u
  Negation : Nat → Type u
  Disjunction : Nat → Type u
  Universal : RSort → Nat → Type u
  Existential : RSort → Nat → Type u

/-- Genuine terms.  In particular there is no abstraction or description
constructor here. -/
inductive Term (signature : Signature) (real apparent : Context) : RSort → Type u where
  | real : Var real sort → Term signature real apparent sort
  | apparent : Var apparent sort → Term signature real apparent sort
  | symbol : signature.Symbol sort → Term signature real apparent sort

/-- An intrinsically sorted argument vector. -/
inductive Arguments (signature : Signature) (real apparent : Context) :
    List RSort → Type u where
  | nil : Arguments signature real apparent []
  | cons : Term signature real apparent sort →
      Arguments signature real apparent sorts →
      Arguments signature real apparent (sort :: sorts)

/-- The least order introduced by binding a variable of `sort`. -/
def bindOrder (matrixOrder : Nat) (sort : RSort) : Nat :=
  max matrixOrder (Nat.succ sort.height)

/-! Kernel-only arithmetic used to compare the order computed before and
after a scope extension.  These proofs deliberately avoid the corresponding
library normalization theorems. -/

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

/-- The printed existential sign together with its eliminable ✱10·01
expansion.  The two negations have different assigned orders in the
intrinsically ordered syntax. -/
structure ExistentialVocabulary (signature : Signature)
    (sort : RSort) (matrixOrder : Nat) where
  printed : signature.Existential sort matrixOrder
  matrixNegation : signature.Negation matrixOrder
  universal : signature.Universal sort matrixOrder
  outerNegation : signature.Negation (bindOrder matrixOrder sort)

/-- A contextual incomplete symbol.  `parameters` are bound in its defining
matrix and the resulting function candidate is bound in the continuation. -/
inductive IncompleteKind where
  | abstraction
  | description

/-- Ramified formulae.  The contextual nodes remain available for recording
unexpanded printed surface syntax; PM's numbered `Df` declarations below do
not produce them, but reduce directly to primitive quantifier syntax. -/
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

/-- ✱10·01: `(∃x).φx .=. ∼(x).∼φx` (Df).  The existential sign is retained
in the vocabulary for the printed reading, but contributes no syntax node. -/
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

/-- The typed transposition of the two nearest apparent variables.  The two
sorts may be different; variables below them retain both index and sort. -/
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

/-- Transport a formula across the typed transposition of its two nearest
apparent variables. -/
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

/-- Simultaneous capture-avoiding substitution.  Every binder case lifts the
substitution, fixing the new index zero and weakening all substituted terms. -/
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

/-- Substitution replacing the nearest binder; all older variables are
lowered by one. -/
def instantiateSubstitution (argument : Term signature realCtx apparent sort) :
    Substitution signature realCtx (sort :: apparent) apparent
  | _, .zero => argument
  | _, .succ v => .apparent v

def Formula.instantiate
    (body : Formula signature realCtx (sort :: apparent) order)
    (argument : Term signature realCtx apparent sort) :
    Formula signature realCtx apparent order :=
  body.substitute (instantiateSubstitution argument)

/-- Universal closure of a two-variable matrix.  The head variable is bound
first, followed by the next variable. -/
def Formula.always₂
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort (bindOrder matrixOrder leftSort))
    (body : Formula signature realCtx
      (leftSort :: rightSort :: apparent) matrixOrder) :
    Formula signature realCtx apparent
      (bindOrder (bindOrder matrixOrder leftSort) rightSort) :=
  .always outer (.always inner body)

/-- Exact simultaneous-looking specialization of a two-variable matrix.
It is deliberately computed from `body`, rather than accepting an unrelated
formula as the purported instance. -/
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

/-- The defining binder equation is the formal capture-avoidance guarantee:
the fresh bound variable is fixed while every replacement crosses it. -/
theorem substitute_always
    (sigma : Substitution signature realCtx source target)
    (meaning : signature.Universal sort matrixOrder)
    (body : Formula signature realCtx (sort :: source) matrixOrder) :
    (Formula.always meaning body).substitute sigma =
      .always meaning (body.substitute (liftSubstitution sigma)) := rfl

/-- Intrinsic well-formation stability for terms. -/
theorem substitute_preserves_term_sort
    (sigma : Substitution signature realCtx source target)
    (term : Term signature realCtx source sort) :
    ∃ output : Term signature realCtx target sort,
      output = term.substitute sigma := ⟨term.substitute sigma, rfl⟩

/-- Intrinsic well-formation stability for formulae, including incomplete
symbol scopes.  Both context and assigned order are preserved in the type. -/
theorem substitute_preserves_formula_order
    (sigma : Substitution signature realCtx source target)
    (formula : Formula signature realCtx source order) :
    ∃ output : Formula signature realCtx target order,
      output = formula.substitute sigma := ⟨formula.substitute sigma, rfl⟩

/-- Substitution after renaming, expressed as one substitution. -/
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

/-- Renaming/substitution fusion.  In particular this proves that a binder
transposition commutes with every subsequent capture-avoiding substitution. -/
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

/-- Swapping the two nearest binders preserves their sorts by construction. -/
theorem swapHeads_preserves_term_sort
    (term : Term signature realCtx
      (leftSort :: rightSort :: apparent) sort) :
    ∃ output : Term signature realCtx
        (rightSort :: leftSort :: apparent) sort,
      output = term.rename swapHeadsRenaming :=
  ⟨term.rename swapHeadsRenaming, rfl⟩

/-- Swapping the two nearest binders preserves the assigned formula order. -/
theorem swapHeads_preserves_formula_order
    (formula : Formula signature realCtx
      (leftSort :: rightSort :: apparent) order) :
    ∃ output : Formula signature realCtx
        (rightSort :: leftSort :: apparent) order,
      output = formula.swapHeads :=
  ⟨formula.swapHeads, rfl⟩

/-- Concrete substitution law for the heterogeneous head transposition. -/
theorem Formula.swapHeads_substitute
    (formula : Formula signature realCtx
      (leftSort :: rightSort :: apparent) order)
    (sigma : Substitution signature realCtx
      (rightSort :: leftSort :: apparent) target) :
    formula.swapHeads.substitute sigma =
      formula.substitute
        (substitutionAfterRenaming swapHeadsRenaming sigma) := by
  exact Formula.rename_substitute swapHeadsRenaming sigma formula

/-! ## PM's incomplete symbols and definitions -/

def classSort (resultOrder excess : Nat) : RSort :=
  .function [.individual] resultOrder excess

def relationSort (resultOrder excess : Nat) : RSort :=
  .function [.individual, .individual] resultOrder excess

/-- Application `phi!(x)` is ordinary intrinsically typed application. -/
def applyUnary
    (function : Term signature realCtx apparent (.function [argument] order excess))
    (term : Term signature realCtx apparent argument) :
    Formula signature realCtx apparent order :=
  .apply function (.cons term .nil)

/-- Application `phi!(x,y)`. -/
def applyBinary
    (function : Term signature realCtx apparent
      (.function [leftSort, rightSort] order excess))
    (left : Term signature realCtx apparent leftSort)
    (right : Term signature realCtx apparent rightSort) :
    Formula signature realCtx apparent order :=
  .apply function (.cons left (.cons right .nil))

/-! ### The eliminable definitions of PM I, ✱9·01–·08

PM explicitly says that the apparent variable in these expressions has the
whole asserted proposition as its real scope.  Accordingly, the left-hand
printed forms below are represented by reducible abbreviations whose bodies
are exactly the expanded right-hand sides.  They are syntax, not rules of
`Derivation`.
-/

/-- ✱9·01: `∼{(x).φx} = (∃x).∼φx` (Df). -/
def star_9_01
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent (bindOrder matrixOrder argument) :=
  .sometimes existential (.neg negation body)

/-- ✱9·02: `∼{(∃x).φx} = (x).∼φx` (Df). -/
def star_9_02
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent (bindOrder matrixOrder argument) :=
  .always universal (.neg negation body)

/-- ✱9·03: `(x).φx ∨ p := (x).φx ∨ p` (Df), with the right occurrence
of `p` weakened across the binder. -/
def star_9_03
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    Formula signature real apparent
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  .always universal
    (.disj disjunction body (fixed.rename (fun v => .succ v)))

/-- ✱9·04: `p ∨ (x).φx := (x).p ∨ φx` (Df). -/
def star_9_04
    (universal : signature.Universal argument (max fixedOrder matrixOrder))
    (disjunction : signature.Disjunction (max fixedOrder matrixOrder))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .always universal
    (.disj disjunction (fixed.rename (fun v => .succ v)) body)

/-- ✱9·05: `(∃x).φx ∨ p := (∃x).φx ∨ p` (Df). -/
def star_9_05
    (existential : ExistentialVocabulary signature argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (body : Formula signature real (argument :: apparent) matrixOrder)
    (fixed : Formula signature real apparent fixedOrder) :
    Formula signature real apparent
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  .sometimes existential
    (.disj disjunction body (fixed.rename (fun v => .succ v)))

/-- ✱9·06: `p ∨ (∃x).φx := (∃x).p ∨ φx` (Df). -/
def star_9_06
    (existential : ExistentialVocabulary signature argument (max fixedOrder matrixOrder))
    (disjunction : signature.Disjunction (max fixedOrder matrixOrder))
    (fixed : Formula signature real apparent fixedOrder)
    (body : Formula signature real (argument :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .sometimes existential
    (.disj disjunction (fixed.rename (fun v => .succ v)) body)

/-- ✱9·07: `(x).φx ∨ (∃y).ψy := (x)(∃y).φx ∨ ψy` (Df).
The two-variable matrix has binder order `y, x`, matching the constructors. -/
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

/-- ✱9·08: `(∃y).ψy ∨ (x).φx := (x)(∃y).ψy ∨ φx` (Df). -/
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

/-! ### Constructor audit for the proposed scope equalities

The six printed Df clauses cannot be installed as Lean equalities between the
two independently built `Formula` trees.  The following declarations make
that obstruction kernel-visible.  They compare the reducible scope expansion
above with the literal outer-connective tree printed on the other side. -/

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

/-- Constructor obstruction for printed ✱9·01,
`∼{(x).φx} = (∃x).∼φx`: the right expansion contains two additional
`Formula.neg` nodes below the common `neg (always ...)` prefix. -/
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

/-- Constructor obstruction for printed ✱9·02,
`∼{(∃x).φx} = (x).∼φx`: the literal left tree is rooted at
`Formula.neg`, while the scope expansion is rooted at `Formula.always`. -/
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

/-- Constructor obstruction for printed ✱9·03,
`(x).φx ∨ p = (x). φx ∨ p`: after the assigned-order cast, the literal
left tree is rooted at `Formula.disj`, while `star_9_03` is rooted at
`Formula.always`. -/
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

/-- Constructor obstruction for printed ✱9·04,
`p ∨ (x).φx = (x). p ∨ φx`: after the assigned-order cast, the literal
left tree is rooted at `Formula.disj`, while `star_9_04` is rooted at
`Formula.always`. -/
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

/-- Constructor obstruction for printed ✱9·05,
`(∃x).φx ∨ p = (∃x). φx ∨ p`: after the assigned-order cast, the literal
left tree is rooted at `Formula.disj`, while `star_9_05` unfolds to a
`Formula.neg` root. -/
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

/-- Constructor obstruction for printed ✱9·06,
`p ∨ (∃x).φx = (∃x). p ∨ φx`: after the assigned-order cast, the literal
left tree is rooted at `Formula.disj`, while `star_9_06` unfolds to a
`Formula.neg` root. -/
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

/-- ✱10·01: `(∃x).φx .=. ∼(x).∼φx` (Df). -/
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

/-- Membership `x ε alpha` is the definitional application `alpha!x`. -/
def membership
    (term : Term signature realCtx apparent .individual)
    (classTerm : Term signature realCtx apparent (classSort order excess)) :
    Formula signature realCtx apparent order :=
  applyUnary classTerm term

/-- The logical meanings required to unfold Leibniz identity at one assigned
order.  This is explicit syntax data, not an axiom identifying meanings. -/
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

/-- The object formula printed at ✱11·1: `(x,y).φ(x,y) ⊃ φ(z,w)`.
The consequent is the exact specialization of the matrix in the antecedent. -/
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

/-- The object formula described by primitive proposition ✱11·07.  Its
consequent closes the same matrix after the typed exchange of its binders. -/
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

/-- Conjunction at possibly different ramified orders, expressed through the
primitive negation and disjunction vocabulary. -/
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

/-- ✱3·01 at one assigned order. -/
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

/-- ✱4·01: equivalence is the conjunction of both implications. -/
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

/-- The matrix in PM's primitive proposition ✱10·1 has its original order,
while its universal closure has the order introduced by binding `x`.
Disjunction computes the order of `(x).φx ⊃ φy` as the maximum of both. -/
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

/-- Typed witness for the exact ✱11·1 shape. -/
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

/-- Typed witness for ✱11·07 with potentially heterogeneous binders. -/
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

/-- ✱13·01: Leibniz identity, `x = y .:=: (φ) : φ!x ⊃ φ!y`.
Identity is therefore a reducible definition, not an atomic constructor. -/
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

/-- ✱20·01: `f{ẑ(ψz)}` is the eliminable expansion
`(∃φ) : (x).φ!x ≡ ψx : f{φ!ẑ}`.  The witness sort has excess zero: the
exclamation mark in PM requires a predicative function. -/
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

/-- ✱20·02: `x ε (φ!ẑ) = φ!x` (Df). -/
def star_20_02
    (predicate : Term signature realCtx apparent (classSort resultOrder 0))
    (x : Term signature realCtx apparent .individual) :
    Formula signature realCtx apparent resultOrder :=
  applyUnary predicate x

theorem star_20_02_unfold
    (predicate : Term signature realCtx apparent (classSort resultOrder 0))
    (x : Term signature realCtx apparent .individual) :
    star_20_02 predicate x = applyUnary predicate x := rfl

/-- ✱21·01: contextual binary relation abstraction. -/
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

/-- ✱14·01: a description has only contextual scope; it is not a term. -/
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

/-- ✱14·02: `E!(ιx)(φx)` unfolds to the existential closure of its
uniqueness matrix.  Construction of that matrix (including ✱13·01 identity)
is kept explicit because its ramified order is part of its type. -/
def star_14_02
    (existential : ExistentialVocabulary signature sort uniquenessOrder)
    (uniquenessMatrix :
      Formula signature realCtx (sort :: apparent) uniquenessOrder) :
    Formula signature realCtx apparent (bindOrder uniquenessOrder sort) :=
  .sometimes existential uniquenessMatrix

/-! ## Reducibility formulae and the heterogeneous PM deduction judgement -/

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

/-- The three kinds of statement to which PM's primitive propositions apply.
`significance` and `functionExistence` are deliberately not formulae: they
record the matrix about which the corresponding metalinguistic statement is
made. -/
inductive Claim (signature : Signature) (real : Context) where
  | assertion {order : Nat} (formula : Formula signature real [] order)
  | significance {argument : RSort} {order : Nat}
      (matrix : Formula signature real [argument] order)
  | functionExistence {argument : RSort} {order : Nat}
      (matrix : Formula signature real [argument] order)

/-- A catalogue reading ties PM's typography to the heterogeneous claim. -/
structure ClaimReading (signature : Signature) (real : Context) where
  printed : String
  parsed : Claim signature real

/-- A predicative unary-function witness, retained for derived interfaces. -/
def UnaryReducibility
    {real : Context} {argument : RSort} {order : Nat}
    (_phi : Formula signature real [argument] order) :=
  { _function : Term signature real [] (.function [argument] order 0) //
    RSort.Predicative (.function [argument] order 0) }

/-- A predicative binary-function witness, retained for derived interfaces. -/
def BinaryReducibility
    {real : Context} {leftSort rightSort : RSort} {order : Nat}
    (_phi : Formula signature real [leftSort, rightSort] order) :=
  { _function : Term signature real []
      (.function [leftSort, rightSort] order 0) //
    RSort.Predicative (.function [leftSort, rightSort] order 0) }

/-- A heterogeneous disjunction whose two member orders are identified with
one common order normalizes to the established mono-order abbreviation.  The
equalities are explicit, so this lemma cannot transport a formula between
unrelated ramified orders. -/
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

/-- A heterogeneous implication whose two member orders are identified with
one common order normalizes to the established mono-order abbreviation.  It
only commutes the casts forced by those equalities through the printed
negation/disjunction tree; it is not an inter-order formula cast. -/
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

/-- The printed surface form of ✱9·34.  By the scope convention established
by ✱9·01–·08 its eliminable expansion is the universal closure of the
elementary ✱1·3 matrix. -/
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

/-! ### The printed meaning of implication at quantified scope

At ✱9·12 PM uses the word *implied*, not one selected constructor tree.
The following relations record the eliminable readings by which ✱1·01 and
✱9·01--·08 turn that printed implication into a ramified `Formula`.
They are syntax certificates only; they add no rule to `Derivation`. -/

/-- A certificate that the second formula is the printed negation of the
first.  The elementary case is ✱1·01; the quantified cases are the two
negation definitions ✱9·01 and ✱9·02. -/
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

/-- The insertion retaining the old head variable when a second apparent
variable is added.  It is the right-matrix renaming in ✱9·07--·08. -/
def implicationScopeHead :
    Renaming (head :: apparent) (head :: tail :: apparent)
  | _, .zero => .zero
  | _, .succ v => .succ (.succ v)

/-- A certificate that the third formula is the printed disjunction of the
first two.  The first two constructors give ✱1·01; the six scope
constructors bear the exact names of ✱9·03--·08.  The recursive premises in
✱9·03--·06 express repeated full-scope propagation without identifying two
different surface members. -/
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

/-- `formula` is an implication of `p` to `q` in PM's printed sense.  The
surface `∼` and `∨` are retained as indices even when ✱9·01--·08 eliminate
them from the root of the resulting ramified tree. -/
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

/-- The automatically inferred ✱1·01 reading preserves every existing
elementary use of ✱9·12. -/
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

/-- The nested elementary reading keeps `Syll` applications inferable even
when their antecedent has been named by a local `let`.  It is still only the
same ✱1·01 computation at the outer implication. -/
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

/- PM's ramified deduction judgement.  At ✱12 a certificate exhibits a
predicative function, and a separate premise derives its pointwise
equivalence before the existential assertion may be introduced. -/
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
      (r : Formula signature real [] rOrder) :
      Derivation (.assertion
        (mixedImplication outerNegation outerDisjunction
          (mixedImplication qNegation qrDisjunction q r)
          (mixedImplication pqNegation innerDisjunction
            (.disj pqDisjunction p q) (.disj prDisjunction p r))))
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
  /-- ✱9·12. "What is implied by a true premiss is true. Pp."
  `ImplicationReading` makes PM's word "implied" explicit: at elementary
  scope it is ✱1·01, while quantified scope is read through ✱9·01--·08. -/
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

/-- Assertion notation for the ramified PM judgement. -/
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

/-- Transport a derivation only along a proved equality of its formula order.
Unlike a formula cast between arbitrary indices, this preserves the ramified
order and merely exposes the `Eq.mp` already forced by that equality. -/
private theorem Derivation.castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

/-- The mono-order specialization of primitive ✱1·1.  It is retained for the
existing propositional corpus while the constructor itself remains typically
ambiguous in the orders of `p` and `q`. -/
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

/-- The mono-order specialization of primitive ✱1·11 at a nonempty real
context.  Its proof is the same equality-controlled normalization as ✱1·1. -/
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

/-- Equality-controlled normalization of the heterogeneous syntax of ✱1·3
when its two propositional variables happen to have the same order.  The
transport removes only the `max` indices proved equal by `natMaxSelf`; it is
not a cast between arbitrary ramified orders. -/
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

/-- The mono-order specialization of the typically ambiguous primitive
✱1·3.  Existing derived propositions use this theorem, while the constructor
retains independent orders for `p` and `q`. -/
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

/-- Equality-controlled normalization of heterogeneous ✱1·4 at one common
order.  Each disjunction is normalized separately before the outer
implication; every transport is justified by a `max` equality. -/
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

/-- The mono-order specialization of the typically ambiguous primitive
✱1·4.  It preserves the established API without restricting the primitive
constructor itself. -/
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

/-- Equality-controlled normalization of heterogeneous ✱1·5 at one common
order.  The proof follows the syntax tree from the two inner disjunctions to
their parents and finally to the outer implication, using only proved `max`
equalities. -/
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

/-- The mono-order specialization of the typically ambiguous primitive
✱1·5, obtained by the targeted tree normalization above. -/
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

/-- Equality-controlled normalization of heterogeneous ✱1·6 at one common
order.  It normalizes the antecedent implication, the two disjunctions, the
consequent implication, and finally the outer implication in that order. -/
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

/-- The mono-order specialization of the typically ambiguous primitive
✱1·6, obtained without any generic conversion between formula orders. -/
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

/-- The same-order instance retained for existing printed uses of ✱9·12. -/
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

/-! ### Instantiating a formula that has no apparent variable

PM's ✱9 lifting rules (✱9·11–✱9·13) state their premise on the matrix with the
apparent variable already replaced by a real one.  A demonstration in the style
of ✱9·34 therefore has to know that the parts of the matrix carrying no apparent
variable — the `p` of `p ∨ φx` — come back from that replacement unchanged.
That is what the following three lemmas establish, and without them the printed
two-stage route cannot be written down at all. -/

/-- Pointwise identity on apparent variables. -/
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

/-- Lifting preserves being pointwise the identity: the fresh binder goes to
itself, and every older variable keeps its (unchanged) image weakened. -/
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

/-- Weakening the real context touches only real variables, so it commutes with
every renaming of the apparent ones. -/
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

/-- Substitution distributes through the same-order implication abbreviation,
including the casts introduced by `Nat.max_self`. -/
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

/-- Weakening the real context distributes through the same-order implication
abbreviation, including the casts introduced by `Nat.max_self`. -/
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

/-- Substitution distributes through the same-order disjunction abbreviation,
including the casts introduced by `Nat.max_self`. -/
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

/-- Weakening the real context distributes through the same-order disjunction
abbreviation, including the casts introduced by `Nat.max_self`. -/
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

/-- The lemma the ✱9 lifting rules actually need.  A formula with no apparent
variable, pushed under a binder and then instantiated, is returned unchanged:
`p` in `⊢ : φx . ⊃ . p ∨ φx` survives ✱9·13 untouched. -/
@[simp] theorem Formula.closed_weakenReal_instantiate
    (p : Formula signature real [] order)
    (argument : RSort) (value : Term signature (argument :: real) [] argument) :
    ((p.rename (fun v => .succ v) : Formula signature real [argument] order).weakenReal
        (fresh := argument)).instantiate value
      = p.weakenReal := by
  rw [Formula.weakenReal_rename, Formula.instantiate, Formula.rename_substitute]
  exact Formula.substitute_eq_self _ (fun v => nomatch v)

/-- Substitution-level form of `closed_weakenReal_instantiate`, used after an
outer instantiation has distributed through logical abbreviations. -/
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

/-- ✱9·34, following the printed two-stage core: ✱1·3 on the matrix,
then ✱9·13, with the final surface form supplied only by the unfolding Df. -/
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
