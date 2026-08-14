namespace PM.RamifiedSyntax

/-- A kernel-only proof of idempotence, used in syntax casts.  The core
`Nat.max_self` theorem is currently proved through the simplifier and therefore
carries `propext`, even though this equality is computational. -/
theorem natMaxSelf (order : Nat) : max order order = order := by
  unfold Max.max Nat.instMax maxOfLe
  change (if order ≤ order then order else order) = order
  rw [if_pos (Nat.le_refl order)]

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

def equivalence (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature realCtx apparent order) :
    Formula signature realCtx apparent order :=
  .neg negation
    (implication negation disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left)))

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

def sameDisjunction (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  Eq.mp (congrArg (Formula signature real apparent) (natMaxSelf order))
    (.disj
      (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
        disjunction)
      left right)

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

/- PM's ramified deduction judgement.  At ✱12 a certificate exhibits a
predicative function, and a separate premise derives its pointwise
equivalence before the existential assertion may be introduced. -/
inductive Derivation {signature : Signature} :
    {real : Context} → Claim signature real → Prop where
  | star_1_1 {order : Nat}
      {p q : Formula signature [] [] order}
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order) :
      Derivation (.assertion p) →
      Derivation (.assertion (implication negation disjunction p q)) →
      Derivation (.assertion q)
  | star_1_11 {real : Context} {realSort : RSort} {order : Nat}
      {p q : Formula signature (realSort :: real) [] order}
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order) :
      Derivation (.assertion p) →
      Derivation (.assertion (implication negation disjunction p q)) →
      Derivation (.assertion q)
  | star_1_2 {order : Nat} (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (p : Formula signature real [] order) :
      Derivation (.assertion
        (implication negation disjunction (sameDisjunction disjunction p p) p))
  | star_1_3 {order : Nat}
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (p q : Formula signature real [] order) :
      Derivation (.assertion (implication negation disjunction q
        (sameDisjunction disjunction p q)))
  | star_1_4 {order : Nat}
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (p q : Formula signature real [] order) :
      Derivation (.assertion (implication negation disjunction
        (sameDisjunction disjunction p q) (sameDisjunction disjunction q p)))
  | star_1_5 {order : Nat}
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (p q r : Formula signature real [] order) :
      Derivation (.assertion (implication negation disjunction
        (sameDisjunction disjunction p (sameDisjunction disjunction q r))
        (sameDisjunction disjunction q (sameDisjunction disjunction p r))))
  | star_1_6 {order : Nat}
      (negation : signature.Negation order)
      (disjunction : signature.Disjunction order)
      (p q r : Formula signature real [] order) :
      Derivation (.assertion (implication negation disjunction
        (implication negation disjunction q r)
        (implication negation disjunction
          (sameDisjunction disjunction p q) (sameDisjunction disjunction p r))))
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
  | star_9_12 {leftOrder rightOrder : Nat}
      {p : Formula signature real [] leftOrder}
      {q : Formula signature real [] rightOrder}
      (negation : signature.Negation leftOrder)
      (disjunction : signature.Disjunction (max leftOrder rightOrder)) :
      Derivation (.assertion p) →
      Derivation (.assertion (mixedImplication negation disjunction p q)) →
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

/-- The same-order instance retained for existing printed uses of ✱9·12. -/
theorem Derivation.star_9_12_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    {p q : Formula signature real [] order}
    (line1 : Derivation (.assertion p))
    (line2 : Derivation (.assertion
      (implication negation disjunction p q))) :
    Derivation (.assertion q) := by
  apply Derivation.star_9_12 negation
    (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction)
    line1
  exact Derivation.uncastAssertionOrder (natMaxSelf order)
    (mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm) disjunction)
      p q) line2

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
  let rawLine := Derivation.star_1_3 negation disjunction p.weakenReal
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
