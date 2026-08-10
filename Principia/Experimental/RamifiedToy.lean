import Principia.Syntax.Formula

namespace PM.Experimental.RamifiedToy

/-!
# Experimental ramified-type vertical slice

This is an architectural experiment, not a formal edition of any numbered PM
proposition. Declarations mentioning `star_9` or `star_10` test rule shapes
only. Object propositions are syntax; Lean `Prop` is used only for the
metalinguistic derivability judgement.
-/

/-- A function records argument types, result-proposition order, and its
excess above the least compatible (predicative) order. -/
inductive RamifiedSort where
  | individual
  | proposition (order : Nat)
  | function (arguments : List RamifiedSort) (resultOrder excess : Nat)

namespace RamifiedSort

mutual
  def height : RamifiedSort → Nat
    | .individual => 0
    | .proposition order => order
    | .function arguments resultOrder excess =>
        max (Nat.succ (maxHeight arguments)) (Nat.succ resultOrder) + excess

  def maxHeight : List RamifiedSort → Nat
    | [] => 0
    | argument :: arguments => max (height argument) (maxHeight arguments)
end

def minimumFunctionOrder (arguments : List RamifiedSort) (resultOrder : Nat) : Nat :=
  max (Nat.succ (maxHeight arguments)) (Nat.succ resultOrder)

def Predicative : RamifiedSort → Prop
  | .function _ _ 0 => True
  | _ => False

end RamifiedSort

abbrev RealContext := List RamifiedSort
abbrev ApparentContext := List RamifiedSort

inductive Var : List RamifiedSort → RamifiedSort → Type where
  | zero : Var (sort :: context) sort
  | succ : Var context sort → Var (other :: context) sort

/-- Connective meanings exist only at explicitly assigned orders. -/
structure Signature where
  Symbol : RamifiedSort → Type
  NegationMeaning : Nat → Type
  DisjunctionMeaning : Nat → Nat → Type

inductive Term (signature : Signature) (realContext : RealContext)
    (apparentContext : ApparentContext) : RamifiedSort → Type where
  | real : Var realContext sort → Term signature realContext apparentContext sort
  | apparent : Var apparentContext sort → Term signature realContext apparentContext sort
  | symbol : signature.Symbol sort → Term signature realContext apparentContext sort

/-- Full applications are intrinsically typed by their argument vector. -/
inductive Arguments (signature : Signature) (realContext : RealContext)
    (apparentContext : ApparentContext) : List RamifiedSort → Type where
  | nil : Arguments signature realContext apparentContext []
  | cons : Term signature realContext apparentContext sort →
      Arguments signature realContext apparentContext sorts →
      Arguments signature realContext apparentContext (sort :: sorts)

def bindOrder (matrixOrder : Nat) (sort : RamifiedSort) : Nat :=
  max matrixOrder (Nat.succ sort.height)

inductive Formula (signature : Signature) (realContext : RealContext) :
    ApparentContext → Nat → Type where
  | propositionVariable :
      Term signature realContext apparentContext (.proposition order) →
      Formula signature realContext apparentContext order
  | apply :
      Term signature realContext apparentContext (.function sorts resultOrder excess) →
      Arguments signature realContext apparentContext sorts →
      Formula signature realContext apparentContext resultOrder
  | neg : signature.NegationMeaning order →
      Formula signature realContext apparentContext order →
      Formula signature realContext apparentContext order
  | disj : signature.DisjunctionMeaning leftOrder rightOrder →
      Formula signature realContext apparentContext leftOrder →
      Formula signature realContext apparentContext rightOrder →
      Formula signature realContext apparentContext (max leftOrder rightOrder)
  | always : Formula signature realContext (sort :: apparentContext) matrixOrder →
      Formula signature realContext apparentContext (bindOrder matrixOrder sort)
  | sometimes : Formula signature realContext (sort :: apparentContext) matrixOrder →
      Formula signature realContext apparentContext (bindOrder matrixOrder sort)

abbrev ApparentRenaming (source target : ApparentContext) :=
  {sort : RamifiedSort} → Var source sort → Var target sort

abbrev RealRenaming (source target : RealContext) :=
  {sort : RamifiedSort} → Var source sort → Var target sort

def liftApparentRenaming (rho : ApparentRenaming source target) :
    ApparentRenaming (sort :: source) (sort :: target)
  | _, .zero => .zero
  | _, .succ entryVar => .succ (rho entryVar)

def Term.renameApparent (rho : ApparentRenaming source target) :
    Term signature realContext source sort → Term signature realContext target sort
  | .real entryVar => .real entryVar
  | .apparent entryVar => .apparent (rho entryVar)
  | .symbol payload => .symbol payload

def Arguments.renameApparent (rho : ApparentRenaming source target) :
    Arguments signature realContext source sorts →
      Arguments signature realContext target sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons (argument.renameApparent rho)
        (arguments.renameApparent rho)

def Formula.renameApparent (rho : ApparentRenaming source target) :
    Formula signature realContext source order → Formula signature realContext target order
  | .propositionVariable entryVar =>
      .propositionVariable (entryVar.renameApparent rho)
  | .apply function arguments =>
      .apply (function.renameApparent rho)
        (arguments.renameApparent rho)
  | .neg meaning proposition => .neg meaning (Formula.renameApparent rho proposition)
  | .disj meaning left right =>
      .disj meaning (Formula.renameApparent rho left) (Formula.renameApparent rho right)
  | .always body => .always (Formula.renameApparent (liftApparentRenaming rho) body)
  | .sometimes body =>
      .sometimes (Formula.renameApparent (liftApparentRenaming rho) body)

def weakenApparent (term : Term signature realContext apparentContext sort) :
    Term signature realContext (fresh :: apparentContext) sort :=
  term.renameApparent (fun entryVar => .succ entryVar)

def Term.renameReal (rho : RealRenaming source target) :
    Term signature source apparentContext sort → Term signature target apparentContext sort
  | .real entryVar => .real (rho entryVar)
  | .apparent entryVar => .apparent entryVar
  | .symbol payload => .symbol payload

def Arguments.renameReal (rho : RealRenaming source target) :
    Arguments signature source apparentContext sorts →
      Arguments signature target apparentContext sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons (argument.renameReal rho) (arguments.renameReal rho)

def Formula.renameReal (rho : RealRenaming source target) :
    Formula signature source apparentContext order → Formula signature target apparentContext order
  | .propositionVariable entryVar => .propositionVariable (entryVar.renameReal rho)
  | .apply function arguments =>
      .apply (function.renameReal rho) (arguments.renameReal rho)
  | .neg meaning proposition => .neg meaning (Formula.renameReal rho proposition)
  | .disj meaning left right =>
      .disj meaning (Formula.renameReal rho left) (Formula.renameReal rho right)
  | .always body => .always (Formula.renameReal rho body)
  | .sometimes body => .sometimes (Formula.renameReal rho body)

def Formula.weakenReal (proposition : Formula signature realContext apparentContext order) :
    Formula signature (fresh :: realContext) apparentContext order :=
  Formula.renameReal (fun entryVar => .succ entryVar) proposition

abbrev ApparentSubstitution (signature : Signature) (realContext : RealContext)
    (source target : ApparentContext) :=
  {sort : RamifiedSort} → Var source sort → Term signature realContext target sort

def liftSubstitution
    (substitution : ApparentSubstitution signature realContext source target) :
    ApparentSubstitution signature realContext (sort :: source) (sort :: target)
  | _, .zero => .apparent .zero
  | _, .succ entryVar => weakenApparent (substitution entryVar)

def Term.substitute
    (substitution : ApparentSubstitution signature realContext source target) :
    Term signature realContext source sort → Term signature realContext target sort
  | .real entryVar => .real entryVar
  | .apparent entryVar => substitution entryVar
  | .symbol payload => .symbol payload

def Arguments.substitute
    (substitution : ApparentSubstitution signature realContext source target) :
    Arguments signature realContext source sorts →
      Arguments signature realContext target sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons (argument.substitute substitution)
        (arguments.substitute substitution)

def Formula.substitute
    (substitution : ApparentSubstitution signature realContext source target) :
    Formula signature realContext source order → Formula signature realContext target order
  | .propositionVariable entryVar =>
      .propositionVariable (entryVar.substitute substitution)
  | .apply function arguments =>
      .apply (function.substitute substitution)
        (arguments.substitute substitution)
  | .neg meaning proposition => .neg meaning (Formula.substitute substitution proposition)
  | .disj meaning left right =>
      .disj meaning (Formula.substitute substitution left) (Formula.substitute substitution right)
  | .always body => .always (Formula.substitute (liftSubstitution substitution) body)
  | .sometimes body => .sometimes (Formula.substitute (liftSubstitution substitution) body)

def instantiateSubstitution (argument : Term signature realContext apparentContext sort) :
    ApparentSubstitution signature realContext (sort :: apparentContext) apparentContext
  | _, .zero => argument
  | _, .succ entryVar => .apparent entryVar

def Formula.instantiate (body : Formula signature realContext (sort :: apparentContext) order)
    (argument : Term signature realContext apparentContext sort) :
    Formula signature realContext apparentContext order :=
  Formula.substitute (instantiateSubstitution argument) body

inductive HeadOccurrence (realContext : RealContext) (apparentContext : ApparentContext)
    (sort : RamifiedSort) where
  | real : Var realContext sort → HeadOccurrence realContext apparentContext sort
  | apparent : Var apparentContext sort → HeadOccurrence realContext apparentContext sort

def abstractHeadVar : Var (head :: realContext) sort →
    HeadOccurrence realContext (head :: apparentContext) sort
  | .zero => .apparent .zero
  | .succ entryVar => .real entryVar

def valueHeadVar : Var (head :: apparentContext) sort →
    HeadOccurrence (head :: realContext) apparentContext sort
  | .zero => .real .zero
  | .succ entryVar => .apparent entryVar

/-- Move the head realContext entryVar into a fresh apparentContext-entryVar position. -/
def Term.abstractHead {signature : Signature} {head sort : RamifiedSort}
    {realContext : RealContext} {apparentContext : ApparentContext} :
    Term signature (head :: realContext) apparentContext sort →
      Term signature realContext (head :: apparentContext) sort
  | .real entryVar =>
      match abstractHeadVar (apparentContext := apparentContext) entryVar with
      | .real retained => .real retained
      | .apparent abstracted => .apparent abstracted
  | .apparent entryVar => .apparent (.succ entryVar)
  | .symbol payload => .symbol payload

/-- Inverse operation: give the fresh apparentContext head the realContext head value. -/
def Term.valueHead {signature : Signature} {head sort : RamifiedSort}
    {realContext : RealContext} {apparentContext : ApparentContext} :
    Term signature realContext (head :: apparentContext) sort →
      Term signature (head :: realContext) apparentContext sort
  | .real entryVar => .real (.succ entryVar)
  | .apparent entryVar =>
      match valueHeadVar (realContext := realContext) entryVar with
      | .real valued => .real valued
      | .apparent retained => .apparent retained
  | .symbol payload => .symbol payload

def Arguments.abstractHead :
    Arguments signature (head :: realContext) apparentContext sorts →
      Arguments signature realContext (head :: apparentContext) sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons argument.abstractHead arguments.abstractHead

def Arguments.valueHead :
    Arguments signature realContext (head :: apparentContext) sorts →
      Arguments signature (head :: realContext) apparentContext sorts
  | .nil => .nil
  | .cons argument arguments => .cons argument.valueHead arguments.valueHead

namespace Formula

/-- Exchange the newly abstracted entryVar with an already present inner
binder.  This is the critical capture-avoidance step absent from the simpler
matrix-only operation. -/
def swapAbstractedWithBinder :
    ApparentRenaming (head :: binder :: apparentContext)
      (binder :: head :: apparentContext)
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ entryVar) => .succ (.succ entryVar)

/-- Turn the realContext entryVar at the head of the realContext context into the new head
apparentContext entryVar, preserving the proposition order and every existing
binder. -/
def abstractRealHead :
    Formula signature (head :: realContext) apparentContext order →
      Formula signature realContext (head :: apparentContext) order
  | .propositionVariable entryVar =>
      .propositionVariable entryVar.abstractHead
  | .apply function arguments =>
      .apply function.abstractHead arguments.abstractHead
  | .neg meaning proposition => .neg meaning proposition.abstractRealHead
  | .disj meaning left right =>
      .disj meaning left.abstractRealHead right.abstractRealHead
  | .always body =>
      .always (body.abstractRealHead.renameApparent swapAbstractedWithBinder)
  | .sometimes body =>
      .sometimes (body.abstractRealHead.renameApparent swapAbstractedWithBinder)

end Formula

/-- Binder-free order-zero matrices.  This is deliberately narrower than
`Formula`: the experimental ✱9 primitives cannot accept an arbitrary higher
order formula disguised as an elementary function. -/
inductive ElementaryMatrix (signature : Signature) (realContext : RealContext)
    (apparentContext : ApparentContext) : Type where
  | propositionVariable :
      Term signature realContext apparentContext (.proposition 0) →
      ElementaryMatrix signature realContext apparentContext
  | apply :
      Term signature realContext apparentContext (.function sorts 0 excess) →
      Arguments signature realContext apparentContext sorts →
      ElementaryMatrix signature realContext apparentContext
  | neg : signature.NegationMeaning 0 →
      ElementaryMatrix signature realContext apparentContext →
      ElementaryMatrix signature realContext apparentContext
  | disj : signature.DisjunctionMeaning 0 0 →
      ElementaryMatrix signature realContext apparentContext →
      ElementaryMatrix signature realContext apparentContext →
      ElementaryMatrix signature realContext apparentContext

namespace ElementaryMatrix

def toFormula : ElementaryMatrix signature realContext apparentContext →
    Formula signature realContext apparentContext 0
  | .propositionVariable entryVar => .propositionVariable entryVar
  | .apply function arguments => .apply function arguments
  | .neg meaning proposition => .neg meaning proposition.toFormula
  | .disj meaning left right => .disj meaning left.toFormula right.toFormula

def abstractHead : ElementaryMatrix signature (head :: realContext) apparentContext →
    ElementaryMatrix signature realContext (head :: apparentContext)
  | .propositionVariable entryVar => .propositionVariable entryVar.abstractHead
  | .apply function arguments =>
      .apply function.abstractHead arguments.abstractHead
  | .neg meaning proposition => .neg meaning proposition.abstractHead
  | .disj meaning left right =>
      .disj meaning left.abstractHead right.abstractHead

def valueHead : ElementaryMatrix signature realContext (head :: apparentContext) →
    ElementaryMatrix signature (head :: realContext) apparentContext
  | .propositionVariable entryVar => .propositionVariable entryVar.valueHead
  | .apply function arguments => .apply function.valueHead arguments.valueHead
  | .neg meaning proposition => .neg meaning proposition.valueHead
  | .disj meaning left right => .disj meaning left.valueHead right.valueHead

def renameReal (rho : RealRenaming source target) :
    ElementaryMatrix signature source apparentContext →
      ElementaryMatrix signature target apparentContext
  | .propositionVariable entryVar =>
      .propositionVariable (entryVar.renameReal rho)
  | .apply function arguments =>
      .apply (function.renameReal rho) (arguments.renameReal rho)
  | .neg meaning proposition => .neg meaning (renameReal rho proposition)
  | .disj meaning left right =>
      .disj meaning (renameReal rho left) (renameReal rho right)

@[simp] theorem term_value_abstract_head
    (term : Term signature (head :: realContext) apparentContext sort) :
    term.abstractHead.valueHead = term := by
  cases term with
  | real entryVar =>
      cases entryVar <;>
        simp [Term.abstractHead, Term.valueHead, abstractHeadVar, valueHeadVar]
  | apparent entryVar =>
      simp [Term.abstractHead, Term.valueHead, abstractHeadVar, valueHeadVar]
  | symbol symbol => simp [Term.abstractHead, Term.valueHead]

@[simp] theorem arguments_value_abstract_head
    (arguments : Arguments signature (head :: realContext) apparentContext sorts) :
    arguments.abstractHead.valueHead = arguments := by
  induction arguments with
  | nil => rfl
  | cons argument arguments inductionHypothesis =>
      simp [Arguments.abstractHead, Arguments.valueHead, inductionHypothesis]

@[simp] theorem value_abstract_head
    (matrix : ElementaryMatrix signature (head :: realContext) apparentContext) :
    matrix.abstractHead.valueHead = matrix := by
  induction matrix with
  | propositionVariable entryVar =>
      simp [abstractHead, valueHead]
  | apply function arguments =>
      simp [abstractHead, valueHead]
  | neg meaning proposition inductionHypothesis =>
      simp [abstractHead, valueHead, inductionHypothesis]
  | disj meaning left right leftHypothesis rightHypothesis =>
      simp [abstractHead, valueHead, leftHypothesis, rightHypothesis]

end ElementaryMatrix

/-- An elementary propositional function with one exactly typed argument. -/
structure ElementaryFunction (signature : Signature)
    (realContext : RealContext) (argument : RamifiedSort) where
  body : ElementaryMatrix signature realContext [argument]

namespace ElementaryFunction

def abstractHead
    (matrix : ElementaryMatrix signature (argument :: realContext) []) :
    ElementaryFunction signature realContext argument :=
  ⟨matrix.abstractHead⟩

def valueHead (function : ElementaryFunction signature realContext argument) :
    ElementaryMatrix signature (argument :: realContext) [] :=
  function.body.valueHead

@[simp] theorem valueHead_abstractHead
    (matrix : ElementaryMatrix signature (argument :: realContext) []) :
    valueHead (abstractHead matrix) = matrix :=
  ElementaryMatrix.value_abstract_head matrix

def weakenReal (function : ElementaryFunction signature realContext argument) :
    ElementaryFunction signature (fresh :: realContext) argument :=
  ⟨function.body.renameReal (fun entryVar => .succ entryVar)⟩

end ElementaryFunction

/-- Exactly the four assigned scope combinations needed around one binder.
The names `00`, `01`, `10`, and `11` refer to matrix/bound scope, not to an
all-orders connective. -/
structure ScopedConnectives (signature : Signature) (argument : RamifiedSort) where
  neg0 : signature.NegationMeaning 0
  neg1 : signature.NegationMeaning (bindOrder 0 argument)
  disj00Meaning : signature.DisjunctionMeaning 0 0
  disj01Meaning : signature.DisjunctionMeaning 0 (bindOrder 0 argument)
  disj10Meaning : signature.DisjunctionMeaning (bindOrder 0 argument) 0
  disj11Meaning : signature.DisjunctionMeaning
    (bindOrder 0 argument) (bindOrder 0 argument)

namespace ScopedConnectives

def disj00 (scope : ScopedConnectives signature argument)
    (left right : Formula signature realContext apparentContext 0) :
    Formula signature realContext apparentContext 0 :=
  .disj scope.disj00Meaning left right

def disj01 (scope : ScopedConnectives signature argument)
    (left : Formula signature realContext apparentContext 0)
    (right : Formula signature realContext apparentContext (bindOrder 0 argument)) :
    Formula signature realContext apparentContext (bindOrder 0 argument) :=
  .disj scope.disj01Meaning left right

def disj10 (scope : ScopedConnectives signature argument)
    (left : Formula signature realContext apparentContext (bindOrder 0 argument))
    (right : Formula signature realContext apparentContext 0) :
    Formula signature realContext apparentContext
      (max (bindOrder 0 argument) 0) :=
  Formula.disj (leftOrder := bindOrder 0 argument) (rightOrder := 0)
    scope.disj10Meaning left right

def disj11 (scope : ScopedConnectives signature argument)
    (left right : Formula signature realContext apparentContext (bindOrder 0 argument)) :
    Formula signature realContext apparentContext
      (max (bindOrder 0 argument) (bindOrder 0 argument)) :=
  Formula.disj (leftOrder := bindOrder 0 argument)
    (rightOrder := bindOrder 0 argument) scope.disj11Meaning left right

def imp00 (scope : ScopedConnectives signature argument)
    (left right : Formula signature realContext apparentContext 0) :
    Formula signature realContext apparentContext 0 :=
  scope.disj00 (.neg scope.neg0 left) right

def imp01 (scope : ScopedConnectives signature argument)
    (left : Formula signature realContext apparentContext 0)
    (right : Formula signature realContext apparentContext (bindOrder 0 argument)) :
    Formula signature realContext apparentContext (bindOrder 0 argument) :=
  scope.disj01 (.neg scope.neg0 left) right

def imp10 (scope : ScopedConnectives signature argument)
    (left : Formula signature realContext apparentContext (bindOrder 0 argument))
    (right : Formula signature realContext apparentContext 0) :
    Formula signature realContext apparentContext
      (max (bindOrder 0 argument) 0) :=
  scope.disj10 (.neg scope.neg1 left) right

def imp11 (scope : ScopedConnectives signature argument)
    (left right : Formula signature realContext apparentContext (bindOrder 0 argument)) :
    Formula signature realContext apparentContext
      (max (bindOrder 0 argument) (bindOrder 0 argument)) :=
  scope.disj11 (.neg scope.neg1 left) right

def emptyApparentRenaming : ApparentRenaming [] [argument]
  | _, entryVar => nomatch entryVar

def weakenClosed (proposition : Formula signature realContext [] 0) :
    Formula signature realContext [argument] 0 :=
  Formula.renameApparent emptyApparentRenaming proposition

/-- Scope-normal form for `p ⊃ (exists x).phi x`, using the mixed
disjunction definitions corresponding to ✱9·04/06 rather than retaining an
outer generic connective. -/
def normalImp01Sometimes (scope : ScopedConnectives signature argument)
    (left : Formula signature realContext [] 0)
    (body : ElementaryMatrix signature realContext [argument]) :
    Formula signature realContext [] (bindOrder 0 argument) :=
  .sometimes
    (scope.disj00 (.neg scope.neg0 (weakenClosed left)) body.toFormula)

/-- Scope-normal form for `(x).phi x ⊃ p`, using ✱9·01 and the
first-order/elementary disjunction clauses before constructing the binder. -/
def normalImp10Always (scope : ScopedConnectives signature argument)
    (body : ElementaryMatrix signature realContext [argument])
    (right : Formula signature realContext [] 0) :
    Formula signature realContext [] (bindOrder 0 argument) :=
  .sometimes
    (scope.disj00 (.neg scope.neg0 body.toFormula) (weakenClosed right))

end ScopedConnectives

/-- A scope-normalizing implication operation for one shared operand order.
Its result order remains separate from that operand order. -/
structure ImplicationAt (signature : Signature) (operandOrder : Nat) where
  resultOrder : Nat
  normalize : {realContext : RealContext} → {apparentContext : ApparentContext} →
    Formula signature realContext apparentContext operandOrder →
    Formula signature realContext apparentContext operandOrder →
    Formula signature realContext apparentContext resultOrder

/-- The elementary assigned-scope normalization is one concrete inhabitant;
other order pairs must supply their own audited normalizer. -/
def ImplicationAt.elementary
    (scope : ScopedConnectives signature argument) :
    ImplicationAt signature 0 where
  resultOrder := 0
  normalize := fun left right => scope.imp00 left right

namespace ElementaryFunction

def value (function : ElementaryFunction signature realContext argument)
    (term : Term signature realContext [] argument) : Formula signature realContext [] 0 :=
  Formula.instantiate function.body.toFormula term

def valueFirst (function : ElementaryFunction signature realContext argument) :
    Formula signature (argument :: argument :: realContext) [] 0 :=
  (function.weakenReal.valueHead).toFormula

def valueSecond (function : ElementaryFunction signature realContext argument) :
    Formula signature (argument :: argument :: realContext) [] 0 :=
  (function.valueHead.renameReal (fun entryVar => .succ entryVar)).toFormula

def bodyUnderOneReal (function : ElementaryFunction signature realContext argument) :
    ElementaryMatrix signature (argument :: realContext) [argument] :=
  function.weakenReal.body

def bodyUnderTwoReals (function : ElementaryFunction signature realContext argument) :
    ElementaryMatrix signature (argument :: argument :: realContext) [argument] :=
  function.weakenReal.weakenReal.body

end ElementaryFunction

/-- Experimental rule-shape test, not canonical PM coverage. -/
inductive ToyDerivation {signature : Signature} :
    {realContext : RealContext} → {order : Nat} →
      Formula signature realContext [] order → Prop where
  | toy_star_9_1
      (function : ElementaryFunction signature realContext argument)
      (scope : ScopedConnectives signature argument) :
      ToyDerivation
        (scope.normalImp01Sometimes function.valueHead.toFormula
          function.bodyUnderOneReal)
  | toy_star_9_11
      (function : ElementaryFunction signature realContext argument)
      (scope : ScopedConnectives signature argument) :
      ToyDerivation
        (scope.normalImp01Sometimes
          (scope.disj00 function.valueFirst function.valueSecond)
          function.bodyUnderTwoReals)
  | toy_star_9_12
      {left right : Formula signature realContext [] operandOrder}
      (operation : ImplicationAt signature operandOrder) :
      ToyDerivation left →
      ToyDerivation (operation.normalize left right) →
      ToyDerivation right
  | toy_star_9_13
      (proposition : Formula signature (argument :: realContext) [] order) :
      ToyDerivation proposition →
      ToyDerivation (.always proposition.abstractRealHead)
  | toy_star_10_1
      (function : ElementaryFunction signature realContext argument)
      (scope : ScopedConnectives signature argument) :
      ToyDerivation
        (scope.normalImp10Always
          function.bodyUnderOneReal function.valueHead.toFormula)

/-- Order is computed from the complete function sort, never supplied as a
detached numeral. -/
def ramifiedFunctionOrder (arguments : List RamifiedSort) (resultOrder excess : Nat) : Nat :=
  RamifiedSort.height (.function arguments resultOrder excess)

/-- Explicit domain element for a reducibility assumption. -/
structure ReducibleAt (signature : Signature) (argument : RamifiedSort)
    (resultOrder excess : Nat) where
  function : Term signature [] [] (.function [argument] resultOrder excess)

def ReducibleAt.sourceOrder
    (_entry : ReducibleAt signature argument resultOrder excess) : Nat :=
  ramifiedFunctionOrder [argument] resultOrder excess

def ReducibleAt.targetOrder
    (_entry : ReducibleAt signature argument resultOrder excess) : Nat :=
  ramifiedFunctionOrder [argument] resultOrder 0

def formalEquivalenceOrder (argument : RamifiedSort) (resultOrder leftExcess
    rightExcess : Nat) : Nat :=
  max (ramifiedFunctionOrder [argument] resultOrder leftExcess)
    (ramifiedFunctionOrder [argument] resultOrder rightExcess)

structure UnaryFormalEquivalence (signature : Signature) where
  formula : {argument : RamifiedSort} → {resultOrder leftExcess rightExcess : Nat} →
    Term signature [] [] (.function [argument] resultOrder leftExcess) →
    Term signature [] [] (.function [argument] resultOrder rightExcess) →
    Formula signature [] []
      (formalEquivalenceOrder argument resultOrder leftExcess rightExcess)

/-- Explicit scoped hypothesis, never a global axiom or derivation rule. -/
structure UnaryReducibility (signature : Signature)
    (formalEquivalence : UnaryFormalEquivalence signature) where
  representative : {argument : RamifiedSort} → {resultOrder excess : Nat} →
    ReducibleAt signature argument resultOrder excess →
    Term signature [] [] (.function [argument] resultOrder 0)
  certificate : {argument : RamifiedSort} → {resultOrder excess : Nat} →
    (entry : ReducibleAt signature argument resultOrder excess) →
    ToyDerivation
      (formalEquivalence.formula entry.function (representative entry))

/-- Extraction is deliberately impossible without the explicit hypothesis
`reducibility`; there is no zero-argument or typeclass-based counterpart. -/
def reducedRepresentative
    (reducibility : UnaryReducibility signature formalEquivalence)
    (entry : ReducibleAt signature argument resultOrder excess) :
    Term signature [] [] (.function [argument] resultOrder 0) :=
  reducibility.representative entry

/-! ## Concrete higher-order witness for the architectural barrier -/

def individualSort : RamifiedSort := .individual
def predicateSort : RamifiedSort := .function [individualSort] 0 0

inductive WitnessSymbol : RamifiedSort → Type where
  | predicate : WitnessSymbol predicateSort
  | evaluator : WitnessSymbol (.function [predicateSort] 0 0)
  | nonPredicativeEvaluator : WitnessSymbol (.function [predicateSort] 0 1)
  | relation : WitnessSymbol
      (.function [predicateSort, individualSort] 0 0)

inductive WitnessNegation : Nat → Type where
  | order0 : WitnessNegation 0
  | order2 : WitnessNegation 2

inductive WitnessDisjunction : Nat → Nat → Type where
  | order00 : WitnessDisjunction 0 0
  | order02 : WitnessDisjunction 0 2
  | order20 : WitnessDisjunction 2 0
  | order22 : WitnessDisjunction 2 2

def witnessSignature : Signature where
  Symbol := WitnessSymbol
  NegationMeaning := WitnessNegation
  DisjunctionMeaning := WitnessDisjunction

def higherScope : ScopedConnectives witnessSignature predicateSort where
  neg0 := WitnessNegation.order0
  neg1 := WitnessNegation.order2
  disj00Meaning := WitnessDisjunction.order00
  disj01Meaning := WitnessDisjunction.order02
  disj10Meaning := WitnessDisjunction.order20
  disj11Meaning := WitnessDisjunction.order22

/-- A genuine elementary function whose argument is itself a first-order
function type; its evaluator is consequently a higher-order application. -/
def higherFunctionWitness :
    ElementaryFunction witnessSignature [] predicateSort :=
  ⟨.apply (.symbol .evaluator) (.cons (.apparent .zero) .nil)⟩

/-- Explicit value at the realContext predicate symbol. -/
def higherFunctionValueWitness : Formula witnessSignature [] [] 0 :=
  higherFunctionWitness.value (.symbol .predicate)

/-- Matrix with a predicate and an individual as two differently typed
apparentContext variables. -/
def twoBinderMatrixWitness :
    ElementaryMatrix witnessSignature [] [individualSort, predicateSort] :=
  .apply (.symbol .relation)
    (.cons (.apparent (.succ .zero)) (.cons (.apparent .zero) .nil))

/-- Two binder steps: the individual step reaches order one and the outer
predicate step reaches order two. -/
def twoBinderFormulaWitness : Formula witnessSignature [] [] 2 :=
  .always (.always twoBinderMatrixWitness.toFormula)

/-- Concrete experimental ✱10·1-shaped derivation for a function whose
argument is itself a function type. -/
def higherToyStar10Witness : ToyDerivation
    (higherScope.normalImp10Always
      higherFunctionWitness.bodyUnderOneReal
      higherFunctionWitness.valueHead.toFormula) :=
  .toy_star_10_1 higherFunctionWitness higherScope

/-- The same higher-order application with one explicit excess order. -/
def higherNonPredicativeFunctionWitness :
    ElementaryFunction witnessSignature [] predicateSort :=
  ⟨.apply (.symbol .nonPredicativeEvaluator)
    (.cons (.apparent .zero) .nil)⟩

def higherNonPredicativeEntry :
    ReducibleAt witnessSignature predicateSort 0 1 :=
  ⟨.symbol .nonPredicativeEvaluator⟩

def higherNonPredicativeStar10Witness : ToyDerivation
    (higherScope.normalImp10Always
      higherNonPredicativeFunctionWitness.bodyUnderOneReal
      higherNonPredicativeFunctionWitness.valueHead.toFormula) :=
  .toy_star_10_1 higherNonPredicativeFunctionWitness higherScope

/-- Dependent evidence tying the exact representative selected by a
reducibility package to the package's certificate for that representative. -/
structure HigherStar10ReducibilityWitness
    (formalEquivalence : UnaryFormalEquivalence witnessSignature) where
  star10 : ToyDerivation
    (higherScope.normalImp10Always
      higherNonPredicativeFunctionWitness.bodyUnderOneReal
      higherNonPredicativeFunctionWitness.valueHead.toFormula)
  reduction : PSigma fun representative :
      Term witnessSignature [] [] (.function [predicateSort] 0 0) =>
    ToyDerivation
      (formalEquivalence.formula
        higherNonPredicativeEntry.function representative)

/-- Build the dependent witness by consuming both `representative` and its
matching `certificate` from the explicitly supplied reducibility package. -/
def higherStar10WithReducibility
    (reducibility : UnaryReducibility witnessSignature formalEquivalence) :
    HigherStar10ReducibilityWitness formalEquivalence :=
  ⟨higherNonPredicativeStar10Witness,
    ⟨reducibility.representative higherNonPredicativeEntry,
      reducibility.certificate higherNonPredicativeEntry⟩⟩

/-- Concrete realContext-head/apparentContext-head round trip at a function argument type. -/
@[simp] theorem higherFunctionHeadRoundTrip :
    higherFunctionWitness.valueHead.abstractHead.valueHead =
      higherFunctionWitness.valueHead :=
  ElementaryMatrix.value_abstract_head higherFunctionWitness.valueHead

/-! ## Elementary-syntax embedding and partial retraction -/

def legacySort : PM.RealType → RamifiedSort
  | .elementaryProposition => .proposition 0

inductive LegacySymbol : RamifiedSort → Type where
  | elementaryConstant : String → LegacySymbol (.proposition 0)

inductive LegacyNegationMeaning : Nat → Type where
  | elementary : LegacyNegationMeaning 0

inductive LegacyDisjunctionMeaning : Nat → Nat → Type where
  | elementary : LegacyDisjunctionMeaning 0 0

def legacySignature : Signature where
  Symbol := LegacySymbol
  NegationMeaning := LegacyNegationMeaning
  DisjunctionMeaning := LegacyDisjunctionMeaning

def embedRealVar : PM.RealVar realContext .elementaryProposition →
    Var (realContext.map legacySort) (.proposition 0)
  | .zero => .zero
  | .succ entryVar => .succ (embedRealVar entryVar)

def eraseRealVar : (realContext : PM.RealContext) →
    Var (realContext.map legacySort) (.proposition 0) →
      PM.RealVar realContext .elementaryProposition
  | _ :: _, .zero => .zero
  | _ :: _, .succ entryVar => .succ (eraseRealVar _ entryVar)

def embedElementary : PM.Elementary realContext →
    Formula legacySignature (realContext.map legacySort) [] 0
  | .constant name =>
      .propositionVariable (.symbol (.elementaryConstant name))
  | .var entryVar => .propositionVariable (.real (embedRealVar entryVar))
  | .neg proposition =>
      .neg LegacyNegationMeaning.elementary (embedElementary proposition)
  | .disj left right =>
      Formula.disj (leftOrder := 0) (rightOrder := 0)
        LegacyDisjunctionMeaning.elementary
        (embedElementary left) (embedElementary right)

structure ErasedElementary (realContext : PM.RealContext) (order : Nat) where
  proposition : PM.Elementary realContext
  order_eq : order = 0

def erasePropositionTerm? : {order : Nat} →
    Term legacySignature (realContext.map legacySort) [] (.proposition order) →
      Option (ErasedElementary (realContext := realContext) order)
  | 0, .real entryVar => some ⟨.var (eraseRealVar realContext entryVar), rfl⟩
  | 0, .symbol (.elementaryConstant name) => some ⟨.constant name, rfl⟩
  | _, _ => none

def eraseElementaryIndexed? : {order : Nat} →
    Formula legacySignature (realContext.map legacySort) [] order →
      Option (ErasedElementary (realContext := realContext) order)
  | _, .propositionVariable entryVar => erasePropositionTerm? entryVar
  | _, .apply _ _ => none
  | _, .neg LegacyNegationMeaning.elementary inner => do
      let erased ← eraseElementaryIndexed? inner
      pure ⟨.neg erased.proposition, erased.order_eq⟩
  | _, .disj LegacyDisjunctionMeaning.elementary left right => do
      let erasedLeft ← eraseElementaryIndexed? left
      let erasedRight ← eraseElementaryIndexed? right
      have resultOrder : max 0 0 = 0 := rfl
      pure ⟨.disj erasedLeft.proposition erasedRight.proposition, resultOrder⟩
  | _, .always _ => none
  | _, .sometimes _ => none

def eraseElementary? (proposition :
    Formula legacySignature (realContext.map legacySort) [] 0) :
    Option (PM.Elementary realContext) := do
  let erased ← eraseElementaryIndexed? proposition
  pure erased.proposition

@[simp] theorem erase_embedRealVar :
    (entryVar : PM.RealVar realContext .elementaryProposition) →
      eraseRealVar realContext (embedRealVar entryVar) = entryVar
  | .zero => rfl
  | .succ entryVar => congrArg PM.RealVar.succ (erase_embedRealVar entryVar)

@[simp] theorem eraseIndexed_embedElementary (proposition : PM.Elementary realContext) :
    eraseElementaryIndexed? (embedElementary proposition) =
      some ⟨proposition, rfl⟩ := by
  induction proposition with
  | constant name => rfl
  | var entryVar => simp [embedElementary, eraseElementaryIndexed?,
      erasePropositionTerm?]
  | neg proposition inductionHypothesis =>
      simp [embedElementary, eraseElementaryIndexed?, inductionHypothesis]
  | disj left right leftHypothesis rightHypothesis =>
      simp [embedElementary, eraseElementaryIndexed?, leftHypothesis, rightHypothesis]

@[simp] theorem erase_embedElementary (proposition : PM.Elementary realContext) :
    eraseElementary? (embedElementary proposition) = some proposition := by
  simp [eraseElementary?, eraseIndexed_embedElementary]

end PM.Experimental.RamifiedToy
