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
inductive Sort where
  | individual
  | proposition (order : Nat)
  | function (arguments : List Sort) (resultOrder excess : Nat)
  deriving DecidableEq, Repr

namespace Sort

mutual
  def height : Sort → Nat
    | .individual => 0
    | .proposition order => order
    | .function arguments resultOrder excess =>
        max (Nat.succ (maxHeight arguments)) (Nat.succ resultOrder) + excess

  def maxHeight : List Sort → Nat
    | [] => 0
    | argument :: arguments => max (height argument) (maxHeight arguments)
end

def minimumFunctionOrder (arguments : List Sort) (resultOrder : Nat) : Nat :=
  max (Nat.succ (maxHeight arguments)) (Nat.succ resultOrder)

def Predicative : Sort → Prop
  | .function _ _ 0 => True
  | _ => False

end Sort

abbrev RealContext := List Sort
abbrev ApparentContext := List Sort

inductive Var : List Sort → Sort → Type where
  | zero : Var (sort :: context) sort
  | succ : Var context sort → Var (other :: context) sort
  deriving DecidableEq, Repr

/-- Connective meanings exist only at explicitly assigned orders. -/
structure Signature where
  Symbol : Sort → Type
  NegationMeaning : Nat → Type
  DisjunctionMeaning : Nat → Nat → Type

inductive Term (signature : Signature) (real : RealContext)
    (apparent : ApparentContext) : Sort → Type where
  | real : Var real sort → Term signature real apparent sort
  | apparent : Var apparent sort → Term signature real apparent sort
  | symbol : signature.Symbol sort → Term signature real apparent sort

/-- Full applications are intrinsically typed by their argument vector. -/
inductive Arguments (signature : Signature) (real : RealContext)
    (apparent : ApparentContext) : List Sort → Type where
  | nil : Arguments signature real apparent []
  | cons : Term signature real apparent sort →
      Arguments signature real apparent sorts →
      Arguments signature real apparent (sort :: sorts)

def bindOrder (matrixOrder : Nat) (sort : Sort) : Nat :=
  max matrixOrder (Nat.succ sort.height)

inductive Formula (signature : Signature) (real : RealContext)
    (apparent : ApparentContext) : Nat → Type where
  | propositionVariable :
      Term signature real apparent (.proposition order) →
      Formula signature real apparent order
  | apply :
      Term signature real apparent (.function sorts resultOrder excess) →
      Arguments signature real apparent sorts →
      Formula signature real apparent resultOrder
  | neg : signature.NegationMeaning order →
      Formula signature real apparent order →
      Formula signature real apparent order
  | disj : signature.DisjunctionMeaning leftOrder rightOrder →
      Formula signature real apparent leftOrder →
      Formula signature real apparent rightOrder →
      Formula signature real apparent (max leftOrder rightOrder)
  | always : Formula signature real (sort :: apparent) matrixOrder →
      Formula signature real apparent (bindOrder matrixOrder sort)
  | sometimes : Formula signature real (sort :: apparent) matrixOrder →
      Formula signature real apparent (bindOrder matrixOrder sort)

namespace Formula

abbrev ApparentRenaming (source target : ApparentContext) :=
  {sort : Sort} → Var source sort → Var target sort

abbrev RealRenaming (source target : RealContext) :=
  {sort : Sort} → Var source sort → Var target sort

def liftApparentRenaming (renaming : ApparentRenaming source target) :
    ApparentRenaming (sort :: source) (sort :: target)
  | _, .zero => .zero
  | _, .succ variable => .succ (renaming variable)

def Term.renameApparent (renaming : ApparentRenaming source target) :
    Term signature real source sort → Term signature real target sort
  | .real variable => .real variable
  | .apparent variable => .apparent (renaming variable)
  | .symbol symbol => .symbol symbol

def Arguments.renameApparent (renaming : ApparentRenaming source target) :
    Arguments signature real source sorts →
      Arguments signature real target sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons (argument.renameApparent renaming)
        (arguments.renameApparent renaming)

def renameApparent (renaming : ApparentRenaming source target) :
    Formula signature real source order → Formula signature real target order
  | .propositionVariable variable =>
      .propositionVariable (variable.renameApparent renaming)
  | .apply function arguments =>
      .apply (function.renameApparent renaming)
        (arguments.renameApparent renaming)
  | .neg meaning proposition => .neg meaning (renameApparent renaming proposition)
  | .disj meaning left right =>
      .disj meaning (renameApparent renaming left) (renameApparent renaming right)
  | .always body => .always (renameApparent (liftApparentRenaming renaming) body)
  | .sometimes body =>
      .sometimes (renameApparent (liftApparentRenaming renaming) body)

def weakenApparent (term : Term signature real apparent sort) :
    Term signature real (fresh :: apparent) sort :=
  term.renameApparent (fun variable => .succ variable)

def Term.renameReal (renaming : RealRenaming source target) :
    Term signature source apparent sort → Term signature target apparent sort
  | .real variable => .real (renaming variable)
  | .apparent variable => .apparent variable
  | .symbol symbol => .symbol symbol

def Arguments.renameReal (renaming : RealRenaming source target) :
    Arguments signature source apparent sorts →
      Arguments signature target apparent sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons (argument.renameReal renaming) (arguments.renameReal renaming)

def renameReal (renaming : RealRenaming source target) :
    Formula signature source apparent order → Formula signature target apparent order
  | .propositionVariable variable => .propositionVariable (variable.renameReal renaming)
  | .apply function arguments =>
      .apply (function.renameReal renaming) (arguments.renameReal renaming)
  | .neg meaning proposition => .neg meaning (renameReal renaming proposition)
  | .disj meaning left right =>
      .disj meaning (renameReal renaming left) (renameReal renaming right)
  | .always body => .always (renameReal renaming body)
  | .sometimes body => .sometimes (renameReal renaming body)

def weakenReal (proposition : Formula signature real apparent order) :
    Formula signature (fresh :: real) apparent order :=
  renameReal (fun variable => .succ variable) proposition

abbrev ApparentSubstitution (signature : Signature) (real : RealContext)
    (source target : ApparentContext) :=
  {sort : Sort} → Var source sort → Term signature real target sort

def liftSubstitution
    (substitution : ApparentSubstitution signature real source target) :
    ApparentSubstitution signature real (sort :: source) (sort :: target)
  | _, .zero => .apparent .zero
  | _, .succ variable => weakenApparent (substitution variable)

def Term.substitute
    (substitution : ApparentSubstitution signature real source target) :
    Term signature real source sort → Term signature real target sort
  | .real variable => .real variable
  | .apparent variable => substitution variable
  | .symbol symbol => .symbol symbol

def Arguments.substitute
    (substitution : ApparentSubstitution signature real source target) :
    Arguments signature real source sorts →
      Arguments signature real target sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons (argument.substitute substitution)
        (arguments.substitute substitution)

def substitute
    (substitution : ApparentSubstitution signature real source target) :
    Formula signature real source order → Formula signature real target order
  | .propositionVariable variable =>
      .propositionVariable (variable.substitute substitution)
  | .apply function arguments =>
      .apply (function.substitute substitution)
        (arguments.substitute substitution)
  | .neg meaning proposition => .neg meaning (substitute substitution proposition)
  | .disj meaning left right =>
      .disj meaning (substitute substitution left) (substitute substitution right)
  | .always body => .always (substitute (liftSubstitution substitution) body)
  | .sometimes body => .sometimes (substitute (liftSubstitution substitution) body)

def instantiateSubstitution (argument : Term signature real apparent sort) :
    ApparentSubstitution signature real (sort :: apparent) apparent
  | _, .zero => argument
  | _, .succ variable => .apparent variable

def instantiate (body : Formula signature real (sort :: apparent) order)
    (argument : Term signature real apparent sort) :
    Formula signature real apparent order :=
  substitute (instantiateSubstitution argument) body

end Formula

/-- Move the head real variable into a fresh apparent-variable position. -/
def Term.abstractHead :
    Term signature (head :: real) apparent sort →
      Term signature real (head :: apparent) sort
  | .real .zero => .apparent .zero
  | .real (.succ variable) => .real variable
  | .apparent variable => .apparent (.succ variable)
  | .symbol symbol => .symbol symbol

/-- Inverse operation: give the fresh apparent head the real head value. -/
def Term.valueHead :
    Term signature real (head :: apparent) sort →
      Term signature (head :: real) apparent sort
  | .real variable => .real (.succ variable)
  | .apparent .zero => .real .zero
  | .apparent (.succ variable) => .apparent variable
  | .symbol symbol => .symbol symbol

def Arguments.abstractHead :
    Arguments signature (head :: real) apparent sorts →
      Arguments signature real (head :: apparent) sorts
  | .nil => .nil
  | .cons argument arguments =>
      .cons argument.abstractHead arguments.abstractHead

def Arguments.valueHead :
    Arguments signature real (head :: apparent) sorts →
      Arguments signature (head :: real) apparent sorts
  | .nil => .nil
  | .cons argument arguments => .cons argument.valueHead arguments.valueHead

namespace Formula

/-- Exchange the newly abstracted variable with an already present inner
binder.  This is the critical capture-avoidance step absent from the simpler
matrix-only operation. -/
def swapAbstractedWithBinder :
    ApparentRenaming (head :: binder :: apparent)
      (binder :: head :: apparent)
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ variable) => .succ (.succ variable)

/-- Turn the real variable at the head of the real context into the new head
apparent variable, preserving the proposition order and every existing
binder. -/
def abstractRealHead :
    Formula signature (head :: real) apparent order →
      Formula signature real (head :: apparent) order
  | .propositionVariable variable =>
      .propositionVariable variable.abstractHead
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
inductive ElementaryMatrix (signature : Signature) (real : RealContext)
    (apparent : ApparentContext) : Type where
  | propositionVariable :
      Term signature real apparent (.proposition 0) →
      ElementaryMatrix signature real apparent
  | apply :
      Term signature real apparent (.function sorts 0 excess) →
      Arguments signature real apparent sorts →
      ElementaryMatrix signature real apparent
  | neg : signature.NegationMeaning 0 →
      ElementaryMatrix signature real apparent →
      ElementaryMatrix signature real apparent
  | disj : signature.DisjunctionMeaning 0 0 →
      ElementaryMatrix signature real apparent →
      ElementaryMatrix signature real apparent →
      ElementaryMatrix signature real apparent

namespace ElementaryMatrix

def toFormula : ElementaryMatrix signature real apparent →
    Formula signature real apparent 0
  | .propositionVariable variable => .propositionVariable variable
  | .apply function arguments => .apply function arguments
  | .neg meaning proposition => .neg meaning proposition.toFormula
  | .disj meaning left right => .disj meaning left.toFormula right.toFormula

def abstractHead : ElementaryMatrix signature (head :: real) apparent →
    ElementaryMatrix signature real (head :: apparent)
  | .propositionVariable variable => .propositionVariable variable.abstractHead
  | .apply function arguments =>
      .apply function.abstractHead arguments.abstractHead
  | .neg meaning proposition => .neg meaning proposition.abstractHead
  | .disj meaning left right =>
      .disj meaning left.abstractHead right.abstractHead

def valueHead : ElementaryMatrix signature real (head :: apparent) →
    ElementaryMatrix signature (head :: real) apparent
  | .propositionVariable variable => .propositionVariable variable.valueHead
  | .apply function arguments => .apply function.valueHead arguments.valueHead
  | .neg meaning proposition => .neg meaning proposition.valueHead
  | .disj meaning left right => .disj meaning left.valueHead right.valueHead

def renameReal (renaming : Formula.RealRenaming source target) :
    ElementaryMatrix signature source apparent →
      ElementaryMatrix signature target apparent
  | .propositionVariable variable =>
      .propositionVariable (variable.renameReal renaming)
  | .apply function arguments =>
      .apply (function.renameReal renaming) (arguments.renameReal renaming)
  | .neg meaning proposition => .neg meaning (renameReal renaming proposition)
  | .disj meaning left right =>
      .disj meaning (renameReal renaming left) (renameReal renaming right)

@[simp] theorem term_value_abstract_head
    (term : Term signature (head :: real) apparent sort) :
    term.abstractHead.valueHead = term := by
  cases term with
  | real variable => cases variable <;> rfl
  | apparent variable => rfl
  | symbol symbol => rfl

@[simp] theorem arguments_value_abstract_head
    (arguments : Arguments signature (head :: real) apparent sorts) :
    arguments.abstractHead.valueHead = arguments := by
  induction arguments with
  | nil => rfl
  | cons argument arguments inductionHypothesis =>
      simp [Arguments.abstractHead, Arguments.valueHead, inductionHypothesis]

@[simp] theorem value_abstract_head
    (matrix : ElementaryMatrix signature (head :: real) apparent) :
    matrix.abstractHead.valueHead = matrix := by
  induction matrix with
  | propositionVariable variable =>
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
    (real : RealContext) (argument : Sort) where
  body : ElementaryMatrix signature real [argument]

namespace ElementaryFunction

def abstractHead
    (matrix : ElementaryMatrix signature (argument :: real) []) :
    ElementaryFunction signature real argument :=
  ⟨matrix.abstractHead⟩

def valueHead (function : ElementaryFunction signature real argument) :
    ElementaryMatrix signature (argument :: real) [] :=
  function.body.valueHead

@[simp] theorem valueHead_abstractHead
    (matrix : ElementaryMatrix signature (argument :: real) []) :
    valueHead (abstractHead matrix) = matrix :=
  ElementaryMatrix.value_abstract_head matrix

def weakenReal (function : ElementaryFunction signature real argument) :
    ElementaryFunction signature (fresh :: real) argument :=
  ⟨function.body.renameReal (fun variable => .succ variable)⟩

end ElementaryFunction

/-- Exactly the four assigned scope combinations needed around one binder.
The names `00`, `01`, `10`, and `11` refer to matrix/bound scope, not to an
all-orders connective. -/
structure ScopedConnectives (signature : Signature) (argument : Sort) where
  neg0 : signature.NegationMeaning 0
  neg1 : signature.NegationMeaning (bindOrder 0 argument)
  disj00 : signature.DisjunctionMeaning 0 0
  disj01 : signature.DisjunctionMeaning 0 (bindOrder 0 argument)
  disj10 : signature.DisjunctionMeaning (bindOrder 0 argument) 0
  disj11 : signature.DisjunctionMeaning
    (bindOrder 0 argument) (bindOrder 0 argument)

namespace ScopedConnectives

def disj00 (scope : ScopedConnectives signature argument)
    (left right : Formula signature real apparent 0) :
    Formula signature real apparent 0 :=
  .disj scope.disj00 left right

def disj01 (scope : ScopedConnectives signature argument)
    (left : Formula signature real apparent 0)
    (right : Formula signature real apparent (bindOrder 0 argument)) :
    Formula signature real apparent (bindOrder 0 argument) :=
  .disj scope.disj01 left right

def disj10 (scope : ScopedConnectives signature argument)
    (left : Formula signature real apparent (bindOrder 0 argument))
    (right : Formula signature real apparent 0) :
    Formula signature real apparent (bindOrder 0 argument) :=
  .disj scope.disj10 left right

def disj11 (scope : ScopedConnectives signature argument)
    (left right : Formula signature real apparent (bindOrder 0 argument)) :
    Formula signature real apparent (bindOrder 0 argument) :=
  .disj scope.disj11 left right

def imp00 (scope : ScopedConnectives signature argument)
    (left right : Formula signature real apparent 0) :
    Formula signature real apparent 0 :=
  scope.disj00 (.neg scope.neg0 left) right

def imp01 (scope : ScopedConnectives signature argument)
    (left : Formula signature real apparent 0)
    (right : Formula signature real apparent (bindOrder 0 argument)) :
    Formula signature real apparent (bindOrder 0 argument) :=
  scope.disj01 (.neg scope.neg0 left) right

def imp10 (scope : ScopedConnectives signature argument)
    (left : Formula signature real apparent (bindOrder 0 argument))
    (right : Formula signature real apparent 0) :
    Formula signature real apparent (bindOrder 0 argument) :=
  scope.disj10 (.neg scope.neg1 left) right

def imp11 (scope : ScopedConnectives signature argument)
    (left right : Formula signature real apparent (bindOrder 0 argument)) :
    Formula signature real apparent (bindOrder 0 argument) :=
  scope.disj11 (.neg scope.neg1 left) right

def weakenClosed (proposition : Formula signature real [] 0) :
    Formula signature real [argument] 0 :=
  Formula.renameApparent (fun variable => nomatch variable) proposition

/-- Scope-normal form for `p ⊃ (exists x).phi x`, using the mixed
disjunction definitions corresponding to ✱9·04/06 rather than retaining an
outer generic connective. -/
def normalImp01Sometimes (scope : ScopedConnectives signature argument)
    (left : Formula signature real [] 0)
    (body : ElementaryMatrix signature real [argument]) :
    Formula signature real [] (bindOrder 0 argument) :=
  .sometimes
    (scope.disj00 (.neg scope.neg0 (weakenClosed left)) body.toFormula)

/-- Scope-normal form for `(x).phi x ⊃ p`, using ✱9·01 and the
first-order/elementary disjunction clauses before constructing the binder. -/
def normalImp10Always (scope : ScopedConnectives signature argument)
    (body : ElementaryMatrix signature real [argument])
    (right : Formula signature real [] 0) :
    Formula signature real [] (bindOrder 0 argument) :=
  .sometimes
    (scope.disj00 (.neg scope.neg0 body.toFormula) (weakenClosed right))

end ScopedConnectives

/-- A scope-normalizing implication operation for one shared operand order.
Its result order remains separate from that operand order. -/
structure ImplicationAt (signature : Signature) (operandOrder : Nat) where
  resultOrder : Nat
  normalize : {real : RealContext} → {apparent : ApparentContext} →
    Formula signature real apparent operandOrder →
    Formula signature real apparent operandOrder →
    Formula signature real apparent resultOrder

/-- The elementary assigned-scope normalization is one concrete inhabitant;
other order pairs must supply their own audited normalizer. -/
def ImplicationAt.elementary
    (scope : ScopedConnectives signature argument) :
    ImplicationAt signature 0 where
  resultOrder := 0
  normalize := fun left right => scope.imp00 left right

namespace ElementaryFunction

def value (function : ElementaryFunction signature real argument)
    (term : Term signature real [] argument) : Formula signature real [] 0 :=
  Formula.instantiate function.body.toFormula term

def valueFirst (function : ElementaryFunction signature real argument) :
    Formula signature (argument :: argument :: real) [] 0 :=
  (function.weakenReal.valueHead).toFormula

def valueSecond (function : ElementaryFunction signature real argument) :
    Formula signature (argument :: argument :: real) [] 0 :=
  (function.valueHead.renameReal (fun variable => .succ variable)).toFormula

def bodyUnderOneReal (function : ElementaryFunction signature real argument) :
    ElementaryMatrix signature (argument :: real) [argument] :=
  function.weakenReal.body

def bodyUnderTwoReals (function : ElementaryFunction signature real argument) :
    ElementaryMatrix signature (argument :: argument :: real) [argument] :=
  function.weakenReal.weakenReal.body

end ElementaryFunction

/-- Experimental rule-shape test, not canonical PM coverage. -/
inductive ToyDerivation (signature : Signature) :
    {real : RealContext} → {order : Nat} →
      Formula signature real [] order → Prop where
  | toy_star_9_1
      (function : ElementaryFunction signature real argument)
      (scope : ScopedConnectives signature argument) :
      ToyDerivation
        (scope.normalImp01Sometimes function.valueHead.toFormula
          function.bodyUnderOneReal)
  | toy_star_9_11
      (function : ElementaryFunction signature real argument)
      (scope : ScopedConnectives signature argument) :
      ToyDerivation
        (scope.normalImp01Sometimes
          (scope.disj00 function.valueFirst function.valueSecond)
          function.bodyUnderTwoReals)
  | toy_star_9_12
      {left right : Formula signature real [] operandOrder}
      (operation : ImplicationAt signature operandOrder) :
      ToyDerivation left →
      ToyDerivation (operation.normalize left right) →
      ToyDerivation right
  | toy_star_9_13
      (proposition : Formula signature (argument :: real) [] order) :
      ToyDerivation proposition →
      ToyDerivation (.always proposition.abstractRealHead)
  | toy_star_10_1
      (function : ElementaryFunction signature real argument)
      (scope : ScopedConnectives signature argument) :
      ToyDerivation
        (scope.normalImp10Always
          function.bodyUnderOneReal function.valueHead.toFormula)

/-- Order is computed from the complete function sort, never supplied as a
detached numeral. -/
def ramifiedFunctionOrder (arguments : List Sort) (resultOrder excess : Nat) : Nat :=
  Sort.height (.function arguments resultOrder excess)

/-- Explicit domain element for a reducibility assumption. -/
structure ReducibleAt (signature : Signature) (argument : Sort)
    (resultOrder excess : Nat) where
  function : Term signature [] [] (.function [argument] resultOrder excess)

def ReducibleAt.sourceOrder
    (_entry : ReducibleAt signature argument resultOrder excess) : Nat :=
  ramifiedFunctionOrder [argument] resultOrder excess

def ReducibleAt.targetOrder
    (_entry : ReducibleAt signature argument resultOrder excess) : Nat :=
  ramifiedFunctionOrder [argument] resultOrder 0

def formalEquivalenceOrder (argument : Sort) (resultOrder leftExcess
    rightExcess : Nat) : Nat :=
  max (ramifiedFunctionOrder [argument] resultOrder leftExcess)
    (ramifiedFunctionOrder [argument] resultOrder rightExcess)

structure UnaryFormalEquivalence (signature : Signature) where
  formula : {argument : Sort} → {resultOrder leftExcess rightExcess : Nat} →
    Term signature [] [] (.function [argument] resultOrder leftExcess) →
    Term signature [] [] (.function [argument] resultOrder rightExcess) →
    Formula signature [] []
      (formalEquivalenceOrder argument resultOrder leftExcess rightExcess)

/-- Explicit scoped hypothesis, never a global axiom or derivation rule. -/
structure UnaryReducibility (signature : Signature)
    (formalEquivalence : UnaryFormalEquivalence signature) where
  representative : {argument : Sort} → {resultOrder excess : Nat} →
    ReducibleAt signature argument resultOrder excess →
    Term signature [] [] (.function [argument] resultOrder 0)
  certificate : {argument : Sort} → {resultOrder excess : Nat} →
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

def individualSort : Sort := .individual
def predicateSort : Sort := .function [individualSort] 0 0

inductive WitnessSymbol : Sort → Type where
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
  neg0 := .order0
  neg1 := .order2
  disj00 := .order00
  disj01 := .order02
  disj10 := .order20
  disj11 := .order22

/-- A genuine elementary function whose argument is itself a first-order
function type; its evaluator is consequently a higher-order application. -/
def higherFunctionWitness :
    ElementaryFunction witnessSignature [] predicateSort :=
  ⟨.apply (.symbol .evaluator) (.cons (.apparent .zero) .nil)⟩

/-- Explicit value at the real predicate symbol. -/
def higherFunctionValueWitness : Formula witnessSignature [] [] 0 :=
  higherFunctionWitness.value (.symbol .predicate)

/-- Matrix with a predicate and an individual as two differently typed
apparent variables. -/
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
  reduction : Sigma fun representative :
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

/-- Concrete real-head/apparent-head round trip at a function argument type. -/
@[simp] theorem higherFunctionHeadRoundTrip :
    ElementaryFunction.abstractHead higherFunctionWitness.valueHead =
      higherFunctionWitness := by
  cases higherFunctionWitness
  rfl

/-! ## Elementary-syntax embedding and partial retraction -/

def legacySort : PM.RealType → Sort
  | .elementaryProposition => .proposition 0

inductive LegacySymbol : Sort → Type where
  | elementaryConstant : String → LegacySymbol (.proposition 0)

inductive LegacyNegationMeaning : Nat → Type where
  | elementary : LegacyNegationMeaning 0

inductive LegacyDisjunctionMeaning : Nat → Nat → Type where
  | elementary : LegacyDisjunctionMeaning 0 0

def legacySignature : Signature where
  Symbol := LegacySymbol
  NegationMeaning := LegacyNegationMeaning
  DisjunctionMeaning := LegacyDisjunctionMeaning

def embedRealVar : PM.RealVar real .elementaryProposition →
    Var (real.map legacySort) (.proposition 0)
  | .zero => .zero
  | .succ variable => .succ (embedRealVar variable)

def eraseRealVar : (real : PM.RealContext) →
    Var (real.map legacySort) (.proposition 0) →
      PM.RealVar real .elementaryProposition
  | _ :: _, .zero => .zero
  | _ :: _, .succ variable => .succ (eraseRealVar _ variable)

def embedElementary : PM.Elementary real →
    Formula legacySignature (real.map legacySort) [] 0
  | .constant name =>
      .propositionVariable (.symbol (.elementaryConstant name))
  | .var variable => .propositionVariable (.real (embedRealVar variable))
  | .neg proposition => .neg .elementary (embedElementary proposition)
  | .disj left right =>
      .disj .elementary (embedElementary left) (embedElementary right)

def erasePropositionTerm? : {order : Nat} →
    Term legacySignature (real.map legacySort) [] (.proposition order) →
      Option (PM.Elementary real)
  | 0, .real variable => some (.var (eraseRealVar real variable))
  | 0, .symbol (.elementaryConstant name) => some (.constant name)
  | _, _ => none

def eraseElementary? (proposition :
    Formula legacySignature (real.map legacySort) [] 0) :
    Option (PM.Elementary real) :=
  match proposition with
  | .propositionVariable variable => erasePropositionTerm? variable
  | .apply _ _ => none
  | .neg .elementary inner => (eraseElementary? inner).map .neg
  | .disj .elementary left right => do
      let erasedLeft ← eraseElementary? left
      let erasedRight ← eraseElementary? right
      pure (.disj erasedLeft erasedRight)
  | .always _ => none
  | .sometimes _ => none

@[simp] theorem erase_embedElementary (proposition : PM.Elementary real) :
    eraseElementary? (embedElementary proposition) = some proposition := by
  induction proposition with
  | constant name => rfl
  | var variable =>
      induction variable with
      | zero => rfl
      | succ variable inductionHypothesis =>
          simp [embedElementary, eraseElementary?,
            erasePropositionTerm?, embedRealVar, eraseRealVar,
            inductionHypothesis]
  | neg proposition inductionHypothesis =>
      simp [embedElementary, eraseElementary?,
        inductionHypothesis]
  | disj left right leftHypothesis rightHypothesis =>
      simp [embedElementary, eraseElementary?,
        leftHypothesis, rightHypothesis]

end PM.Experimental.RamifiedToy
