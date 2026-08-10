import Principia.Experimental.RamifiedToy

namespace PM.Experimental.PredicativeGateToy

open RamifiedToy

/-!
# Experimental predicative/reducibility gate

This is a syntax and dependency experiment, not a formalization of the
canonical loci.  The source evidence is the first-edition scan, leaves
196--199 (printed pp. 174--177):

* leaf 196 / p. 174, SHA-256
  `56e8d8644f7db3d93d3a29d208fd75a5fc346a11c11fff337211ec9194f4cb79`;
* leaf 197 / p. 175, SHA-256
  `190549556ab8e2ca2c757baa0ed705181ade995cdc21742d5478a72ba25fb0ed`;
* leaf 198 / p. 176, SHA-256
  `4b4f4e557eba3e16e231f3e437af150fb6f347ea20b6602948f363432048227a`;
* leaf 199 / p. 177, SHA-256
  `377a277639f9d194f712cf5d0a88d5979b7243b26088b04133d0be91464b4960`.

The scan and Project Gutenberg 78050 transcription agree; Wikisource has no page
transcription. Minimal transcription:

* `✱12·1  ⊢ : (∃f) : φx . ≡ₓ . f!x    Pp`
* `✱12·11 ⊢ : (∃f) : φ(x,y) . ≡ₓ,ᵧ . f!(x,y)    Pp`
* `✱13·01 x = y .=: (φ) : φ!x .⊃. φ!y  Df`
* `✱13·101 ⊢ : x = y .⊃. ψx ⊃ ψy`

Verbatim proof transcription for the last item:

`⊢ . ✱12·1 . ⊃ ⊢ :: (∃φ) :: ψx . ≡ . φ!x : ψy . ≡ . φ!y                                      (1)`

`⊢ . ✱13·1 . ⊃ ⊢ :: Hp . ⊃ :: φ!x . ⊃φ . φ!y ::`

`[✱4·84·85 . ✱10·27]  ⊃ :: ψx . ≡ . φ!x : ψy . ≡ . φ!y : ⊃φ : ψx . ⊃ . ψy ::`

`[✱10·23]              ⊃ :: (∃φ) : ψx . ≡ . φ!x : ψy . ≡ . φ!y : ⊃ : ψx . ⊃ . ψy      (2)`

`⊢ . (1) . (2) . ⊃ ⊢ . Prop`

The code below exposes the primitive reducibility packages and the transport
shape only. It does not claim to reconstruct the printed proof of ✱13·101,
whose ✱10·23/·27 dependencies are not yet formalized here.
-/

/-- A minimal proposition AST in which the exclamation mark survives. -/
inductive DeepFormula (signature : Signature)
    (realContext : RamifiedToy.RealContext) : ApparentContext → Nat → Type where
  | applyGeneral {arguments : List RamifiedSort} {resultOrder excess : Nat} :
      Term signature realContext apparentContext
        (.function arguments resultOrder excess) →
      Arguments signature realContext apparentContext arguments →
      DeepFormula signature realContext apparentContext resultOrder
  | applyPredicative {arguments : List RamifiedSort} {resultOrder : Nat} :
      Term signature realContext apparentContext
        (.function arguments resultOrder 0) →
      Arguments signature realContext apparentContext arguments →
      DeepFormula signature realContext apparentContext resultOrder
  | implication : DeepFormula signature realContext apparentContext order →
      DeepFormula signature realContext apparentContext order →
      DeepFormula signature realContext apparentContext order
  | equivalence : DeepFormula signature realContext apparentContext order →
      DeepFormula signature realContext apparentContext order →
      DeepFormula signature realContext apparentContext order
  | alwaysFunction {functionSort : RamifiedSort} {matrixOrder : Nat} :
      DeepFormula signature realContext (functionSort :: apparentContext) matrixOrder →
      DeepFormula signature realContext apparentContext
        (bindOrder matrixOrder functionSort)

def DeepFormula.renameApparent (rho : ApparentRenaming source target) :
    DeepFormula signature realContext source order →
      DeepFormula signature realContext target order
  | .applyGeneral function inputs =>
      .applyGeneral (function.renameApparent rho) (inputs.renameApparent rho)
  | .applyPredicative function inputs =>
      .applyPredicative (function.renameApparent rho) (inputs.renameApparent rho)
  | .implication left right =>
      .implication (left.renameApparent rho) (right.renameApparent rho)
  | .equivalence left right =>
      .equivalence (left.renameApparent rho) (right.renameApparent rho)
  | .alwaysFunction body =>
      .alwaysFunction (body.renameApparent (liftApparentRenaming rho))

def DeepFormula.renameReal (rho : RealRenaming source target) :
    DeepFormula signature source apparentContext order →
      DeepFormula signature target apparentContext order
  | .applyGeneral function inputs =>
      .applyGeneral (function.renameReal rho) (inputs.renameReal rho)
  | .applyPredicative function inputs =>
      .applyPredicative (function.renameReal rho) (inputs.renameReal rho)
  | .implication left right =>
      .implication (left.renameReal rho) (right.renameReal rho)
  | .equivalence left right =>
      .equivalence (left.renameReal rho) (right.renameReal rho)
  | .alwaysFunction body => .alwaysFunction (body.renameReal rho)

def DeepFormula.substitute
    (substitution : ApparentSubstitution signature realContext source target) :
    DeepFormula signature realContext source order →
      DeepFormula signature realContext target order
  | .applyGeneral function inputs =>
      .applyGeneral (function.substitute substitution) (inputs.substitute substitution)
  | .applyPredicative function inputs =>
      .applyPredicative (function.substitute substitution) (inputs.substitute substitution)
  | .implication left right =>
      .implication (left.substitute substitution) (right.substitute substitution)
  | .equivalence left right =>
      .equivalence (left.substitute substitution) (right.substitute substitution)
  | .alwaysFunction body =>
      .alwaysFunction (body.substitute (liftSubstitution substitution))

def DeepFormula.abstractHead :
    DeepFormula signature (head :: realContext) apparentContext order →
      DeepFormula signature realContext (head :: apparentContext) order
  | .applyGeneral function inputs =>
      .applyGeneral function.abstractHead inputs.abstractHead
  | .applyPredicative function inputs =>
      .applyPredicative function.abstractHead inputs.abstractHead
  | .implication left right => .implication left.abstractHead right.abstractHead
  | .equivalence left right => .equivalence left.abstractHead right.abstractHead
  | .alwaysFunction body =>
      .alwaysFunction
        (body.abstractHead.renameApparent Formula.swapAbstractedWithBinder)

def DeepFormula.valueHead :
    DeepFormula signature realContext (head :: apparentContext) order →
      DeepFormula signature (head :: realContext) apparentContext order
  | .applyGeneral function inputs =>
      .applyGeneral function.valueHead inputs.valueHead
  | .applyPredicative function inputs =>
      .applyPredicative function.valueHead inputs.valueHead
  | .implication left right => .implication left.valueHead right.valueHead
  | .equivalence left right => .equivalence left.valueHead right.valueHead
  | .alwaysFunction body =>
      .alwaysFunction
        ((body.renameApparent Formula.swapAbstractedWithBinder).valueHead)

/-- Even at excess zero, omitting and printing `!` are different syntax. -/
theorem generalApply_ne_predicativeApply
    (function : Term signature realContext apparentContext
      (.function arguments resultOrder 0))
    (inputs : Arguments signature realContext apparentContext arguments) :
    DeepFormula.applyGeneral function inputs ≠
      DeepFormula.applyPredicative function inputs := by
  intro equality
  cases equality

/-- Derivability for the marked deep syntax. It has no unconditional
constructor: evidence enters only through the explicitly scoped primitive
packages below. -/
inductive DeepDerivation (signature : Signature) :
    {order : Nat} → DeepFormula signature [] [] order → Prop

/-- The exact unary equivalence matrix of ✱12·1: the general function occurs
on the left, its predicative representative on the right, under one binder. -/
def unaryEquivalenceFormula
    (function : Term signature [] [] (.function [argument] resultOrder excess))
    (representative : Term signature [] [] (.function [argument] resultOrder 0)) :
    DeepFormula signature [] [] (bindOrder resultOrder argument) :=
  .alwaysFunction
    (.equivalence
      (.applyGeneral (weakenApparent function) (.cons (.apparent .zero) .nil))
      (.applyPredicative (weakenApparent representative)
        (.cons (.apparent .zero) .nil)))

/-- Experimental package matching the arity of ✱12·1 exactly. -/
structure UnaryReducibility12_1 (signature : Signature)
    {argument : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [argument] resultOrder excess)) where
  representative : Term signature [] [] (.function [argument] resultOrder 0)
  certificate : DeepDerivation signature
    (unaryEquivalenceFormula function representative)

/-- The exact binary equivalence matrix of ✱12·11, under two binders. -/
def binaryEquivalenceFormula
    (function : Term signature [] []
      (.function [left, right] resultOrder excess))
    (representative : Term signature [] []
      (.function [left, right] resultOrder 0)) :
    DeepFormula signature [] []
      (bindOrder (bindOrder resultOrder right) left) :=
  .alwaysFunction
    (.alwaysFunction
      (.equivalence
        (.applyGeneral (weakenApparent (weakenApparent function))
          (.cons (.apparent (.succ .zero)) (.cons (.apparent .zero) .nil)))
        (.applyPredicative (weakenApparent (weakenApparent representative))
          (.cons (.apparent (.succ .zero)) (.cons (.apparent .zero) .nil)))))

/-- Separate experimental package matching the arity of ✱12·11 exactly.
There is deliberately no variadic or arity-three reducibility interface. -/
structure BinaryReducibility12_11 (signature : Signature)
    {left right : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [left, right] resultOrder excess)) where
  representative :
    Term signature [] [] (.function [left, right] resultOrder 0)
  certificate : DeepDerivation signature
    (binaryEquivalenceFormula function representative)

/-- Exact experimental definiens shape for ✱13·01: the same bound predicative
function `φ!` occurs on both sides, first at `x`, then at `y`. -/
def star13_01Df
    (x y : Term signature realContext apparentContext argument) :
    DeepFormula signature realContext apparentContext
      (bindOrder resultOrder (.function [argument] resultOrder 0)) :=
  .alwaysFunction
    (.implication
      (.applyPredicative (.apparent .zero)
        (.cons (weakenApparent x) .nil))
      (.applyPredicative (.apparent .zero)
        (.cons (weakenApparent y) .nil)))

/-- The explicit result of the experimental ✱13·101 transport shape. The
representative, its `φ!` application, and its certificate are dependent data. -/
structure Star13_101Transport
    (signature : Signature)
    (argument : RamifiedSort) (resultOrder excess : Nat)
    (function : Term signature [] [] (.function [argument] resultOrder excess))
    (inputSymbol : signature.Symbol argument) where
  representative : Term signature [] [] (.function [argument] resultOrder 0)
  predicativeOccurrence : DeepFormula signature [] [] resultOrder
  isMarkedRepresentative : predicativeOccurrence =
    .applyPredicative representative (.cons (.symbol inputSymbol) .nil)
  certificate : DeepDerivation signature
    (unaryEquivalenceFormula function representative)

/-- Toy transport corresponding only to the reducibility-dependent first move
in the printed proof of ✱13·101. It cannot be called without the scoped ✱12·1
package, and consumes both fields of that package. -/
def star13_101TransportShape
    {signature : Signature}
    (function : Term signature [] [] (.function [argument] resultOrder excess))
    (reducibility : UnaryReducibility12_1 signature function)
    (inputSymbol : signature.Symbol argument) :
    Star13_101Transport signature argument resultOrder excess function inputSymbol :=
  let representative := reducibility.representative
  ⟨representative,
    .applyPredicative representative (.cons (.symbol inputSymbol) .nil),
    rfl,
    reducibility.certificate⟩

end PM.Experimental.PredicativeGateToy
