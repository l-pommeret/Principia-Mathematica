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

The two still-missing transport theorems were checked directly against the
first-edition scan (pp. 148--150, leaves 170--172):

* `✱10·23  ⊢ :: (x) . φx ⊃ p . ≡ : (∃x) . φx . ⊃ . p`
* `✱10·27  ⊢ :: (z) . φz ⊃ ψz . ⊃ : (z) . φz . ⊃ . (z) . ψz`

The principal printed proof of ✱10·23 cites ✱4·2 and the definitions ✱9·03,
✱9·02, and ✱1·01.  PM identifies ✱10·27 directly with ✱9·21; its alternative
proof cites ✱10·14, Ass, ✱10·1, ✱10·21, and Exp.  These are theorem
dependencies, not additional non-logical assumptions.  Neither theorem is
postulated by the experiment below.

The code below exposes the primitive reducibility packages and the transport
premise only. It does not claim to reconstruct the printed proof of ✱13·101,
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
  | existentialAntecedentImplication {argument : RamifiedSort}
      {matrixOrder : Nat} :
      DeepFormula signature realContext (argument :: apparentContext) matrixOrder →
      DeepFormula signature realContext apparentContext matrixOrder →
      DeepFormula signature realContext apparentContext
        (bindOrder matrixOrder argument)
  | equivalence : DeepFormula signature realContext apparentContext order →
      DeepFormula signature realContext apparentContext order →
      DeepFormula signature realContext apparentContext order
  | alwaysFunction {functionSort : RamifiedSort} {matrixOrder : Nat} :
      DeepFormula signature realContext (functionSort :: apparentContext) matrixOrder →
      DeepFormula signature realContext apparentContext
        (bindOrder matrixOrder functionSort)
  | sometimesFunction {functionSort : RamifiedSort} {matrixOrder : Nat} :
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
  | .existentialAntecedentImplication matrix right =>
      .existentialAntecedentImplication
        (matrix.renameApparent (liftApparentRenaming rho))
        (right.renameApparent rho)
  | .equivalence left right =>
      .equivalence (left.renameApparent rho) (right.renameApparent rho)
  | .alwaysFunction body =>
      .alwaysFunction (body.renameApparent (liftApparentRenaming rho))
  | .sometimesFunction body =>
      .sometimesFunction (body.renameApparent (liftApparentRenaming rho))

def DeepFormula.renameReal (rho : RealRenaming source target) :
    DeepFormula signature source apparentContext order →
      DeepFormula signature target apparentContext order
  | .applyGeneral function inputs =>
      .applyGeneral (function.renameReal rho) (inputs.renameReal rho)
  | .applyPredicative function inputs =>
      .applyPredicative (function.renameReal rho) (inputs.renameReal rho)
  | .implication left right =>
      .implication (left.renameReal rho) (right.renameReal rho)
  | .existentialAntecedentImplication matrix right =>
      .existentialAntecedentImplication
        (matrix.renameReal rho) (right.renameReal rho)
  | .equivalence left right =>
      .equivalence (left.renameReal rho) (right.renameReal rho)
  | .alwaysFunction body => .alwaysFunction (body.renameReal rho)
  | .sometimesFunction body => .sometimesFunction (body.renameReal rho)

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
  | .existentialAntecedentImplication matrix right =>
      .existentialAntecedentImplication
        (matrix.substitute (liftSubstitution substitution))
        (right.substitute substitution)
  | .equivalence left right =>
      .equivalence (left.substitute substitution) (right.substitute substitution)
  | .alwaysFunction body =>
      .alwaysFunction (body.substitute (liftSubstitution substitution))
  | .sometimesFunction body =>
      .sometimesFunction (body.substitute (liftSubstitution substitution))

def DeepFormula.abstractHead :
    DeepFormula signature (head :: realContext) apparentContext order →
      DeepFormula signature realContext (head :: apparentContext) order
  | .applyGeneral function inputs =>
      .applyGeneral function.abstractHead inputs.abstractHead
  | .applyPredicative function inputs =>
      .applyPredicative function.abstractHead inputs.abstractHead
  | .implication left right => .implication left.abstractHead right.abstractHead
  | .existentialAntecedentImplication matrix right =>
      .existentialAntecedentImplication
        (matrix.abstractHead.renameApparent Formula.swapAbstractedWithBinder)
        right.abstractHead
  | .equivalence left right => .equivalence left.abstractHead right.abstractHead
  | .alwaysFunction body =>
      .alwaysFunction
        (body.abstractHead.renameApparent Formula.swapAbstractedWithBinder)
  | .sometimesFunction body =>
      .sometimesFunction
        (body.abstractHead.renameApparent Formula.swapAbstractedWithBinder)

def DeepFormula.valueHead
    (formula : DeepFormula signature realContext (head :: apparentContext) order) :
    DeepFormula signature (head :: realContext) apparentContext order :=
  let weakenedReal := formula.renameReal (fun entryVar => .succ entryVar)
  weakenedReal.substitute (instantiateSubstitution (.real .zero))

def DeepFormula.weakenApparent
    (formula : DeepFormula signature realContext apparentContext order) :
    DeepFormula signature realContext (fresh :: apparentContext) order :=
  formula.renameApparent (fun entryVar => .succ entryVar)

/-- Even at excess zero, omitting and printing `!` are different syntax. -/
theorem generalApply_ne_predicativeApply
    (function : Term signature realContext apparentContext
      (.function arguments resultOrder 0))
    (inputs : Arguments signature realContext apparentContext arguments) :
    DeepFormula.applyGeneral function inputs ≠
      DeepFormula.applyPredicative function inputs := by
  intro equality
  cases equality

/-- Exact scoped proposition printed at ✱10·23.  The left side binds the
argument over an implication; the right side places the existential
proposition in antecedent position without moving `p` under its binder. -/
def star10_23Formula
    (matrix : DeepFormula signature realContext [argument] matrixOrder)
    (p : DeepFormula signature realContext [] matrixOrder) :
    DeepFormula signature realContext [] (bindOrder matrixOrder argument) :=
  .equivalence
    (.alwaysFunction (.implication matrix p.weakenApparent))
    (.existentialAntecedentImplication matrix p)

/-- Exact scoped proposition printed at ✱10·27.  It transports a pointwise
implication under the universal binder; no semantic quantifier rule is used. -/
def star10_27Formula
    (left right : DeepFormula signature realContext [argument] matrixOrder) :
    DeepFormula signature realContext [] (bindOrder matrixOrder argument) :=
  .implication
    (.alwaysFunction (.implication left right))
    (.implication (.alwaysFunction left) (.alwaysFunction right))

/-- Derivability for the marked deep syntax. It has no unconditional
constructor: evidence enters only through the explicitly scoped primitive
packages below. -/
inductive DeepDerivation (signature : Signature) :
    {order : Nat} → DeepFormula signature [] [] order → Prop

/-- The exact object-language formula of ✱12·1.  The outer existential binds
the predicative representative; the inner universal binds its argument. -/
def unaryReducibilityFormula
    (function : Term signature [] [] (.function [argument] resultOrder excess)) :
    DeepFormula signature [] []
      (bindOrder (bindOrder resultOrder argument)
        (.function [argument] resultOrder 0)) :=
  .sometimesFunction
    (.alwaysFunction
      (.equivalence
        (.applyGeneral (weakenApparent (weakenApparent function))
          (.cons (.apparent .zero) .nil))
        (.applyPredicative (.apparent (.succ .zero))
          (.cons (.apparent .zero) .nil))))

/-- Experimental package matching the arity of ✱12·1 exactly. -/
structure UnaryReducibility12_1 (signature : Signature)
    {argument : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [argument] resultOrder excess)) where
  certificate : DeepDerivation signature
    (unaryReducibilityFormula function)

/-- The exact object-language formula of ✱12·11: one existential function
binder followed by the two argument binders, and no variadic generalisation. -/
def binaryReducibilityFormula
    (function : Term signature [] []
      (.function [left, right] resultOrder excess)) :
    DeepFormula signature [] []
      (bindOrder (bindOrder (bindOrder resultOrder right) left)
        (.function [left, right] resultOrder 0)) :=
  .sometimesFunction
    (.alwaysFunction
      (.alwaysFunction
        (.equivalence
          (.applyGeneral
            (weakenApparent (weakenApparent (weakenApparent function)))
            (.cons (.apparent (.succ .zero))
              (.cons (.apparent .zero) .nil)))
          (.applyPredicative (.apparent (.succ (.succ .zero)))
            (.cons (.apparent (.succ .zero))
              (.cons (.apparent .zero) .nil))))))

/-- Separate experimental package matching the arity of ✱12·11 exactly.
There is deliberately no variadic or arity-three reducibility interface. -/
structure BinaryReducibility12_11 (signature : Signature)
    {left right : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [left, right] resultOrder excess)) where
  certificate : DeepDerivation signature
    (binaryReducibilityFormula function)

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

/-- The reducibility-dependent first premise of ✱13·101 is now the printed
existential proposition itself, rather than a stronger meta-level witness.
The remaining ✱10·23/·27 transport is deliberately not postulated here. -/
def star13_101ReducibilityPremise
    {signature : Signature}
    (function : Term signature [] [] (.function [argument] resultOrder excess))
    (reducibility : UnaryReducibility12_1 signature function) :
    DeepDerivation signature (unaryReducibilityFormula function) :=
  reducibility.certificate

end PM.Experimental.PredicativeGateToy
