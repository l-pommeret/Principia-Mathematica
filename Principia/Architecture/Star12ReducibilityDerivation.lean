import Principia.Experimental.PredicativeGateToy
import Principia.Architecture.Star12Q289Reducibility
import Principia.Deduction.Star12Derived
import Principia.Syntax.Printed

/-!
# PM I ✱12 — source-critical reducibility judgement

The primary objects below are the binder- and predicativity-sensitive PM AST
formulae from `PredicativeGateToy`, not their unramified `Prop` translations.
Since ✱12·1 and ✱12·11 are printed `Pp`, their derivations are primitive
constructors at exactly the unary and binary formula schemas.  No variadic
constructor, semantic truth rule, or conversion from an arbitrary Lean proof
is provided.
-/

namespace PM.Architecture.Star12ReducibilityDerivation

open PM.Experimental.RamifiedToy
open PM.Experimental.PredicativeGateToy

/-- Concrete printed-to-AST witness for the accepted ramified ✱12 calculus. -/
structure RamifiedReading (signature : Signature) (order : Nat) where
  printed : PM.PrintedFormula
  parsed : DeepFormula signature [] [] order
  scopeReading : String

/-- The narrow PM assertion judgement for the two audited reducibility Pp's. -/
inductive ReducibilityDerivation (signature : Signature) :
    {order : Nat} → DeepFormula signature [] [] order → Prop where
  /-- ✱12·1: primitive assertion of the exact unary reducibility AST. -/
  | star_12_1
      {argument : RamifiedSort} {resultOrder excess : Nat}
      (function : Term signature [] []
        (.function [argument] resultOrder excess))
      (hReducibility : UnaryReducibility12_1 signature function) :
      ReducibilityDerivation signature (unaryReducibilityFormula function)
  /-- ✱12·11: primitive assertion of the exact binary reducibility AST. -/
  | star_12_11
      {left right : RamifiedSort} {resultOrder excess : Nat}
      (function : Term signature [] []
        (.function [left, right] resultOrder excess))
      (hReducibility : BinaryReducibility12_11 signature function) :
      ReducibilityDerivation signature (binaryReducibilityFormula function)

def star_12_1_reading
    {argument : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [argument] resultOrder excess)) :
    RamifiedReading signature
      (bindOrder (bindOrder resultOrder argument)
        (.function [argument] resultOrder 0)) where
  printed := PM.pmPrinted "⊢ : (∃f) : φx .≡ₓ .f!x  Pp"
  parsed := unaryReducibilityFormula function
  scopeReading := "The existential predicative-function binder scopes over the pointwise equivalence."

def star_12_11_reading
    {left right : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [left, right] resultOrder excess)) :
    RamifiedReading signature
      (bindOrder (bindOrder (bindOrder resultOrder right) left)
        (.function [left, right] resultOrder 0)) where
  printed := PM.pmPrinted "⊢ : (∃f) : φ(x, y) .≡ₓ,ᵧ .f!(x, y)  Pp"
  parsed := binaryReducibilityFormula function
  scopeReading := "The existential predicative-function binder scopes over the two-place pointwise equivalence."


/-- Public kernel certificate for the printed unary primitive proposition. -/
theorem star_12_1
    {argument : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [argument] resultOrder excess))
    (hReducibility : UnaryReducibility12_1 signature function) :
    ReducibilityDerivation signature (unaryReducibilityFormula function) :=
  .star_12_1 function hReducibility

/-- Public kernel certificate for the printed binary primitive proposition. -/
theorem star_12_11
    {left right : RamifiedSort} {resultOrder excess : Nat}
    (function : Term signature [] []
      (.function [left, right] resultOrder excess))
    (hReducibility : BinaryReducibility12_11 signature function) :
    ReducibilityDerivation signature (binaryReducibilityFormula function) :=
  .star_12_11 function hReducibility

end PM.Architecture.Star12ReducibilityDerivation
