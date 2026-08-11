import Principia.Syntax.Apparent

namespace PM

/-!
# Assigned-order formulas

This is the minimal canonical bridge out of the elementary fragment.  An
order is always explicit; no constructor ranges over a type of all orders and
no object proposition is a Lean `Prop`.  The order-zero embedding is
conservative and has a partial eraser back to `Elementary`.
-/

inductive OrderedFormula (Γ : RealContext) : Nat → Type where
  | elementary : Elementary Γ → OrderedFormula Γ 0
  | firstOrder : FirstOrder Γ [] → OrderedFormula Γ 1
  | neg : OrderedFormula Γ order → OrderedFormula Γ order
  | disj : OrderedFormula Γ order → OrderedFormula Γ order → OrderedFormula Γ order

namespace OrderedFormula

prefix:max "∼ₒ" => neg
infixl:55 " ∨ₒ " => disj

def imp (p q : OrderedFormula Γ order) : OrderedFormula Γ order :=
  (∼ₒ p) ∨ₒ q

infixr:54 " ⊃ₒ " => imp

/-- The six printed scope cases of ✱9·03–·08, plus same assigned first order
for the analogues of ✱1.  A caller must choose one; there is no unindexed
cross-order connective. -/
inductive FirstOrderDisjunctionScope where
  | sameAssignedOrder
  | universalRightElementary
  | elementaryLeftUniversal
  | existentialRightElementary
  | elementaryLeftExistential
  | universalLeftExistential
  | existentialLeftUniversal

/-- Scope-labelled first-order disjunction.  The label is the audit hook to
the relevant one of ✱9·03–·08 (or to a proved same-order analogue). -/
def scopedFirstOrderDisj (scope : FirstOrderDisjunctionScope)
    (left right : OrderedFormula Γ 1) : OrderedFormula Γ 1 :=
  .disj left right

def firstImp (left right : OrderedFormula Γ 1) : OrderedFormula Γ 1 :=
  scopedFirstOrderDisj .sameAssignedOrder (∼ₒ left) right

def always (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.always body)

def sometimes (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.sometimes body)

def embedElementary (p : Elementary Γ) : OrderedFormula Γ 0 := .elementary p

def eraseElementary? : OrderedFormula Γ order → Option (Elementary Γ)
  | .elementary p => some p
  | .firstOrder _ => none
  | .neg p => (eraseElementary? p).map .neg
  | .disj p q => do
      let p ← eraseElementary? p
      let q ← eraseElementary? q
      pure (.disj p q)

@[simp] theorem erase_embedElementary (p : Elementary Γ) :
    eraseElementary? (embedElementary p) = some p := rfl

end OrderedFormula

end PM
