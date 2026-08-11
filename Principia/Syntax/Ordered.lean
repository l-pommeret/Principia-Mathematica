import Principia.Syntax.Apparent

namespace PM

/-!
# Assigned-order formulas

This is the minimal canonical bridge out of the elementary fragment.  An
order is always explicit; no constructor ranges over a type of all orders and
no object proposition is a Lean `Prop`.  The order-zero embedding is
conservative and has a partial eraser back to `Elementary`.
-/

namespace OrderedFormula

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

end OrderedFormula

/-- A disjunction at an assigned order is available only through its audited
scope witness. The elementary and first-order cases are separate on purpose:
there is no default cross-order connective. -/
inductive OrderedDisjunctionScope : Nat → Type where
  | elementary : OrderedDisjunctionScope 0
  | firstOrder : OrderedFormula.FirstOrderDisjunctionScope →
      OrderedDisjunctionScope 1

inductive OrderedFormula (Γ : RealContext) : Nat → Type where
  | elementary : Elementary Γ → OrderedFormula Γ 0
  | firstOrder : FirstOrder Γ [] → OrderedFormula Γ 1
  /-- One explicit next assigned order.  This is not an all-orders binder:
  values are exactly `Quantified (FirstOrder Γ) []`, i.e. one further PM
  apparent-variable step above the first-order matrix. -/
  | secondOrder : SecondOrder Γ [] → OrderedFormula Γ 2
  | neg : OrderedFormula Γ order → OrderedFormula Γ order
  | disj : OrderedDisjunctionScope order → OrderedFormula Γ order →
      OrderedFormula Γ order → OrderedFormula Γ order

namespace OrderedFormula

prefix:max "∼ₒ" => neg

/-- Scope-certified disjunction at an assigned order. -/
def scopedDisj (scope : OrderedDisjunctionScope order)
    (left right : OrderedFormula Γ order) : OrderedFormula Γ order :=
  .disj scope left right

def scopedImp (scope : OrderedDisjunctionScope order)
    (p q : OrderedFormula Γ order) : OrderedFormula Γ order :=
  scopedDisj scope (∼ₒ p) q

/-- Scope-labelled first-order disjunction.  The label is the audit hook to
the relevant one of ✱9·03–·08 (or to a proved same-order analogue). -/
def scopedFirstOrderDisj (scope : FirstOrderDisjunctionScope)
    (left right : OrderedFormula Γ 1) : OrderedFormula Γ 1 :=
  scopedDisj (.firstOrder scope) left right

def firstImp (left right : OrderedFormula Γ 1) : OrderedFormula Γ 1 :=
  scopedImp (.firstOrder .sameAssignedOrder) left right

def always (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.always body)

def sometimes (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.sometimes body)

/-- The one fixed order-two universal used by the printed line (4) of
✱9·21.  No polymorphic `all` operation is exported from this syntax layer. -/
def alwaysFirstOrder (body : FirstOrder Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  .secondOrder (Quantified.always body)

def embedElementary (p : Elementary Γ) : OrderedFormula Γ 0 := .elementary p

def eraseElementary? : OrderedFormula Γ order → Option (Elementary Γ)
  | .elementary p => some p
  | .firstOrder _ => none
  | .secondOrder _ => none
  | .neg p => (eraseElementary? p).map .neg
  | .disj .elementary p q => do
      let p ← eraseElementary? p
      let q ← eraseElementary? q
      pure (.disj p q)
  | .disj (.firstOrder _) _ _ => none

@[simp] theorem erase_embedElementary (p : Elementary Γ) :
    eraseElementary? (embedElementary p) = some p := rfl

end OrderedFormula

end PM
