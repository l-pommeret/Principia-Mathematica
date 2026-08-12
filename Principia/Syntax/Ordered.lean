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
  /-- The same-assigned-order connective at the one explicit next order
  already represented by `OrderedFormula.secondOrder`.  This is syntax and a
  scope certificate only: it introduces neither a primitive assertion nor a
  detachment rule. -/
  | secondOrder : OrderedDisjunctionScope 2

inductive OrderedFormula (Γ : RealContext) : Nat → Type where
  | elementary : Elementary Γ → OrderedFormula Γ 0
  | firstOrder : FirstOrder Γ [] → OrderedFormula Γ 1
  /-- Same-assigned-order first-order matrices.  This conservative carrier
  exposes negation and disjunction between quantified first-order atoms; it
  carries syntax only and adds no assertion or detachment principle. -/
  | firstOrderMatrix : FirstOrderMatrix Γ [] → OrderedFormula Γ 1
  /-- One explicit next assigned order.  This is not an all-orders binder:
  values are exactly `Quantified (FirstOrder Γ) []`, i.e. one further PM
  apparent-variable step above the first-order matrix. -/
  | secondOrder : SecondOrder Γ [] → OrderedFormula Γ 2
  /-- The audited enriched carrier for the sole mixed first-to-second-order
  implication shape required by the printed second application of ✱9·1.
  It remains distinct from the historical `secondOrder` carrier; the explicit
  embedding is provided by `FirstOrderMatrix.ofSecondOrder`. -/
  | secondOrderMatrix : FirstOrderMatrix.Quantified Γ [] → OrderedFormula Γ 2
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

/-- The PM abbreviation `∼P ∨ Q` at the single explicitly represented second
assigned order.  The constructor carries only the matching-order scope
certificate; derivability remains entirely separate. -/
def secondImp (left right : OrderedFormula Γ 2) : OrderedFormula Γ 2 :=
  scopedImp .secondOrder left right

def always (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.always body)

def sometimes (body : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.sometimes body)

/-- The one fixed order-two universal used by the printed line (4) of
✱9·21.  No polymorphic `all` operation is exported from this syntax layer. -/
def alwaysFirstOrder (body : FirstOrder Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  .secondOrder (Quantified.always body)

/-- Capture-free renaming of ambient real variables at every represented
assigned order.  It is syntax transport only. -/
def renameReal (ρ : Apparent.RealRenaming Γ Ξ) :
    OrderedFormula Γ order → OrderedFormula Ξ order
  | .elementary p => .elementary (Elementary.schemaInstance (fun v => .var (ρ v)) p)
  | .firstOrder p => .firstOrder (FirstOrder.renameReal ρ p)
  | .firstOrderMatrix p => .firstOrderMatrix (FirstOrderMatrix.renameReal ρ p)
  | .secondOrder p => .secondOrder (SecondOrder.renameReal ρ p)
  | .secondOrderMatrix p =>
      .secondOrderMatrix (by
        cases p with
        | always body => exact .always (FirstOrderMatrix.renameReal ρ body)
        | sometimes body => exact .sometimes (FirstOrderMatrix.renameReal ρ body))
  | .neg p => .neg (renameReal ρ p)
  | .disj scope p q => .disj scope (renameReal ρ p) (renameReal ρ q)


def embedElementary (p : Elementary Γ) : OrderedFormula Γ 0 := .elementary p

def eraseElementary? : OrderedFormula Γ order → Option (Elementary Γ)
  | .elementary p => some p
  | .firstOrder _ => none
  | .firstOrderMatrix _ => none
  | .secondOrder _ => none
  | .secondOrderMatrix _ => none
  | .neg p => (eraseElementary? p).map .neg
  | .disj .elementary p q => do
      let p ← eraseElementary? p
      let q ← eraseElementary? q
      pure (.disj p q)
  | .disj (.firstOrder _) _ _ => none
  | .disj .secondOrder _ _ => none

@[simp] theorem erase_embedElementary (p : Elementary Γ) :
    eraseElementary? (embedElementary p) = some p := rfl

end OrderedFormula

end PM
