import Principia.Syntax.Ordered
import Principia.Deduction.System

namespace PM

/-!
# Ordered derivations

An `OrderedRuleBook` records the explicitly assigned analogue of the
elementary primitive rules at one order.  It is evidence passed to a proof,
not an axiom, instance, or implicit all-orders principle.  The elementary
calculus remains a separate conservative fragment: a generic ordered
derivation cannot silently change a rulebook of arbitrary assigned order into
an order-zero one.
-/

structure OrderedRuleBook (Γ : RealContext) (order : Nat) where
  /-- The primitive rules accepted at this *assigned* order.  This is a type
  of audited certificates, not a proposition-level truth predicate. -/
  Primitive : OrderedFormula Γ order → Type

inductive OrderedDerivation (rules : OrderedRuleBook Γ order) :
    OrderedFormula Γ order → Prop where
  | primitive {p : OrderedFormula Γ order} : rules.Primitive p →
      OrderedDerivation rules p
  | detach {p q : OrderedFormula Γ order} (scope : OrderedDisjunctionScope order) :
      OrderedDerivation rules p → OrderedDerivation rules (OrderedFormula.scopedImp scope p q) →
        OrderedDerivation rules q

end PM
