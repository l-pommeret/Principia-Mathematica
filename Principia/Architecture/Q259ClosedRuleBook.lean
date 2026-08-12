import Principia.Architecture.FirstOrderPrerequisites
import Principia.Architecture.FirstOrderQ259

namespace PM.Architecture.Q259ClosedRuleBook

/-!
# Closed citation environment for PM I ✱9·3, ·31, ·32, ·33

`OrderedAssertion` already contains exactly the two printed first-order Pp's
✱9·1/·11 and the two printed inference forms ✱9·12/·13.  This structure adds
only the two earlier *derived* citations used by the four demonstrations:
✱9·21 and ✱9·25.  It has no target constructor, arbitrary primitive family,
or order-polymorphic rule.

The polymorphism below ranges only over PM real-variable contexts.  Each
conclusion is fixed at assigned order one, and each implication is the
scope-certified `OrderedFormula.firstImp` from the audited prerequisites.
-/

open PM.Architecture.FirstOrderPrerequisites

structure Q259ClosedRuleBook where
  /-- The cited universal monotonicity theorem ✱9·21, at its exact schema. -/
  star_9_21 : {Γ : RealContext} →
    (φ ψ : Apparent Γ [.elementaryProposition]) →
    Star_9_21Derivation φ ψ
  /-- The cited distribution theorem ✱9·25, at its exact schema. -/
  star_9_25 : {Γ : RealContext} → (p : Elementary Γ) →
    (φ : Apparent Γ [.elementaryProposition]) →
    Star_9_25Derivation p φ

/-- The exact assertion contract for the analogue of ✱1·2 on universals.
It is a target, never a `Q259ClosedRuleBook` field. -/
abbrev Star_9_3Derivation (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_3_target φ)

/-- The exact assertion contract for the analogue of ✱1·2 on existentials.
It is a target, never a `Q259ClosedRuleBook` field. -/
abbrev Star_9_31Derivation (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_31_target φ)

/-- The exact assertion contract for the universal right-injection analogue
of ✱1·3. It is a target, never a `Q259ClosedRuleBook` field. -/
abbrev Star_9_32Derivation (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_32_target q φ)

/-- The exact assertion contract for the existential right-injection analogue
of ✱1·3. It is a target, never a `Q259ClosedRuleBook` field. -/
abbrev Star_9_33Derivation (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (FirstOrderQ259.star_9_33_target q φ)

/-- PM I ✱9·32, following the printed `✱1·3; ✱9·13; ✱9·25` chain.
The matrix passed to ✱9·13 is exactly `q ⊃ (φx ∨ q)`; the final conversion
is solely the certified ✱9·03 reduction built into the target. -/
theorem star_9_32 (rules : Q259ClosedRuleBook) (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_32Derivation q φ := by
  let body := Apparent.ofElementary (∼ₚ q) ∨ₐ (φ ∨ₐ Apparent.ofElementary q)
  have elementaryLine : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary (Apparent.openHead body)) := by
    exact OrderedAssertion.elementary
      (PM.Derivation.star_1_3
        (Apparent.openHead φ)
        (Apparent.openHead (Apparent.ofElementary q)))
  have universalLine : OrderedAssertion
      (.firstOrder (FirstOrder.always body)) :=
    OrderedAssertion.star_9_13 body elementaryLine
  exact OrderedAssertion.star_9_12 universalLine
    (rules.star_9_25 (∼ₚ q) (φ ∨ₐ Apparent.ofElementary q))

/-- PM I ✱9·33.  As indicated by “Proof as above”, ✱1·3 asserts the
elementary value `q ⊃ (φx ∨ q)`.  The corresponding explicit schema instance
of ✱9·1 existentially closes that same matrix, and the mixed ✱9·12 rule
detaches it.  The result is definitionally the printed ✱9·06/·03 reading. -/
theorem star_9_33 (_rules : Q259ClosedRuleBook) (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_33Derivation q φ := by
  let body := matrixImp (Apparent.ofElementary q)
    (φ ∨ₐ Apparent.ofElementary q)
  have elementaryLine : OrderedAssertion
      (.elementary (Apparent.elementaryValue body q)) := by
    simpa [body, matrixImp, Apparent.elementaryValue, Elementary.imp] using
      OrderedAssertion.elementary (PM.Derivation.star_1_3
        (Apparent.elementaryValue φ q) q)
  exact OrderedAssertion.star_9_12_elementary_to_first elementaryLine
    (OrderedAssertion.star_9_1_instance body q)

end PM.Architecture.Q259ClosedRuleBook
