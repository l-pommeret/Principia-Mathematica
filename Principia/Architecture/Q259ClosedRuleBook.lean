import Principia.Architecture.FirstOrderPrerequisites
import Principia.Architecture.FirstOrderQ259
import Principia.Architecture.Star921MatrixKernel
import Principia.Architecture.Star931Kernel
import Principia.Architecture.Star922Kernel
import Principia.Architecture.Star92Kernel
import Principia.Architecture.Star935Kernel
import Principia.Architecture.Star936Kernel

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

/-- The exact kernel-judgement contract for the analogue of ✱1·2 on
universals.  The source-audited ✱9·21 matrix-schema bridge is deliberately
kept distinct from `OrderedAssertion`: it certifies this one closed target
without adding a generic canonical-conversion rule. -/
abbrev Star_9_3Derivation (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Star921MatrixKernel.Star9KernelAssertion (FirstOrderQ259.star_9_3_target φ)

/-- PM I ✱9·3 through the closed, source-audited ✱9·21 matrix-schema bridge.
Unlike the adjacent rule-book theorems, this conclusion is intentionally a
`Star9KernelAssertion`, not an `OrderedAssertion`: the latter has no
source-authorized general rule for reifying arbitrary Raw normalizations. -/
theorem star_9_3 (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_3Derivation φ := by
  simpa [FirstOrderQ259.star_9_3_target,
    Star921MatrixKernel.star_9_3_ordered_target] using
    Star921MatrixKernel.derive_star_9_3 φ

/-- The exact assertion contract for the analogue of ✱1·2 on existentials.
It is a target, never a `Q259ClosedRuleBook` field. -/
abbrev Star_9_31Derivation (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Nonempty (Star931Kernel.Star931KernelAssertion φ)

/-- PM I ✱9·31 through its source-faithful closed Raw normalization chain.
The rule-book argument is retained for the uniform Q259 public signature;
the proof itself uses only the primitive and definitional citations audited
in `Star931Kernel`. -/
theorem star_9_31 (_rules : Q259ClosedRuleBook)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star_9_31Derivation φ :=
  ⟨Star931Kernel.derive φ⟩

/-- Exact closed kernel contract for existential monotonicity ✱9·22.  The
result is the source-audited normalization chain, deliberately not an
`OrderedAssertion` produced by an unprinted conversion rule. -/
abbrev Star_9_22Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop :=
  Star922Kernel.Star922KernelAssertion φ ψ

theorem star_9_22 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star_9_22Derivation φ ψ :=
  Star922Kernel.derive φ ψ

abbrev Star_9_2Derivation (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Prop :=
  Star92Kernel.Star92KernelAssertion φ y

theorem star_9_2 (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Star_9_2Derivation φ y :=
  Star92Kernel.derive φ y

abbrev Star_9_35Derivation (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Star935Kernel.Star935KernelAssertion p φ

theorem star_9_35 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star_9_35Derivation p φ :=
  Star935Kernel.derive p φ

/-- Exact closed kernel contract for the universal permutation theorem
✱9·36.  Its ✱9·21 stage remains the audited canonical Raw witness, rather
than an unprinted reification into `OrderedAssertion`. -/
abbrev Star_9_36Derivation (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Star936Kernel.Star936KernelAssertion p φ

/-- PM I ✱9·36 through the source-fixed
`✱1·4; ✱9·13·21; (✱9·03·04)` chain. -/
theorem star_9_36 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star_9_36Derivation p φ :=
  Star936Kernel.derive p φ

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
