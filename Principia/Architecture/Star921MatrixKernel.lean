import Principia.Architecture.FirstOrderPrerequisites
import Principia.Architecture.CanonicalOrderedAdapters
import Principia.Architecture.CanonicalOrderedJudgement

namespace PM.Architecture.Star921MatrixKernel

open PM.Architecture.FirstOrderPrerequisites
open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

/-! Typed function-schema boundary for the use of ✱9·21 in ✱9·3.

The source occurrence is not a pair of `Apparent` functions: its antecedent
is a first-order matrix, while its consequent remains an apparent value.
This module records that syntax faithfully and deliberately introduces no
`OrderedAssertion` constructor or detachment principle. -/

/-- The exact mixed function shape occurring in line (4) of ✱9·3.  `left`
is an assigned first-order matrix value and `right` is an elementary
apparent value at the same apparent-variable context. -/
structure MatrixFunctionSchema (Γ : RealContext) where
  left : FirstOrder Γ [.elementaryProposition]
  right : Apparent Γ [.elementaryProposition]

/-- The antecedent function `α(x) = φx ∨ (y).φy` of the printed ✱9·3 use of
✱9·21. -/
def star_9_3_alpha (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder Γ [.elementaryProposition] :=
  FirstOrder.disjMatrixLeft φ
    (FirstOrder.always (Apparent.rename Apparent.innerVariableRenaming φ))

/-- The consequent function `β(x) = φx`. -/
def star_9_3_beta (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] := φ

/-- The source-labelled mixed function instance used in line (5) of ✱9·3. -/
def star_9_3_matrix_schema (φ : Apparent Γ [.elementaryProposition]) :
    MatrixFunctionSchema Γ where
  left := star_9_3_alpha φ
  right := star_9_3_beta φ

/-- The matrix implication in printed line (4) is definitionally the
already-certified `star_9_3_line4_matrix`. -/
theorem star_9_3_matrix_schema_line4
    (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder.impFirstToMatrix (star_9_3_matrix_schema φ).left
      (star_9_3_matrix_schema φ).right = star_9_3_line4_matrix φ := rfl

/-- Canonical Raw spelling of the first-order matrix implication at a mixed
schema value. -/
def matrixSchemaImpRaw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  ofFirstOrder (FirstOrder.impFirstToMatrix schema.left schema.right)

/-- The identity form used as printed line (1) when ✱9·21 is instantiated at
the mixed schema.  It is syntax only: ✱2·08 has not yet been lifted to this
first-order carrier. -/
def star_9_21_matrix_line1_raw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  .disj (.neg (matrixSchemaImpRaw schema)) (matrixSchemaImpRaw schema)

/-- The first ✱9·1 source shape for a mixed first-order matrix: its
existential binder scopes the complete implication. -/
def star_9_21_matrix_line2_raw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  .quantified .sometimes
    (.disj (.neg (weakenBound (matrixSchemaImpRaw schema)))
      (weakenBound (matrixSchemaImpRaw schema)))

/-- The source line-(5) conclusion after the theorem-level instance of
✱9·21: `∀x αx ⊃ ∀x βx`.  Its two sides retain their distinct assigned
carriers in Raw syntax. -/
def star_9_21_matrix_line5_raw (schema : MatrixFunctionSchema Γ) : Raw Γ :=
  .disj
    (.neg (.quantified .always (ofFirstOrder schema.left)))
    (.quantified .always (ofApparent schema.right))

/-- Assigned-order-one target of ✱9·3, kept locally so this theorem-schema
module remains below the Q259 packaging layer. -/
def star_9_3_ordered_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  let p := OrderedFormula.always φ
  OrderedFormula.firstImp
    (OrderedFormula.scopedFirstOrderDisj .sameAssignedOrder p p) p

/-- The final displayed Raw target of ✱9·3 after its cited ✱9·03
normalization.  It is the Raw image of the existing assigned-order-one
target, so no alternate object-language target is introduced. -/
def star_9_3_line6_raw (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofOrdered (star_9_3_ordered_target φ)

theorem star_9_3_matrix_line4_raw
    (φ : Apparent Γ [.elementaryProposition]) :
    matrixSchemaImpRaw (star_9_3_matrix_schema φ) =
      ofFirstOrder (star_9_3_line4_matrix φ) := rfl

/-- Closed canonical counterpart of `Star9KernelAssertion` for a source
target which has not been reified into an `OrderedFormula` carrier.  It is an
abbreviation for an existing normalized assertion witness, not a new rule. -/
abbrev Star9CanonicalAssertion (target : Raw Γ) : Prop :=
  CanonicalOrderedJudgement.NormalizedCanonicalAssertion target

namespace Star9KernelAssertion

/-- PM I ✱9·21 through its complete source-audited line-(7) normalization.
The exact target is the canonical Raw rendering of the printed apparent
formula.  Unlike ✱9·3, no equality to `ofOrdered (star_9_21_target φ ψ)` is
available, so this deliberately remains in the closed canonical judgement
rather than falsely claiming an `OrderedAssertion`. -/
def star_9_21 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star9CanonicalAssertion (star_9_21_line7_raw φ ψ) :=
  CanonicalOrderedJudgement.derive_star_9_21_line7_normalized φ ψ

end Star9KernelAssertion

end PM.Architecture.Star921MatrixKernel
