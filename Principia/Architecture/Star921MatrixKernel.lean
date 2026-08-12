import Principia.Architecture.FirstOrderPrerequisites

namespace PM.Architecture.Star921MatrixKernel

open PM.Architecture.FirstOrderPrerequisites

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

end PM.Architecture.Star921MatrixKernel
