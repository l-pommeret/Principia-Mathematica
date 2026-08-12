import Principia.Architecture.FirstOrderPrerequisites
import Principia.Architecture.CanonicalOrderedAdapters

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

/-- A narrowly scoped theorem-schema action licensed by the printed use of
✱9·21 in line (5) of ✱9·3.  It is intentionally not an `OrderedAssertion`
constructor: the latter would be a new Pp.  The sole constructor records the
exact mixed schema target and requires the preceding line-(4) derivation. -/
inductive Star921MatrixSchemaDerivation (schema : MatrixFunctionSchema Γ) :
    Raw Γ → Prop where
  /-- The ✱2·08 identity at the assigned first-order matrix carrier.  The
  source line (1) of the ✱9·3 proof applies the identity to the mixed matrix
  implication; this is theorem-schema evidence, not an `OrderedAssertion`
  constructor. -/
  | matrixIdentity :
      Star921MatrixSchemaDerivation schema (star_9_21_matrix_line1_raw schema)
  /-- Reify the already-derived indexed line (4) as theorem-schema evidence.
  The equality is explicit so this cannot transport arbitrary assertions. -/
  | indexedLine4
      (proof : OrderedAssertion (star_9_3_line4_target φ))
      (h : schema = star_9_3_matrix_schema φ) :
      Star921MatrixSchemaDerivation schema (matrixSchemaImpRaw schema)
  | star_9_21_firstOrder_instance :
      Star921MatrixSchemaDerivation schema (matrixSchemaImpRaw schema) →
      Star921MatrixSchemaDerivation schema (star_9_21_matrix_line5_raw schema)

/-- The exact theorem-level transition corresponding to the printed
`(4).✱9·21` line.  It remains unusable until its line-(4) Raw derivation is
constructed from the existing indexed assertion; no logical assertion is
manufactured here. -/
def star_9_21_firstOrder_instance
    (schema : MatrixFunctionSchema Γ)
    (line4 : Star921MatrixSchemaDerivation schema (matrixSchemaImpRaw schema)) :
    Star921MatrixSchemaDerivation schema (star_9_21_matrix_line5_raw schema) :=
  .star_9_21_firstOrder_instance line4

theorem star_9_3_matrix_line4_raw
    (φ : Apparent Γ [.elementaryProposition]) :
    matrixSchemaImpRaw (star_9_3_matrix_schema φ) =
      ofFirstOrder (star_9_3_line4_matrix φ) := rfl

/-- The existing indexed proof of line (4), reflected into the narrowly
scoped theorem-schema evidence used by its printed ✱9·21 application. -/
def derive_star_9_3_line4_schema
    (φ : Apparent Γ [.elementaryProposition]) :
    Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
      (matrixSchemaImpRaw (star_9_3_matrix_schema φ)) :=
  .indexedLine4 (derive_star_9_3_line4 φ) rfl

/-- The exact source line (5) of ✱9·3. -/
def derive_star_9_3_line5_schema
    (φ : Apparent Γ [.elementaryProposition]) :
    Star921MatrixSchemaDerivation (star_9_3_matrix_schema φ)
      (star_9_21_matrix_line5_raw (star_9_3_matrix_schema φ)) :=
  star_9_21_firstOrder_instance _ (derive_star_9_3_line4_schema φ)

end PM.Architecture.Star921MatrixKernel
