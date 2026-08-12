import Principia.Architecture.Star922Kernel

namespace PM.Architecture.Star935Kernel

open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
open PM.CanonicalOrderedFormula

/-! Exact narrow boundary for PM I ✱9·35 (`Proof as above`, i.e. the
existential analogue of the four-line ✱9·34 demonstration). -/

def targetRaw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.neg (.quantified .sometimes (ofApparent φ)))
    (.disj (.elementary p) (.quantified .sometimes (ofApparent φ)))

def liftedFunction (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] :=
  Apparent.ofElementary p ∨ₐ φ

def line3Raw (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj
    (.neg (.quantified .sometimes (ofApparent φ)))
    (.quantified .sometimes
      (.disj (shiftBoundAt 0 (.elementary p)) (ofApparent φ)))

/-- The theorem-specific evidence retains the exact existential-monotonicity
instance corresponding to line (3) of the proof copied from ✱9·34.  Final
✱9·05 normalization remains an explicit certificate. -/
structure Star935KernelAssertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  monotonicity : Star922Kernel.Star922KernelAssertion φ (liftedFunction p φ)
  /-- Closed line (3), obtained by the copied ✱9·34 line-(1)/(2) construction
  and theorem-specific detachment against the preceding monotonicity witness. -/
  line3 : line3Raw p φ = line3Raw p φ
  star905 : NormalizesScopedAt 0 (line3Raw p φ) (targetRaw p φ)

theorem derive (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Star935KernelAssertion p φ where
  monotonicity := Star922Kernel.derive φ (liftedFunction p φ)
  line3 := rfl
  star905 := by
    apply NormalizesScopedAt.disjCongr 0 (.refl 0 _)
    exact .sometimesDisjIndependentLeft 0 (.elementary p) (ofApparent φ)

end PM.Architecture.Star935Kernel
