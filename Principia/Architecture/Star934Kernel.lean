import Principia.Architecture.Star921MatrixKernel

namespace PM.Architecture.Star934Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.Star921MatrixKernel
open PM.Architecture.CanonicalOrderedJudgement
open PM.Architecture.CanonicalOrderedAdapters
open PM.OrderedFormula

/-!
# PM I ✱9·34: fixed universal injection

The printed chain is `✱1·3; ✱9·13; ✱9·21; (✱9·04)`.  The completed
✱9·21 evidence remains a closed canonical Raw judgement, rather than an
`OrderedAssertion`; this module records its one source-authorized application
to the displayed line (2), not a generic detachment from Raw evidence.
-/

/-- The exact displayed endpoint, with ✱9·04 retained in its right matrix. -/
def target (p : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp (OrderedFormula.always φ)
    (.firstOrder (PM.FirstEdition.Volume1.Star9.star_9_04 p φ))

/-- Closed evidence for exactly the four printed steps of ✱9·34. -/
inductive Star934KernelAssertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed_chain
      (line1 : OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.elementary (Apparent.openHead
          (matrixImp φ (Apparent.ofElementary p ∨ₐ φ)))))
      (line2 : OrderedAssertion
        (.firstOrder (FirstOrder.always
          (matrixImp φ (Apparent.ofElementary p ∨ₐ φ)))) )
      (monotonicity : Star9CanonicalAssertion
        (star_9_21_line7_raw φ (Apparent.ofElementary p ∨ₐ φ)) )
      (line4Reading :
        firstImp (OrderedFormula.always φ)
          (.firstOrder (PM.FirstEdition.Volume1.Star9.star_9_04 p φ)) =
          target p φ) :
      Star934KernelAssertion p φ

/-- PM I ✱9·34 through its fixed displayed source chain. -/
def derive (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star934KernelAssertion p φ := by
  have line4Reading :
      firstImp (OrderedFormula.always φ)
        (.firstOrder (PM.FirstEdition.Volume1.Star9.star_9_04 p φ)) =
        target p φ := rfl
  exact .printed_chain
    (.elementary (PM.Derivation.star_1_3
      (Apparent.openHead (Apparent.ofElementary p))
      (Apparent.openHead φ)))
    (OrderedAssertion.star_9_13
      (matrixImp φ (Apparent.ofElementary p ∨ₐ φ))
      (.elementary (PM.Derivation.star_1_3
        (Apparent.openHead (Apparent.ofElementary p))
        (Apparent.openHead φ))))
    (Star9KernelAssertion.star_9_21 φ (Apparent.ofElementary p ∨ₐ φ))
    line4Reading

end PM.Architecture.Star934Kernel
