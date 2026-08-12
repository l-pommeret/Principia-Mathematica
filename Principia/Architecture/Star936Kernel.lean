import Principia.Architecture.Star921MatrixKernel

namespace PM.Architecture.Star936Kernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.Star921MatrixKernel
open PM.Architecture.CanonicalOrderedJudgement
open PM.Architecture.CanonicalOrderedAdapters
open PM.OrderedFormula

/-!
# PM I ✱9·36: fixed universal permutation

The printed chain is `✱1·4; ✱9·13·21; (✱9·03·04)`.  As with the adjacent
closed ✱9 theorems, the ✱9·21 step is retained as its established canonical
Raw judgement instead of being falsely reified as an `OrderedAssertion`.
-/

/-- The exact displayed endpoint, retaining the two cited reductions. -/
def target (p : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp
    (.firstOrder (FirstOrder.disjElementaryLeft p (FirstOrder.always φ)))
    (.firstOrder (FirstOrder.disjRightElementary (FirstOrder.always φ) p))

/-- Closed evidence for exactly the three printed stages of ✱9·36. -/
inductive Star936KernelAssertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed_chain
      (line1 : OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.elementary (Apparent.openHead
          (matrixImp (Apparent.ofElementary p ∨ₐ φ)
            (φ ∨ₐ Apparent.ofElementary p)))))
      (line2 : OrderedAssertion
        (.firstOrder (FirstOrder.always
          (matrixImp (Apparent.ofElementary p ∨ₐ φ)
            (φ ∨ₐ Apparent.ofElementary p)))) )
      (monotonicity : Star9CanonicalAssertion
        (star_9_21_line7_raw (Apparent.ofElementary p ∨ₐ φ)
          (φ ∨ₐ Apparent.ofElementary p)))
      (line3Reading :
        firstImp
          (.firstOrder (FirstOrder.disjElementaryLeft p (FirstOrder.always φ)))
          (.firstOrder (FirstOrder.disjRightElementary (FirstOrder.always φ) p)) =
          target p φ) :
      Star936KernelAssertion p φ

/-- PM I ✱9·36 through its fixed displayed source chain. -/
def derive (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star936KernelAssertion p φ := by
  have line3Reading :
      firstImp
        (.firstOrder (FirstOrder.disjElementaryLeft p (FirstOrder.always φ)))
        (.firstOrder (FirstOrder.disjRightElementary (FirstOrder.always φ) p)) =
        target p φ := rfl
  exact .printed_chain
    (.elementary (PM.Derivation.star_1_4
      (Apparent.openHead (Apparent.ofElementary p))
      (Apparent.openHead φ)))
    (OrderedAssertion.star_9_13
      (matrixImp (Apparent.ofElementary p ∨ₐ φ)
        (φ ∨ₐ Apparent.ofElementary p))
      (.elementary (PM.Derivation.star_1_4
        (Apparent.openHead (Apparent.ofElementary p))
        (Apparent.openHead φ))))
    (Star9KernelAssertion.star_9_21
      (Apparent.ofElementary p ∨ₐ φ)
      (φ ∨ₐ Apparent.ofElementary p))
    line3Reading

end PM.Architecture.Star936Kernel
