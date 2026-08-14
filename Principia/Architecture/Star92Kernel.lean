import Principia.Architecture.CanonicalOrderedJudgement

namespace PM.Architecture.Star92Kernel

open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
open PM.CanonicalOrderedFormula

/-! Source-faithful mixed-order boundary for PM I ✱9·2.

The printed conclusion `(x).φx ⊃ φy` has a first-order antecedent and an
elementary consequent.  It is therefore deliberately not represented by the
homogeneous `OrderedFormula.firstImp`. -/

def valueRaw (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Raw Γ :=
  .elementary (Apparent.atReal φ y)

def targetRaw (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Raw Γ :=
  .disj (.neg (.quantified .always (ofApparent φ))) (valueRaw φ y)

/-- Secondary audit record for the five printed source steps of ✱9·2.
This is deliberately not an inductive judgement: the object calculus must not
gain a theorem-specific `printed_chain` constructor. -/
def Star92KernelAssertion
    (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Prop :=
  ∃ (_line1 : PM.Derivation
        (∼ₚ (Apparent.atReal φ y) ∨ₚ (Apparent.atReal φ y)))
    (_line2 : FirstOrderPrerequisites.OrderedAssertion
        (FirstOrderPrerequisites.star_9_1_instance_target
          (∼ₐ φ ∨ₐ Apparent.ofElementary (Apparent.atReal φ y))
          (Apparent.atReal φ y)))
    (line3 : Raw Γ), line3 =
        .quantified .sometimes
          (.disj (.neg (ofApparent φ)) (weakenBound (valueRaw φ y))) ∧
      ∃ line4 : Raw Γ, NormalizesScoped line3 line4 ∧
        line4 = .disj (.quantified .sometimes (.neg (ofApparent φ)))
          (valueRaw φ y) ∧
        NormalizesScoped line4 (targetRaw φ y)

def line3Raw (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Raw Γ :=
  .quantified .sometimes
    (.disj (.neg (ofApparent φ)) (weakenBound (valueRaw φ y)))

def line4Raw (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Raw Γ :=
  .disj (.quantified .sometimes (.neg (ofApparent φ))) (valueRaw φ y)

theorem derive (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Star92KernelAssertion φ y := by
  refine ⟨PM.FirstEdition.Volume1.Star2.star_2_1 (Apparent.atReal φ y),
    FirstOrderPrerequisites.OrderedAssertion.star_9_1_instance
      (∼ₐ φ ∨ₐ Apparent.ofElementary (Apparent.atReal φ y))
      (Apparent.atReal φ y), line3Raw φ y, rfl, line4Raw φ y,
    NormalizesScoped.star_9_05_disj_independent_right _ _, rfl, ?_⟩
  apply NormalizesScoped.disjCongr
  · exact .negAlwaysReverse _
  · exact .refl _

end PM.Architecture.Star92Kernel
