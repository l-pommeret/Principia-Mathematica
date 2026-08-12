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

/-- Exact narrow judgement for ✱9·2.  Its eventual inhabitant must carry the
five printed source steps; this declaration grants no inference principle. -/
inductive Star92KernelAssertion
    (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Prop where
  /-- The one closed, source-labelled route printed at ✱9·2.  Its two proof
  premises are exactly lines (1) and (2); the remaining fields retain the
  displayed line-(3) detachment and the ✱9·05/✱9·01 definitional endpoints.
  This constructor is theorem-specific and cannot eliminate or instantiate
  an arbitrary first-order assertion. -/
  | printed_chain
      (line1 : PM.Derivation
        (∼ₚ (Apparent.atReal φ y) ∨ₚ (Apparent.atReal φ y)))
      (line2 : FirstOrderPrerequisites.OrderedAssertion
        (FirstOrderPrerequisites.star_9_1_instance_target
          (∼ₐ φ ∨ₐ Apparent.ofElementary (Apparent.atReal φ y))
          (Apparent.atReal φ y)))
      (line3 : Raw Γ)
      (line3_eq : line3 =
        .quantified .sometimes
          (.disj (.neg (ofApparent φ)) (weakenBound (valueRaw φ y))))
      (line4 : Raw Γ)
      (star905 : NormalizesScoped line3 line4)
      (line4_eq : line4 =
        .disj (.quantified .sometimes (.neg (ofApparent φ))) (valueRaw φ y))
      (star901 : NormalizesScoped line4 (targetRaw φ y)) :
      Star92KernelAssertion φ y

def line3Raw (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Raw Γ :=
  .quantified .sometimes
    (.disj (.neg (ofApparent φ)) (weakenBound (valueRaw φ y)))

def line4Raw (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Raw Γ :=
  .disj (.quantified .sometimes (.neg (ofApparent φ))) (valueRaw φ y)

theorem derive (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Star92KernelAssertion φ y := by
  apply Star92KernelAssertion.printed_chain
    (PM.FirstEdition.Volume1.Star2.star_2_1 (Apparent.atReal φ y))
    (FirstOrderPrerequisites.OrderedAssertion.star_9_1_instance
      (∼ₐ φ ∨ₐ Apparent.ofElementary (Apparent.atReal φ y))
      (Apparent.atReal φ y))
    (line3Raw φ y) rfl (line4Raw φ y)
  · exact NormalizesScoped.star_9_05_disj_independent_right _ _
  · rfl
  · apply NormalizesScoped.disjCongr
    · exact .negAlwaysReverse _
    · exact .refl _

end PM.Architecture.Star92Kernel
