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
structure Star92KernelAssertion
    (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Prop where
  endpoint_eq : targetRaw φ y = targetRaw φ y

end PM.Architecture.Star92Kernel
