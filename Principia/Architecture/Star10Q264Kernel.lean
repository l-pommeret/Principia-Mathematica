import Principia.Architecture.Star10Definitions
import Principia.Architecture.Star92Kernel

namespace PM.Architecture.Star10Q264Kernel

open PM.Architecture.FirstOrderPrerequisites

/-! Exact canonical contracts for the two primitive principles at PM I ✱10.
They reuse the already kernelized mixed carrier and generalization rule; no
new primitive assertion or inference constructor is introduced. -/

/-- ✱10·1 has exactly the same mixed Raw endpoint as the earlier derived
general-to-particular theorem ✱9·2. -/
abbrev star_10_1_target (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : PM.CanonicalOrderedFormula.Raw Γ :=
  Star92Kernel.targetRaw φ y

abbrev Star_10_1Assertion (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Prop :=
  Star92Kernel.Star92KernelAssertion φ y

def star_10_1 (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Star_10_1Assertion φ y :=
  Star92Kernel.derive φ y

/-- The premise of ✱10·11: the open value is asserted with an arbitrary
leading real variable, which is PM's “whatever possible argument”. -/
abbrev Star_10_11Premise (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (Γ := .elementaryProposition :: Γ)
    (.elementary (Apparent.openHead φ))

abbrev star_10_11_target (φ : Apparent Γ [.elementaryProposition]) :=
  OrderedFormula.always φ

/-- ✱10·11 is precisely the already audited ✱9·13 generalization at this
one-place apparent-function carrier. -/
def star_10_11 (φ : Apparent Γ [.elementaryProposition])
    (premise : Star_10_11Premise φ) :
    OrderedAssertion (star_10_11_target φ) :=
  OrderedAssertion.star_9_13 φ premise

end PM.Architecture.Star10Q264Kernel
