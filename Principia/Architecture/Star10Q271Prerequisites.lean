import Principia.Architecture.Star10Q265FinalPrerequisites
import Principia.FirstEdition.Volume1.Part1.SectionA.Star3

namespace PM.Architecture.Star10Q271Prerequisites

open PM.Architecture.FirstOrderPrerequisites

/-! The fixed ingredients of the printed ✱10·33 proof.  This record is not
an order-polymorphic conjunction or assertion rule: it packages only the
four explicitly cited operations at their already canonical scopes. -/
structure Star_10_33Composition : Prop where
  particular : {Ξ : RealContext} →
    (χ : Apparent Ξ [.elementaryProposition]) →
    (y : RealVar Ξ .elementaryProposition) →
    Star10Q264Kernel.Star_10_1Assertion χ y
  simplifyLeft : {Ξ : RealContext} → (p q : Elementary Ξ) →
    Derivation ((p ∧ₚ q) ⊃ₚ p)
  simplifyRight : {Ξ : RealContext} → (p q : Elementary Ξ) →
    Derivation ((p ∧ₚ q) ⊃ₚ q)
  generalizeScope : Star10Q265FinalPrerequisites.Star_10_11_21Action

/-- Exact ✱10·1, ✱3·27, ✱3·26, ✱10·11·21 composition cited by ✱10·33. -/
def star_10_33_composition : Star_10_33Composition where
  particular := fun χ y => Star10Q264Kernel.star_10_1 χ y
  simplifyLeft := fun p q => PM.FirstEdition.Volume1.Star3.star_3_26 p q
  simplifyRight := fun p q => PM.FirstEdition.Volume1.Star3.star_3_27 p q
  generalizeScope := Star10Q265FinalPrerequisites.star_10_11_21

end PM.Architecture.Star10Q271Prerequisites
