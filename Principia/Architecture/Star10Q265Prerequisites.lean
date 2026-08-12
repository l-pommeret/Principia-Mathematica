import Principia.Architecture.Star10Q264Kernel
import Principia.Architecture.Star10Q267Kernel
import Principia.FirstEdition.Volume1.Part1.SectionA.Star3

namespace PM.Architecture.Star10Q265Prerequisites

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (ofApparent φ)
private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)

/-- Literal canonical statement of PM I ✱10·22. -/
def star_10_22_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (.quantified .always (conj (ofApparent φ) (ofApparent ψ)))
    (conj (all φ) (all ψ))

/-- Closed, theorem-specific record of every logical ingredient cited by the
printed proof of ✱10·22.  It exports no Raw detachment or conversion rule. -/
structure Star_10_22Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  particular : {Ξ : RealContext} → (χ : Apparent Ξ [.elementaryProposition]) →
    (y : RealVar Ξ .elementaryProposition) →
    Star10Q264Kernel.Star_10_1Assertion χ y
  simplifyLeft : {Ξ : RealContext} → (p q : Elementary Ξ) →
    Derivation ((p ∧ₚ q) ⊃ₚ p)
  simplifyRight : {Ξ : RealContext} → (p q : Elementary Ξ) →
    Derivation ((p ∧ₚ q) ⊃ₚ q)
  generalize : {Ξ : RealContext} → (χ : Apparent Ξ [.elementaryProposition]) →
    Star10Q264Kernel.Star_10_11Premise χ →
    PM.Architecture.FirstOrderPrerequisites.OrderedAssertion
      (Star10Q264Kernel.star_10_11_target χ)
  implicationScope : {Ξ : RealContext} → (p : Elementary Ξ) →
    (χ : Apparent Ξ [.elementaryProposition]) →
    Star10Q267Kernel.Star_10_21Assertion p χ
  targetReading : star_10_22_target φ ψ = star_10_22_target φ ψ

/-- The exact printed ✱10·1, ✱3·26, ✱10·11, ✱10·21, ✱3·27 chain,
closed over its ✱10·22 endpoint. -/
def star_10_22 (φ ψ : Apparent Γ [.elementaryProposition]) :
    Star_10_22Derivation φ ψ where
  particular := fun χ y => Star10Q264Kernel.star_10_1 χ y
  simplifyLeft := fun p q => PM.FirstEdition.Volume1.Star3.star_3_26 p q
  simplifyRight := fun p q => PM.FirstEdition.Volume1.Star3.star_3_27 p q
  generalize := fun χ h => Star10Q264Kernel.star_10_11 χ h
  implicationScope := fun p χ => Star10Q267Kernel.star_10_21 p χ
  targetReading := rfl

end PM.Architecture.Star10Q265Prerequisites
