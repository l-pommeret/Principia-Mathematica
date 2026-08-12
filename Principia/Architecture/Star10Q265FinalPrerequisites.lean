import Principia.Architecture.Star10Q265Prerequisites
import Principia.Architecture.Star10Q268Kernel
import Principia.FirstEdition.Volume1.Part1.SectionA.Star4

namespace PM.Architecture.Star10Q265FinalPrerequisites

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

/-- The citation `✱10·11·21` is a composed use, not a separately numbered
Pp: retain exactly its generalization and implication-scope ingredients. -/
structure Star_10_11_21Action : Prop where
  generalize : {Ξ : RealContext} → (χ : Apparent Ξ [.elementaryProposition]) →
    Star10Q264Kernel.Star_10_11Premise χ →
    PM.Architecture.FirstOrderPrerequisites.OrderedAssertion
      (Star10Q264Kernel.star_10_11_target χ)
  implicationScope : {Ξ : RealContext} → (p : Elementary Ξ) →
    (χ : Apparent Ξ [.elementaryProposition]) →
    Star10Q267Kernel.Star_10_21Assertion p χ

def star_10_11_21 : Star_10_11_21Action where
  generalize := fun χ h => Star10Q264Kernel.star_10_11 χ h
  implicationScope := fun p χ => Star10Q267Kernel.star_10_21 p χ

/-- Reuse the independently closed, canonical ✱10·23 normalization; Q265
does not introduce a second target or assertion carrier for that item. -/
abbrev Star_10_23Derivation (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Prop := Star10Q268Kernel.Star_10_23Assertion φ p

def star_10_23 (φ : Apparent Γ [.elementaryProposition]) (p : Elementary Γ) :
    Star_10_23Derivation φ p := Star10Q268Kernel.star_10_23 φ p

end PM.Architecture.Star10Q265FinalPrerequisites
