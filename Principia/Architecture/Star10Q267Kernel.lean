import Principia.Architecture.Star10Q264Kernel
import Principia.Architecture.CanonicalNormalization

namespace PM.Architecture.Star10Q267Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization

private def e (p : Elementary Γ) : Raw Γ := .elementary p
private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (ofApparent φ)
private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)

def star_10_2_left (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (.disj (weakenBound (e p)) (ofApparent φ))

def star_10_2_right (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .disj (e p) (all φ)

def star_10_2_target (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (star_10_2_left p φ) (star_10_2_right p φ)

/-- Closed evidence attached only to the exact ✱10·2 endpoint.  The
normalization is the displayed binder-independent disjunction reading; the
two primitive fields retain precisely ✱10·1 and ✱10·11 rather than granting
a general Raw assertion conversion. -/
structure Star_10_2Assertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  scope : NormalizesScoped (star_10_2_left p φ) (star_10_2_right p φ)
  particular : {Ξ : RealContext} → (ψ : Apparent Ξ [.elementaryProposition]) →
    (y : RealVar Ξ .elementaryProposition) →
    Star10Q264Kernel.Star_10_1Assertion ψ y
  generalize : {Ξ : RealContext} → (ψ : Apparent Ξ [.elementaryProposition]) →
    Star10Q264Kernel.Star_10_11Premise ψ →
    PM.Architecture.FirstOrderPrerequisites.OrderedAssertion
      (Star10Q264Kernel.star_10_11_target ψ)
  targetReading : star_10_2_target p φ = star_10_2_target p φ

def star_10_2 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star_10_2Assertion p φ where
  scope := NormalizesScoped.disjLeftReverse .always (ofApparent φ) (e p)
  particular := fun ψ y => Star10Q264Kernel.star_10_1 ψ y
  generalize := fun ψ h => Star10Q264Kernel.star_10_11 ψ h
  targetReading := rfl

/-- ✱10·21 is the literal `∼p/p` instance of ✱10·2, with PM implication
expanded as disjunction. -/
def star_10_21_target (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  star_10_2_target (∼ₚ p) φ

abbrev Star_10_21Assertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  Star_10_2Assertion (∼ₚ p) φ

def star_10_21 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star_10_21Assertion p φ :=
  star_10_2 (∼ₚ p) φ

/-- Exact target of ✱10·22, catalogued here even though its printed logical
composition is not yet inhabitable by the closed assertion interfaces. -/
def star_10_22_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (.quantified .always (conj (ofApparent φ) (ofApparent ψ)))
    (conj (all φ) (all ψ))

end PM.Architecture.Star10Q267Kernel
