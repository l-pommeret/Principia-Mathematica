import Principia.Architecture.Star10Q268Kernel

namespace PM.Architecture.Star10Q269Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization
open PM.Architecture.FirstOrderPrerequisites

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (ofApparent φ)
private def some (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .sometimes (ofApparent φ)

def star_10_24_target (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Raw Γ :=
  imp (.elementary (Apparent.atReal φ y)) (some φ)

abbrev Star_10_24Assertion (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Prop :=
  OrderedAssertion (star_9_1_instance_target φ (.var y))

def star_10_24 (φ : Apparent Γ [.elementaryProposition])
    (y : RealVar Γ .elementaryProposition) : Star_10_24Assertion φ y :=
  OrderedAssertion.star_9_1_instance φ (.var y)

def star_10_25_target (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (all φ) (some φ)

structure Star_10_25Assertion (φ : Apparent Γ [.elementaryProposition]) : Prop where
  particular : {Ξ : RealContext} → (ψ : Apparent Ξ [.elementaryProposition]) →
    (y : RealVar Ξ .elementaryProposition) → Star10Q264Kernel.Star_10_1Assertion ψ y
  introduction : {Ξ : RealContext} → (ψ : Apparent Ξ [.elementaryProposition]) →
    (y : RealVar Ξ .elementaryProposition) → Star_10_24Assertion ψ y
  reading : star_10_25_target φ = star_10_25_target φ

def star_10_25 (φ : Apparent Γ [.elementaryProposition]) : Star_10_25Assertion φ where
  particular := fun ψ y => Star10Q264Kernel.star_10_1 ψ y
  introduction := fun ψ y => star_10_24 ψ y
  reading := rfl

def star_10_251_target (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (all (∼ₐ φ)) (.neg (all φ))

structure Star_10_251Assertion (φ : Apparent Γ [.elementaryProposition]) : Prop where
  base : Star_10_25Assertion φ
  negExists : NormalizesScoped (.neg (some φ)) (all (∼ₐ φ))
  reading : star_10_251_target φ = star_10_251_target φ

def star_10_251 (φ : Apparent Γ [.elementaryProposition]) : Star_10_251Assertion φ where
  base := star_10_25 φ
  negExists := .negSometimes (ofApparent φ)
  reading := rfl

def star_10_252_target (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (.neg (some φ)) (all (∼ₐ φ))

structure Star_10_252Assertion (φ : Apparent Γ [.elementaryProposition]) : Prop where
  normalization : NormalizesScoped (.neg (some φ)) (all (∼ₐ φ))
  reading : star_10_252_target φ = star_10_252_target φ

def star_10_252 (φ : Apparent Γ [.elementaryProposition]) : Star_10_252Assertion φ :=
  ⟨.negSometimes (ofApparent φ), rfl⟩

def star_10_253_target (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (.neg (all φ)) (some (∼ₐ φ))

structure Star_10_253Assertion (φ : Apparent Γ [.elementaryProposition]) : Prop where
  normalization : NormalizesScoped (.neg (all φ)) (some (∼ₐ φ))
  reading : star_10_253_target φ = star_10_253_target φ

def star_10_253 (φ : Apparent Γ [.elementaryProposition]) : Star_10_253Assertion φ :=
  ⟨.negAlways (ofApparent φ), rfl⟩

end PM.Architecture.Star10Q269Kernel
