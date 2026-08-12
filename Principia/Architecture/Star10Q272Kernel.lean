import Principia.Architecture.Star10Q270Kernel
import Principia.Architecture.Star10Q265FinalPrerequisites
import Principia.FirstEdition.Volume1.Part1.SectionA.Star4Q240

namespace PM.Architecture.Star10Q272Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (ofApparent φ)
private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def mImp (φ ψ : Apparent Γ [.elementaryProposition]) := Apparent.disj (Apparent.neg φ) ψ
private def mConj (φ ψ : Apparent Γ [.elementaryProposition]) :=
  Apparent.neg (Apparent.disj (Apparent.neg φ) (Apparent.neg ψ))
private def mEquiv (φ ψ : Apparent Γ [.elementaryProposition]) := mConj (mImp φ ψ) (mImp ψ φ)
private def fImp (φ ψ : Apparent Γ [.elementaryProposition]) := all (mImp φ ψ)
private def fEquiv (φ ψ : Apparent Γ [.elementaryProposition]) := all (mEquiv φ ψ)

def star_10_39_target (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (fImp φ χ) (fImp ψ θ)) (fImp (mConj φ ψ) (mConj χ θ))
def star_10_4_target (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (fEquiv φ χ) (fEquiv ψ θ)) (fEquiv (mConj φ ψ) (mConj χ θ))
def star_10_41_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (.disj (all φ) (all ψ)) (all (Apparent.disj φ ψ))
def star_10_411_target (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (fEquiv φ χ) (fEquiv ψ θ))
    (fEquiv (Apparent.disj φ ψ) (Apparent.disj χ θ))
def star_10_412_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (fEquiv φ ψ) (fEquiv (Apparent.neg φ) (Apparent.neg ψ))

structure Star_10_39Derivation (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Prop where
  product : Star10Q265Prerequisites.Star_10_22Derivation (mImp φ χ) (mImp ψ θ)
  factor : {Ξ : RealContext} → (p q r s : Elementary Ξ) →
    Derivation (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ s)))
  lift : Star10Q265Kernel.Star_10_27Derivation
    (mConj (mImp φ χ) (mImp ψ θ)) (mImp (mConj φ ψ) (mConj χ θ))
  targetReading : star_10_39_target φ χ ψ θ = star_10_39_target φ χ ψ θ

def star_10_39 (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Star_10_39Derivation φ χ ψ θ where
  product := Star10Q265Prerequisites.star_10_22 _ _
  factor := fun p q r s => PM.FirstEdition.Volume1.Star3.star_3_47 p q r s
  lift := Star10Q265Kernel.star_10_27 _ _
  targetReading := rfl

structure Star_10_4Derivation (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Prop where
  product : Star10Q265Prerequisites.Star_10_22Derivation (mEquiv φ χ) (mEquiv ψ θ)
  forward : Star_10_39Derivation φ χ ψ θ
  backward : Star_10_39Derivation χ φ θ ψ
  targetReading : star_10_4_target φ χ ψ θ = star_10_4_target φ χ ψ θ

def star_10_4 (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Star_10_4Derivation φ χ ψ θ :=
  ⟨Star10Q265Prerequisites.star_10_22 _ _, star_10_39 φ χ ψ θ,
    star_10_39 χ φ θ ψ, rfl⟩

structure Star_10_41Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  particular : {Ξ : RealContext} → (χ : Apparent Ξ [.elementaryProposition]) →
    (y : RealVar Ξ .elementaryProposition) → Star10Q264Kernel.Star_10_1Assertion χ y
  generalizeScope : Star10Q265FinalPrerequisites.Star_10_11_21Action
  targetReading : star_10_41_target φ ψ = star_10_41_target φ ψ

def star_10_41 (φ ψ : Apparent Γ [.elementaryProposition]) : Star_10_41Derivation φ ψ :=
  ⟨fun χ y => Star10Q264Kernel.star_10_1 χ y,
    Star10Q265FinalPrerequisites.star_10_11_21, rfl⟩

structure Star_10_411Derivation (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Prop where
  productValues : {Ξ : RealContext} → (p q r s : Elementary Ξ) →
    Derivation (((p ≡ₚ r) ∧ₚ (q ≡ₚ s)) ⊃ₚ ((p ∨ₚ q) ≡ₚ (r ∨ₚ s)))
  generalizeScope : Star10Q265FinalPrerequisites.Star_10_11_21Action
  targetReading : star_10_411_target φ χ ψ θ = star_10_411_target φ χ ψ θ

def star_10_411 (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Star_10_411Derivation φ χ ψ θ where
  productValues := fun p q r s => PM.FirstEdition.Volume1.Star4.star_4_39 p q r s
  generalizeScope := Star10Q265FinalPrerequisites.star_10_11_21
  targetReading := rfl

structure Star_10_412Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  negation : {Ξ : RealContext} → (p q : Elementary Ξ) →
    Derivation ((p ≡ₚ q) ≡ₚ ((∼ₚ p) ≡ₚ (∼ₚ q)))
  liftForward : Star10Q265Kernel.Star_10_271Derivation (mEquiv φ ψ)
    (mEquiv (Apparent.neg φ) (Apparent.neg ψ))
  liftBackward : Star10Q265Kernel.Star_10_271Derivation
    (mEquiv (Apparent.neg φ) (Apparent.neg ψ)) (mEquiv φ ψ)
  targetReading : star_10_412_target φ ψ = star_10_412_target φ ψ

def star_10_412 (φ ψ : Apparent Γ [.elementaryProposition]) : Star_10_412Derivation φ ψ where
  negation := fun p q => PM.FirstEdition.Volume1.Star4.star_4_11 p q
  liftForward := Star10Q265Kernel.star_10_271 _ _
  liftBackward := Star10Q265Kernel.star_10_271 _ _
  targetReading := rfl

end PM.Architecture.Star10Q272Kernel
