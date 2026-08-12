import Principia.Architecture.Star10Q265FinalPrerequisites
import Principia.Architecture.Star10Q265Kernel
import Principia.Architecture.Star10Q269Kernel
import Principia.FirstEdition.Volume1.Part1.SectionA.Star5Kernel

namespace PM.Architecture.Star10Q274Kernel
open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ := .quantified .always (ofApparent φ)
private def some (φ : Apparent Γ [.elementaryProposition]) : Raw Γ := .quantified .sometimes (ofApparent φ)
private def imp (p q : Raw Γ) := rawImp p q
private def conj (p q : Raw Γ) := Raw.neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) := conj (imp p q) (imp q p)
private def mImp (φ ψ : Apparent Γ [.elementaryProposition]) := Apparent.disj (Apparent.neg φ) ψ
private def fImp (φ ψ : Apparent Γ [.elementaryProposition]) := all (mImp φ ψ)

def star_10_51_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (.neg (some (Apparent.neg (Apparent.disj (Apparent.neg φ) (Apparent.neg ψ)))))
    (fImp φ (Apparent.neg ψ))
def star_10_53_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (.neg (some φ)) (fImp φ ψ)

def star_10_52_target (φ : Apparent Γ [.elementaryProposition]) (p : Elementary Γ) : Raw Γ :=
  imp (some φ) (imp (all (Apparent.disj (Apparent.neg φ)
    (Apparent.weaken (Apparent.ofElementary p : Apparent Γ [])))) (.elementary p))
def star_10_541_target (p : Elementary Γ) (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (fImp φ (Apparent.disj (Apparent.weaken (Apparent.ofElementary p : Apparent Γ [])) ψ))
    (.disj (.elementary p) (fImp φ ψ))
def star_10_542_target (p : Elementary Γ) (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (fImp φ (mImp (Apparent.weaken (Apparent.ofElementary p : Apparent Γ [])) ψ))
    (imp (.elementary p) (fImp φ ψ))

structure Star_10_52Derivation (φ : Apparent Γ [.elementaryProposition]) (p : Elementary Γ) : Prop where
  implicationToConstant : Star10Q265FinalPrerequisites.Star_10_23Derivation φ p
  exportation : {Ξ : RealContext} → (q r : Elementary Ξ) →
    Derivation (q ⊃ₚ ((q ⊃ₚ r) ≡ₚ r))
  targetReading : star_10_52_target φ p = star_10_52_target φ p

def star_10_52 (φ : Apparent Γ [.elementaryProposition]) (p : Elementary Γ) : Star_10_52Derivation φ p where
  implicationToConstant := Star10Q265FinalPrerequisites.star_10_23 φ p
  exportation := fun q r => PM.FirstEdition.Volume1.Star5.star_5_5 q r
  targetReading := rfl

structure Star_10_541Derivation (p : Elementary Γ) (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  scope : Star10Q267Kernel.Star_10_2Assertion p (mImp φ ψ)
  lift : Star10Q265Kernel.Star_10_271Derivation (mImp φ
    (Apparent.disj (Apparent.weaken (Apparent.ofElementary p : Apparent Γ [])) ψ))
    (Apparent.disj (Apparent.weaken (Apparent.ofElementary p : Apparent Γ [])) (mImp φ ψ))
  targetReading : star_10_541_target p φ ψ = star_10_541_target p φ ψ

def star_10_541 (p : Elementary Γ) (φ ψ : Apparent Γ [.elementaryProposition]) : Star_10_541Derivation p φ ψ :=
  ⟨Star10Q267Kernel.star_10_2 p (mImp φ ψ), Star10Q265Kernel.star_10_271 _ _, rfl⟩

structure Star_10_542Derivation (p : Elementary Γ) (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  substitution : Star_10_541Derivation (∼ₚ p) φ ψ
  targetReading : star_10_542_target p φ ψ = star_10_542_target p φ ψ

def star_10_542 (p : Elementary Γ) (φ ψ : Apparent Γ [.elementaryProposition]) : Star_10_542Derivation p φ ψ :=
  ⟨star_10_541 (∼ₚ p) φ ψ, rfl⟩

structure Star_10_51Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  negatedExistence : Star10Q269Kernel.Star_10_252Assertion
    (Apparent.neg (Apparent.disj (Apparent.neg φ) (Apparent.neg ψ)))
  lift : Star10Q265Kernel.Star_10_271Derivation
    (Apparent.neg (Apparent.neg (Apparent.disj (Apparent.neg φ) (Apparent.neg ψ))))
    (mImp φ (Apparent.neg ψ))
  targetReading : star_10_51_target φ ψ = star_10_51_target φ ψ

def star_10_51 (φ ψ : Apparent Γ [.elementaryProposition]) : Star_10_51Derivation φ ψ :=
  ⟨Star10Q269Kernel.star_10_252 _, Star10Q265Kernel.star_10_271 _ _, rfl⟩

structure Star_10_53Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop where
  negatedExistence : Star10Q269Kernel.Star_10_252Assertion φ
  explosion : {Ξ : RealContext} → (p q : Elementary Ξ) → Derivation ((∼ₚ p) ⊃ₚ (p ⊃ₚ q))
  lift : Star10Q265Kernel.Star_10_27Derivation
    (Apparent.neg φ) (mImp φ ψ)
  targetReading : star_10_53_target φ ψ = star_10_53_target φ ψ

def star_10_53 (φ ψ : Apparent Γ [.elementaryProposition]) : Star_10_53Derivation φ ψ where
  negatedExistence := Star10Q269Kernel.star_10_252 φ
  explosion := fun p q => PM.FirstEdition.Volume1.Star2.star_2_21 p q
  lift := Star10Q265Kernel.star_10_27 _ _
  targetReading := rfl

end PM.Architecture.Star10Q274Kernel
