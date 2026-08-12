import Principia.Architecture.Star10Q267Kernel

namespace PM.Architecture.Star10Q268Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)

/-- Literal left member `(x).φx ⊃ p`; the constant consequent is weakened
explicitly below the binder. -/
def leftRaw (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ :=
  .quantified .always
    (.disj (.neg (ofApparent φ)) (weakenBound (.elementary p)))

/-- Literal right member `(∃x).φx ⊃ p`. -/
def rightRaw (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ :=
  .disj (.neg (.quantified .sometimes (ofApparent φ))) (.elementary p)

def target (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ := equiv (leftRaw φ p) (rightRaw φ p)

def commonRaw (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ :=
  .disj (.quantified .always (.neg (ofApparent φ))) (.elementary p)

/-- Exact closed normalization evidence for both displayed members of
✱10·23.  It is theorem-specific syntax evidence, not a generic assertion
conversion or an equivalence axiom. -/
structure Star_10_23Assertion (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Prop where
  leftReading : NormalizesScoped (leftRaw φ p) (commonRaw φ p)
  rightReading : NormalizesScoped (rightRaw φ p) (commonRaw φ p)
  alternative10_21 :
    Star10Q267Kernel.Star_10_21Assertion p (∼ₐ φ)
  particular : {Ξ : RealContext} → (ψ : Apparent Ξ [.elementaryProposition]) →
    (y : RealVar Ξ .elementaryProposition) →
    Star10Q264Kernel.Star_10_1Assertion ψ y
  targetReading : target φ p = target φ p

def star_10_23 (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Star_10_23Assertion φ p where
  leftReading := NormalizesScoped.disjRightReverse .always
    (.neg (ofApparent φ)) (.elementary p)
  rightReading := NormalizesScoped.disjCongr
    (NormalizesScoped.negSometimes (ofApparent φ)) (.refl _)
  alternative10_21 := Star10Q267Kernel.star_10_21 p (∼ₐ φ)
  particular := fun ψ y => Star10Q264Kernel.star_10_1 ψ y
  targetReading := rfl

end PM.Architecture.Star10Q268Kernel
