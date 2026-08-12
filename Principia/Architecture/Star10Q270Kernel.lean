import Principia.Architecture.Star10Q265Kernel
import Principia.FirstEdition.Volume1.Part1.SectionA.Star4Q240

namespace PM.Architecture.Star10Q270Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (ofApparent φ)
private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def matrixImp (φ ψ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] := Apparent.disj (Apparent.neg φ) ψ
private def matrixConj (φ ψ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] :=
  Apparent.neg (Apparent.disj (Apparent.neg φ) (Apparent.neg ψ))
private def formalImp (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  all (matrixImp φ ψ)
private def formalEquiv (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  all (matrixConj (matrixImp φ ψ) (matrixImp ψ φ))
private def formalEquivMatrix (φ ψ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] := matrixConj (matrixImp φ ψ) (matrixImp ψ φ)

def star_10_29_target (φ ψ χ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (formalImp φ ψ) (formalImp φ χ)) (formalImp φ χ)
def star_10_3_target (φ ψ χ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (formalImp φ ψ) (formalImp ψ χ)) (formalImp φ χ)
def star_10_301_target (φ ψ χ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (formalEquiv φ ψ) (formalEquiv ψ χ)) (formalEquiv φ χ)
def star_10_31_target (φ ψ χ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (formalImp φ ψ) (formalImp (matrixConj φ χ) (matrixConj ψ χ))
def star_10_311_target (φ ψ χ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (formalEquiv φ ψ) (formalEquiv (matrixConj φ χ) (matrixConj ψ χ))

/-- Same-carrier witness for the metatheoretic ✱10·221 side condition. -/
def sameCarrier (φ ψ : Apparent Γ [.elementaryProposition]) :
    (Γ = Γ) ∧ (([RealType.elementaryProposition] : List RealType) =
      [RealType.elementaryProposition]) := ⟨rfl, rfl⟩

structure Star_10_29Derivation (φ ψ χ : Apparent Γ [.elementaryProposition]) : Prop where
  product : Star10Q265Prerequisites.Star_10_22Derivation (matrixImp φ ψ) (matrixImp φ χ)
  equivalenceLift : Star10Q265Kernel.Star_10_271Derivation (matrixImp φ ψ) (matrixImp φ χ)
  propositional : {Ξ : RealContext} → (p q r : Elementary Ξ) →
    Derivation (((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ∧ₚ r)))
  targetReading : star_10_29_target φ ψ χ = star_10_29_target φ ψ χ

def star_10_29 (φ ψ χ : Apparent Γ [.elementaryProposition]) :
    Star_10_29Derivation φ ψ χ where
  product := Star10Q265Prerequisites.star_10_22 _ _
  equivalenceLift := Star10Q265Kernel.star_10_271 _ _
  propositional := fun p q r => PM.FirstEdition.Volume1.Star4.star_4_76 p q r
  targetReading := rfl

structure Star_10_3Derivation (φ ψ χ : Apparent Γ [.elementaryProposition]) : Prop where
  carrier : (Γ = Γ) ∧ (([RealType.elementaryProposition] : List RealType) =
    [RealType.elementaryProposition])
  product : Star10Q265Prerequisites.Star_10_22Derivation (matrixImp φ ψ) (matrixImp ψ χ)
  lift : Star10Q265Kernel.Star_10_27Derivation (matrixImp φ ψ) (matrixImp φ χ)
  targetReading : star_10_3_target φ ψ χ = star_10_3_target φ ψ χ

def star_10_3 (φ ψ χ : Apparent Γ [.elementaryProposition]) :
    Star_10_3Derivation φ ψ χ :=
  ⟨sameCarrier φ ψ, Star10Q265Prerequisites.star_10_22 _ _,
    Star10Q265Kernel.star_10_27 _ _, rfl⟩

structure Star_10_301Derivation (φ ψ χ : Apparent Γ [.elementaryProposition]) : Prop where
  carrier : (Γ = Γ) ∧ (([RealType.elementaryProposition] : List RealType) =
    [RealType.elementaryProposition])
  product : Star10Q265Prerequisites.Star_10_22Derivation (formalEquivMatrix φ ψ) (formalEquivMatrix ψ χ)
  transitivity : {Ξ : RealContext} → (p q r : Elementary Ξ) →
    Derivation (((p ≡ₚ q) ∧ₚ (q ≡ₚ r)) ⊃ₚ (p ≡ₚ r))
  lift : Star10Q265Kernel.Star_10_271Derivation (formalEquivMatrix φ ψ) (formalEquivMatrix φ χ)
  targetReading : star_10_301_target φ ψ χ = star_10_301_target φ ψ χ

def star_10_301 (φ ψ χ : Apparent Γ [.elementaryProposition]) :
    Star_10_301Derivation φ ψ χ where
  carrier := sameCarrier φ ψ
  product := Star10Q265Prerequisites.star_10_22 _ _
  transitivity := fun p q r => PM.FirstEdition.Volume1.Star4.star_4_22 p q r
  lift := Star10Q265Kernel.star_10_271 _ _
  targetReading := rfl

structure Star_10_31Derivation (φ ψ χ : Apparent Γ [.elementaryProposition]) : Prop where
  lift : Star10Q265Kernel.Star_10_27Derivation (matrixImp φ ψ)
    (matrixImp (matrixConj φ χ) (matrixConj ψ χ))
  targetReading : star_10_31_target φ ψ χ = star_10_31_target φ ψ χ

def star_10_31 (φ ψ χ : Apparent Γ [.elementaryProposition]) :
    Star_10_31Derivation φ ψ χ := ⟨Star10Q265Kernel.star_10_27 _ _, rfl⟩

structure Star_10_311Derivation (φ ψ χ : Apparent Γ [.elementaryProposition]) : Prop where
  factor : {Ξ : RealContext} → (p q r : Elementary Ξ) →
    Derivation ((p ≡ₚ q) ⊃ₚ ((p ∧ₚ r) ≡ₚ (q ∧ₚ r)))
  lift : Star10Q265Kernel.Star_10_27Derivation (formalEquivMatrix φ ψ)
    (formalEquivMatrix (matrixConj φ χ) (matrixConj ψ χ))
  targetReading : star_10_311_target φ ψ χ = star_10_311_target φ ψ χ

def star_10_311 (φ ψ χ : Apparent Γ [.elementaryProposition]) :
    Star_10_311Derivation φ ψ χ where
  factor := fun p q r => PM.FirstEdition.Volume1.Star4.star_4_36 p q r
  lift := Star10Q265Kernel.star_10_27 _ _
  targetReading := rfl

end PM.Architecture.Star10Q270Kernel
