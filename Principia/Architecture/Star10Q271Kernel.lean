import Principia.Architecture.Star10Q269Kernel

namespace PM.Architecture.Star10Q271Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters
open PM.Architecture.CanonicalNormalization

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (ofApparent φ)
private def some (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .sometimes (ofApparent φ)

def star_10_33_target (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ :=
  equiv (.quantified .always
    (conj (ofApparent φ) (weakenBound (.elementary p))))
    (conj (all φ) (.elementary p))

def star_10_34_left (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ :=
  .quantified .sometimes
    (imp (ofApparent φ) (weakenBound (.elementary p)))
def star_10_34_right (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ := imp (all φ) (.elementary p)
def star_10_34_target (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ := equiv (star_10_34_left φ p) (star_10_34_right φ p)

structure Star_10_34Assertion (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Prop where
  extraction : NormalizesScoped (star_10_34_left φ p)
    (.disj (.quantified .sometimes (.neg (ofApparent φ))) (.elementary p))
  deMorgan : NormalizesScoped
    (.disj (.quantified .sometimes (.neg (ofApparent φ))) (.elementary p))
    (star_10_34_right φ p)
  reading : star_10_34_target φ p = star_10_34_target φ p

def star_10_34 (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Star_10_34Assertion φ p where
  extraction := .disjRightReverse .sometimes (.neg (ofApparent φ)) (.elementary p)
  deMorgan := .disjCongr (.negAlwaysReverse (ofApparent φ)) (.refl _)
  reading := rfl

def star_10_36_left (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ :=
  .quantified .sometimes (.disj (ofApparent φ) (weakenBound (.elementary p)))
def star_10_36_right (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ := .disj (some φ) (.elementary p)
def star_10_36_target (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Raw Γ := equiv (star_10_36_left φ p) (star_10_36_right φ p)

structure Star_10_36Assertion (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Prop where
  extraction : NormalizesScoped (star_10_36_left φ p) (star_10_36_right φ p)
  reading : star_10_36_target φ p = star_10_36_target φ p

def star_10_36 (φ : Apparent Γ [.elementaryProposition])
    (p : Elementary Γ) : Star_10_36Assertion φ p :=
  ⟨.disjRightReverse .sometimes (ofApparent φ) (.elementary p), rfl⟩

def star_10_37_left (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .sometimes
    (imp (weakenBound (.elementary p)) (ofApparent φ))
def star_10_37_right (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (.elementary p) (some φ)
def star_10_37_target (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (star_10_37_left p φ) (star_10_37_right p φ)

structure Star_10_37Assertion (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  extraction : NormalizesScoped (star_10_37_left p φ) (star_10_37_right p φ)
  reading : star_10_37_target p φ = star_10_37_target p φ

def star_10_37 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star_10_37Assertion p φ :=
  ⟨.disjLeftReverse .sometimes (ofApparent φ) (.neg (.elementary p)), rfl⟩

end PM.Architecture.Star10Q271Kernel
