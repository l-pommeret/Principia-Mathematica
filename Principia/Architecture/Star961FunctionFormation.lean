import Principia.Architecture.Star96SameType

namespace PM.FirstEdition.Volume1.Star9

/-- A PM elementary function is represented intensionally by its capture-safe
matrix.  The argument-place list is part of its type. -/
abbrev ElementaryFunction (Γ : PM.RealContext) (Δ : PM.BoundContext) :=
  PM.Apparent Γ Δ

/-- PM I ✱9·61: pointwise disjunction of two functions with the same argument
places is again a function with exactly those places. -/
def star_9_61 (φ ψ : ElementaryFunction Γ Δ) : ElementaryFunction Γ Δ :=
  PM.Apparent.disj φ ψ

/-- The two functions asserted to exist at ✱9·62.  The free `x` place is
retained; `y` is closed once by the primitive always/sometimes binders. -/
structure Star_9_62Functions (Γ : PM.RealContext) where
  alwaysDisj : PM.FirstOrder Γ [.elementaryProposition]
  sometimesDisj : PM.FirstOrder Γ [.elementaryProposition]

/-- PM I ✱9·62, with the shared `x` argument type enforced by the indices. -/
def star_9_62
    (φ : ElementaryFunction Γ [.elementaryProposition, .elementaryProposition])
    (ψ : ElementaryFunction Γ [.elementaryProposition]) : Star_9_62Functions Γ where
  alwaysDisj := PM.FirstOrder.disjRightMatrix (PM.FirstOrder.always φ) ψ
  sometimesDisj := PM.FirstOrder.disjRightMatrix (PM.FirstOrder.sometimes φ) ψ

/-- The four explicit always/sometimes combinations covered by the printed
“etc.” in ✱9·63, all retaining the same free `x` argument place. -/
structure Star_9_63Functions (Γ : PM.RealContext) where
  alwaysAlways : PM.FirstOrderMatrix Γ [.elementaryProposition]
  alwaysSometimes : PM.FirstOrderMatrix Γ [.elementaryProposition]
  sometimesAlways : PM.FirstOrderMatrix Γ [.elementaryProposition]
  sometimesSometimes : PM.FirstOrderMatrix Γ [.elementaryProposition]

/-- PM I ✱9·63.  Both binary matrices have the same indexed argument places;
the two bound places are closed independently before disjunction. -/
def star_9_63
    (φ ψ : ElementaryFunction Γ [.elementaryProposition, .elementaryProposition]) :
    Star_9_63Functions Γ where
  alwaysAlways := .disj (.quantified (.always φ)) (.quantified (.always ψ))
  alwaysSometimes := .disj (.quantified (.always φ)) (.quantified (.sometimes ψ))
  sometimesAlways := .disj (.quantified (.sometimes φ)) (.quantified (.always ψ))
  sometimesSometimes := .disj (.quantified (.sometimes φ)) (.quantified (.sometimes ψ))

end PM.FirstEdition.Volume1.Star9
