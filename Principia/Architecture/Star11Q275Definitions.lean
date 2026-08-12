import Principia.Architecture.Star10Definitions

namespace PM.Architecture.Star11Q275Definitions

private def matrixImp (φ ψ : Apparent Γ Δ) : Apparent Γ Δ :=
  .disj (.neg φ) ψ

/-- PM I ✱11·01: `(x,y).φ(x,y) := (x)(y).φ(x,y)`. Bound-variable order is
represented by the two successive typed `always` constructors. -/
abbrev star_11_01 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : SecondOrder Γ [] :=
  .always (.always φ)

/-- PM I ✱11·02: three successive universal binders. -/
abbrev star_11_02 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition, .elementaryProposition]) :
    Quantified (SecondOrder Γ) [] :=
  .always (.always (.always φ))

/-- PM I ✱11·03: two successive existential binders. -/
abbrev star_11_03 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : SecondOrder Γ [] :=
  .sometimes (.sometimes φ)

/-- PM I ✱11·04: three successive existential binders. -/
abbrev star_11_04 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition, .elementaryProposition]) :
    Quantified (SecondOrder Γ) [] :=
  .sometimes (.sometimes (.sometimes φ))

/-- PM I ✱11·05: pointwise implication beneath the exact two universal
binders defined at ✱11·01. -/
abbrev star_11_05 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : SecondOrder Γ [] :=
  .always (.always (matrixImp φ ψ))

end PM.Architecture.Star11Q275Definitions
