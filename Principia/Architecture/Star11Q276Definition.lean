import Principia.Architecture.Star11Q275Definitions

namespace PM.Architecture.Star11Q276Definition

private def matrixImp (φ ψ : Apparent Γ Δ) : Apparent Γ Δ :=
  .disj (.neg φ) ψ

private def matrixConj (φ ψ : Apparent Γ Δ) : Apparent Γ Δ :=
  .neg (.disj (.neg φ) (.neg ψ))

private def matrixEquiv (φ ψ : Apparent Γ Δ) : Apparent Γ Δ :=
  matrixConj (matrixImp φ ψ) (matrixImp ψ φ)

/-- PM I ✱11·06: pointwise equivalence beneath exactly the two universal
binders introduced by ✱11·01. -/
abbrev star_11_06 (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : SecondOrder Γ [] :=
  .always (.always (matrixEquiv φ ψ))

end PM.Architecture.Star11Q276Definition
