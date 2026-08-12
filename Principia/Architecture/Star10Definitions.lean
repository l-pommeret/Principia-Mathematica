import Principia.Syntax.Apparent

namespace PM.Architecture.Star10Definitions

private def matrixImp (φ ψ : PM.Apparent Γ Δ) : PM.Apparent Γ Δ :=
  .disj (.neg φ) ψ

private def matrixConj (φ ψ : PM.Apparent Γ Δ) : PM.Apparent Γ Δ :=
  .neg (.disj (.neg φ) (.neg ψ))

private def matrixEquiv (φ ψ : PM.Apparent Γ Δ) : PM.Apparent Γ Δ :=
  matrixConj (matrixImp φ ψ) (matrixImp ψ φ)

/-- PM I ✱10·01: `(∃x).φx .=. ∼(x).∼φx  Df`. -/
abbrev star_10_01 {Γ Δ}
    (φ : PM.Apparent Γ (.elementaryProposition :: Δ)) : PM.FirstOrder Γ Δ :=
  PM.FirstOrder.neg (PM.FirstOrder.always (.neg φ))

/-- PM I ✱10·02: `φx ⊃ₓ ψx .=. (x).φx ⊃ ψx  Df`. -/
abbrev star_10_02 {Γ Δ}
    (φ ψ : PM.Apparent Γ (.elementaryProposition :: Δ)) : PM.FirstOrder Γ Δ :=
  PM.FirstOrder.always (matrixImp φ ψ)

/-- PM I ✱10·03: `φx ≡ₓ ψx .=. (x).φx ≡ ψx  Df`. -/
abbrev star_10_03 {Γ Δ}
    (φ ψ : PM.Apparent Γ (.elementaryProposition :: Δ)) : PM.FirstOrder Γ Δ :=
  PM.FirstOrder.always (matrixEquiv φ ψ)

end PM.Architecture.Star10Definitions
