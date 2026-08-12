import Principia.Architecture.Star10Definitions
import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.Star10Q273Targets

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def all (p : Raw Γ) : Raw Γ := .quantified .always p
private def some (p : Raw Γ) : Raw Γ := .quantified .sometimes p

private def formalEquiv (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  all (equiv (ofApparent φ) (ofApparent ψ))

/-- Exact Raw statement of PM I ✱10·413. -/
def star_10_413_target (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (formalEquiv φ χ) (formalEquiv ψ θ))
    (formalEquiv (Apparent.disj (.neg φ) ψ)
      (Apparent.disj (.neg χ) θ))

/-- Exact Raw statement of PM I ✱10·414. -/
def star_10_414_target (φ χ ψ θ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (conj (formalEquiv φ χ) (formalEquiv ψ θ))
    (all (equiv (equiv (ofApparent φ) (ofApparent ψ))
      (equiv (ofApparent χ) (ofApparent θ))))

/-- Exact Raw statement of PM I ✱10·42. -/
def star_10_42_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  equiv (.disj (some (ofApparent φ)) (some (ofApparent ψ)))
    (some (.disj (ofApparent φ) (ofApparent ψ)))

/-- Exact Raw statement of PM I ✱10·43. The source uses distinct displayed
real values; they are explicit parameters, never semantic substitution. -/
def star_10_43_target (φ ψ : Apparent Γ [.elementaryProposition])
    (x z : RealVar Γ .elementaryProposition) : Raw Γ :=
  imp (formalEquiv φ
      (Apparent.ofElementary (Apparent.atReal ψ z) : Apparent Γ [.elementaryProposition]))
    (equiv (.elementary (Apparent.atReal φ x))
      (formalEquiv
        (Apparent.ofElementary (Apparent.atReal φ z) : Apparent Γ [.elementaryProposition]) ψ))

/-- Exact Raw statement of PM I ✱10·5. -/
def star_10_5_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (some (conj (ofApparent φ) (ofApparent ψ)))
    (conj (some (ofApparent φ)) (some (ofApparent ψ)))

end PM.Architecture.Star10Q273Targets
