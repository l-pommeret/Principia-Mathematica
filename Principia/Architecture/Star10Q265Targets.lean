import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.Star10Q265Targets

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def e (p : Elementary Γ) : Raw Γ :=
  ofApparent (Apparent.ofElementary p : Apparent Γ [])
private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofFirstOrder (FirstOrder.always φ)
private def some (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofFirstOrder (FirstOrder.sometimes φ)
private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def formalImp (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (imp (ofApparent φ) (ofApparent ψ))
private def formalEquiv (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  .quantified .always (equiv (ofApparent φ) (ofApparent ψ))

/-- Exact Raw statement of PM I ✱10·27. -/
def star_10_27_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (formalImp φ ψ) (imp (all φ) (all ψ))

/-- Exact Raw statement of PM I ✱10·271. -/
def star_10_271_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (formalEquiv φ ψ) (equiv (all φ) (all ψ))

/-- Exact Raw statement of PM I ✱10·28. -/
def star_10_28_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (formalImp φ ψ) (imp (some φ) (some ψ))

/-- Exact Raw statement of PM I ✱10·281. -/
def star_10_281_target (φ ψ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (formalEquiv φ ψ) (equiv (some φ) (some ψ))

/-- Exact Raw statement of PM I ✱10·35. -/
def star_10_35_target (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  let wp := Apparent.weaken (Apparent.ofElementary p : Apparent Γ [])
  let pφ := Apparent.neg (Apparent.disj (Apparent.neg wp) (Apparent.neg φ))
  equiv (ofFirstOrder (FirstOrder.sometimes pφ)) (conj (e p) (some φ))

end PM.Architecture.Star10Q265Targets
