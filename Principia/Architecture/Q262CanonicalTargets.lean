import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.Q262CanonicalTargets

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def e (p : Elementary Γ) : Raw Γ :=
  ofApparent (Apparent.ofElementary p : Apparent Γ [])
private def all (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofFirstOrder (FirstOrder.always φ)
private def some (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  ofFirstOrder (FirstOrder.sometimes φ)
private def imp (p q : Raw Γ) : Raw Γ := rawImp p q

/-- Exact canonical Raw target of PM I ✱9·5. -/
def star_9_5_target (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (imp (e p) (e q)) (imp (.disj (e p) (all φ)) (.disj (e q) (all φ)))

/-- Exact canonical Raw target of PM I ✱9·501. -/
def star_9_501_target (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (imp (e p) (e q)) (imp (.disj (e p) (some φ)) (.disj (e q) (some φ)))

/-- Exact canonical Raw target of PM I ✱9·51. -/
def star_9_51_target (p r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (imp (e p) (all φ)) (imp (.disj (e p) (e r)) (.disj (all φ) (e r)))

/-- Exact canonical Raw target of PM I ✱9·511. -/
def star_9_511_target (p r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (imp (e p) (some φ)) (imp (.disj (e p) (e r)) (.disj (some φ) (e r)))

/-- Exact canonical Raw target of PM I ✱9·52. -/
def star_9_52_target (q r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (imp (all φ) (e q)) (imp (.disj (all φ) (e r)) (.disj (e q) (e r)))

/-- Exact canonical Raw target of PM I ✱9·521. -/
def star_9_521_target (q r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  imp (imp (some φ) (e q)) (imp (.disj (some φ) (e r)) (.disj (e q) (e r)))

end PM.Architecture.Q262CanonicalTargets
