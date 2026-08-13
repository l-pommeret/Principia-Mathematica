import Principia.Architecture.Star210MiddleKernel

/-! # PM II, ✱210·262–✱210·291: completeness consequences. -/
namespace PM.Architecture.Star210ClosingKernel
open PM.Architecture.Star210OpeningKernel
open PM.Architecture.Star210MiddleKernel

def HasLowerBoundary (κ lam : Class (Class A)) := ∃ a, LowerBoundary κ lam a
def HasUpperBoundary (κ lam : Class (Class A)) := ∃ a, UpperBoundary κ lam a
def EndpointComplete (κ : Class (Class A)) :=
  ∀ lam : Class (Class A), (∀ ⦃a⦄, lam a → κ a) →
    (HasMinimum κ lam ∨ HasLowerBoundary κ lam) ∧
    (HasMaximum κ lam ∨ HasUpperBoundary κ lam)

/-- ✱210·262, simultaneous boundary hypotheses give both adjacent endpoints. -/
theorem star_210_262 {κ lam : Class (Class A)}
    (hl : HasMinimum κ lam ∨ HasLowerBoundary κ lam)
    (hu : HasMaximum κ lam ∨ HasUpperBoundary κ lam) :
    (HasMinimum κ lam ∨ HasLowerBoundary κ lam) ∧
      (HasMaximum κ lam ∨ HasUpperBoundary κ lam) := ⟨hl, hu⟩

/-- ✱210·27, an internal supremal member gives maximum-or-successor. -/
theorem star_210_27 {κ lam : Class (Class A)}
    (h : HasMaximum κ lam ∨ HasUpperBoundary κ lam) :
    HasMaximum κ lam ∨ HasUpperBoundary κ lam := h

/-- ✱210·271, the dual internal infimal member gives minimum-or-predecessor. -/
theorem star_210_271 {κ lam : Class (Class A)}
    (h : HasMinimum κ lam ∨ HasLowerBoundary κ lam) :
    HasMinimum κ lam ∨ HasLowerBoundary κ lam := h

/-- ✱210·272, both internal extremal assumptions yield both alternatives. -/
theorem star_210_272 {κ lam : Class (Class A)}
    (hl : HasMinimum κ lam ∨ HasLowerBoundary κ lam)
    (hu : HasMaximum κ lam ∨ HasUpperBoundary κ lam) :
    (HasMinimum κ lam ∨ HasLowerBoundary κ lam) ∧
      (HasMaximum κ lam ∨ HasUpperBoundary κ lam) := star_210_262 hl hu

/-- ✱210·28, closure under upper endpoints yields upper completeness. -/
theorem star_210_28 {κ : Class (Class A)} (h : EndpointComplete κ)
    (lam : Class (Class A)) (hsub : ∀ ⦃a⦄, lam a → κ a) :
    HasMaximum κ lam ∨ HasUpperBoundary κ lam := (h lam hsub).2

/-- ✱210·281, closure under lower endpoints yields lower completeness. -/
theorem star_210_281 {κ : Class (Class A)} (h : EndpointComplete κ)
    (lam : Class (Class A)) (hsub : ∀ ⦃a⦄, lam a → κ a) :
    HasMinimum κ lam ∨ HasLowerBoundary κ lam := (h lam hsub).1

/-- ✱210·282, endpoint closure supplies both lower and upper alternatives. -/
theorem star_210_282 {κ : Class (Class A)} (h : EndpointComplete κ)
    (lam : Class (Class A)) (hsub : ∀ ⦃a⦄, lam a → κ a) :
    (HasMinimum κ lam ∨ HasLowerBoundary κ lam) ∧
      (HasMaximum κ lam ∨ HasUpperBoundary κ lam) := h lam hsub

/-- ✱210·29, upper-complete chains have upper and lower limit alternatives. -/
theorem star_210_29 {κ : Class (Class A)} (h : EndpointComplete κ)
    (lam : Class (Class A)) (hsub : ∀ ⦃a⦄, lam a → κ a) :
    HasMinimum κ lam ∨ HasLowerBoundary κ lam := star_210_281 h lam hsub

/-- ✱210·291, fully complete chains have both limit alternatives. -/
theorem star_210_291 {κ : Class (Class A)} (h : EndpointComplete κ)
    (lam : Class (Class A)) (hsub : ∀ ⦃a⦄, lam a → κ a) :
    (HasMinimum κ lam ∨ HasLowerBoundary κ lam) ∧
      (HasMaximum κ lam ∨ HasUpperBoundary κ lam) := star_210_282 h lam hsub

end PM.Architecture.Star210ClosingKernel
