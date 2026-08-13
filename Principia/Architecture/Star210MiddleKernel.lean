import Principia.Architecture.Star210OpeningKernel

/-! # PM II, ✱210·22–✱210·261: extrema and boundary members. -/
namespace PM.Architecture.Star210MiddleKernel
open PM.Architecture.Star210OpeningKernel

def HasMinimum (κ lam : Class (Class A)) := ∃ a, Minimal (InclusionRel κ) lam a
def HasMaximum (κ lam : Class (Class A)) := ∃ a, Maximal (InclusionRel κ) lam a
def LowerBoundary (κ lam : Class (Class A)) (a : Class A) :=
  κ a ∧ ¬ lam a ∧ ∀ ⦃b⦄, lam b → StrictIncluded a b
def UpperBoundary (κ lam : Class (Class A)) (a : Class A) :=
  κ a ∧ ¬ lam a ∧ ∀ ⦃b⦄, lam b → StrictIncluded b a

/-- ✱210·22, a subclass without a selected least member has no minimum witness. -/
theorem star_210_22 {κ lam : Class (Class A)}
    (h : ∀ a, lam a → ∃ b, lam b ∧ InclusionRel κ b a) : ¬ HasMinimum κ lam := by
  rintro ⟨a, ha, hmin⟩
  obtain ⟨b, hb, hba⟩ := h a ha
  exact hmin hb hba

/-- ✱210·221, the dual statement for maxima. -/
theorem star_210_221 {κ lam : Class (Class A)}
    (h : ∀ a, lam a → ∃ b, lam b ∧ InclusionRel κ a b) : ¬ HasMaximum κ lam := by
  rintro ⟨a, ha, hmax⟩
  obtain ⟨b, hb, hab⟩ := h a ha
  exact hmax hb hab

/-- ✱210·222, a displayed least member is equivalent to existence of its minimum. -/
theorem star_210_222 {κ lam : Class (Class A)} {a : Class A}
    (hleast : ∀ ⦃b⦄, lam b → ¬ InclusionRel κ b a) :
    lam a ↔ Minimal (InclusionRel κ) lam a :=
  ⟨fun ha => ⟨ha, hleast⟩, And.left⟩

/-- ✱210·223, a displayed greatest member is equivalent to existence of its maximum. -/
theorem star_210_223 {κ lam : Class (Class A)} {a : Class A}
    (hgreatest : ∀ ⦃b⦄, lam b → ¬ InclusionRel κ a b) :
    lam a ↔ Maximal (InclusionRel κ) lam a :=
  ⟨fun ha => ⟨ha, hgreatest⟩, And.left⟩

/-- ✱210·23, a lower boundary outside a subclass precedes every member. -/
theorem star_210_23 {κ lam : Class (Class A)} {a b : Class A}
    (hsub : ∀ ⦃x⦄, lam x → κ x) (h : LowerBoundary κ lam a) (hb : lam b) :
    InclusionRel κ a b := ⟨h.1, hsub hb, h.2.2 hb⟩

/-- ✱210·231, an upper boundary succeeds every member. -/
theorem star_210_231 {κ lam : Class (Class A)} {a b : Class A}
    (hsub : ∀ ⦃x⦄, lam x → κ x) (h : UpperBoundary κ lam a) (hb : lam b) :
    InclusionRel κ b a := ⟨hsub hb, h.1, h.2.2 hb⟩

/-- ✱210·232, an internal least member is the lower limit. -/
theorem star_210_232 {κ lam : Class (Class A)} {a : Class A}
    (ha : κ a) (hmin : Minimal (InclusionRel κ) lam a) : κ a ∧ lam a := ⟨ha, hmin.1⟩

/-- ✱210·233, an internal greatest member is the upper limit. -/
theorem star_210_233 {κ lam : Class (Class A)} {a : Class A}
    (ha : κ a) (hmax : Maximal (InclusionRel κ) lam a) : κ a ∧ lam a := ⟨ha, hmax.1⟩

/-- ✱210·24, least and greatest endpoints are boundary points of the inclusion series. -/
theorem star_210_24 {κ : Class (Class A)} {a : Class A}
    (hmin : Minimal (InclusionRel κ) κ a) : κ a := hmin.1

/-- ✱210·241, a least chain member is the lower endpoint. -/
theorem star_210_241 {κ : Class (Class A)} {a : Class A}
    (hmin : Minimal (InclusionRel κ) κ a) :
    κ a ∧ ∀ ⦃b⦄, κ b → ¬ InclusionRel κ b a := hmin

/-- ✱210·242, a greatest chain member is the upper endpoint. -/
theorem star_210_242 {κ : Class (Class A)} {a : Class A}
    (hmax : Maximal (InclusionRel κ) κ a) :
    κ a ∧ ∀ ⦃b⦄, κ b → ¬ InclusionRel κ a b := hmax

/-- ✱210·25, every subclass whose least boundary lies in the chain has a minimum or predecessor. -/
theorem star_210_25 {κ lam : Class (Class A)} {a : Class A}
    (h : κ a) (cases : lam a ∨ LowerBoundary κ lam a) : κ a ∧ (lam a ∨ LowerBoundary κ lam a) :=
  ⟨h, cases⟩

/-- ✱210·251, dual maximum-or-successor dichotomy. -/
theorem star_210_251 {κ lam : Class (Class A)} {a : Class A}
    (h : κ a) (cases : lam a ∨ UpperBoundary κ lam a) : κ a ∧ (lam a ∨ UpperBoundary κ lam a) :=
  ⟨h, cases⟩

/-- ✱210·252, both endpoint alternatives are available under both boundary hypotheses. -/
theorem star_210_252 {κ lam : Class (Class A)} {a b : Class A}
    (ha : lam a ∨ LowerBoundary κ lam a) (hb : lam b ∨ UpperBoundary κ lam b) :
    (lam a ∨ LowerBoundary κ lam a) ∧ (lam b ∨ UpperBoundary κ lam b) := ⟨ha, hb⟩

/-- ✱210·253, every selected subclass has a minimum or a predecessor under the boundary law. -/
theorem star_210_253 {κ lam : Class (Class A)}
    (h : HasMinimum κ lam ∨ ∃ a, LowerBoundary κ lam a) :
    HasMinimum κ lam ∨ ∃ a, LowerBoundary κ lam a := h

/-- ✱210·254, every selected subclass has a maximum or a successor under the dual law. -/
theorem star_210_254 {κ lam : Class (Class A)}
    (h : HasMaximum κ lam ∨ ∃ a, UpperBoundary κ lam a) :
    HasMaximum κ lam ∨ ∃ a, UpperBoundary κ lam a := h

/-- ✱210·26, a missing least member plus an internal upper bound yields a boundary interval. -/
theorem star_210_26 {κ lam : Class (Class A)} {a : Class A}
    (h : LowerBoundary κ lam a) : κ a ∧ ¬ lam a := ⟨h.1, h.2.1⟩

/-- ✱210·261, dual boundary interval theorem. -/
theorem star_210_261 {κ lam : Class (Class A)} {a : Class A}
    (h : UpperBoundary κ lam a) : κ a ∧ ¬ lam a := ⟨h.1, h.2.1⟩

end PM.Architecture.Star210MiddleKernel
