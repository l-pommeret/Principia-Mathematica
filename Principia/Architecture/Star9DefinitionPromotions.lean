import Principia.Syntax.Apparent

namespace PM.Architecture.Star9DefinitionPromotions

open PM

/-- Canonical declaration for PM I ✱9·03. -/
theorem star_9_03 (body : Apparent Γ (.elementaryProposition :: Δ))
    (p : Elementary Γ) :
    FirstOrder.disjRightElementary (FirstOrder.always body) p =
      FirstOrder.always (body ∨ₐ Apparent.ofElementary p) :=
  FirstOrder.star_9_03_reduction body p

/-- Canonical declaration for PM I ✱9·04. -/
theorem star_9_04 (p : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder.disjElementaryLeft p (FirstOrder.always body) =
      FirstOrder.always (Apparent.ofElementary p ∨ₐ body) :=
  FirstOrder.star_9_04_reduction p body

/-- Canonical declaration for PM I ✱9·05. -/
theorem star_9_05 (body : Apparent Γ (.elementaryProposition :: Δ))
    (p : Elementary Γ) :
    FirstOrder.disjRightElementary (FirstOrder.sometimes body) p =
      FirstOrder.sometimes (body ∨ₐ Apparent.ofElementary p) :=
  FirstOrder.star_9_05_reduction body p

/-- Canonical declaration for PM I ✱9·06. -/
theorem star_9_06 (p : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder.disjElementaryLeft p (FirstOrder.sometimes body) =
      FirstOrder.sometimes (Apparent.ofElementary p ∨ₐ body) :=
  FirstOrder.star_9_06_reduction p body

/-- Canonical declaration for PM I ✱9·07. -/
theorem star_9_07 (φ ψ : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder.disjAlwaysSometimes φ ψ =
      Quantified.always (Quantified.sometimes
        (Apparent.rename Apparent.outerVariableRenaming φ ∨ₐ
          Apparent.rename Apparent.innerVariableRenaming ψ)) :=
  FirstOrder.star_9_07_reduction φ ψ

/-- Canonical declaration for PM I ✱9·08. -/
theorem star_9_08 (ψ φ : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder.disjSometimesAlways ψ φ =
      Quantified.always (Quantified.sometimes
        (Apparent.rename Apparent.innerVariableRenaming ψ ∨ₐ
          Apparent.rename Apparent.outerVariableRenaming φ)) :=
  FirstOrder.star_9_08_reduction ψ φ

end PM.Architecture.Star9DefinitionPromotions
