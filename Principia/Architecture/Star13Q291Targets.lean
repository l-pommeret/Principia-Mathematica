import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.Star13Q291Targets

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)

/-- PM I ✱13·11, at its exact propositional envelope. The second parameter is
the ramified function-quantified member; canonical `Raw` has no function binder. -/
def star_13_11_target (identityXY formallyEquivalentUnderPhi : Raw Γ) : Raw Γ :=
  equiv identityXY formallyEquivalentUnderPhi

/-- PM I ✱13·12: identity implies equivalence of the displayed values. -/
def star_13_12_target (identityXY psiX psiY : Elementary Γ) : Raw Γ :=
  imp (.elementary identityXY) (equiv (.elementary psiX) (.elementary psiY))

/-- PM I ✱13·13: substitution in its printed conjunctive form. -/
def star_13_13_target (identityXY psiX psiY : Elementary Γ) : Raw Γ :=
  imp (conj (.elementary psiX) (.elementary identityXY)) (.elementary psiY)

/-- PM I ✱13·14: incompatible function values imply non-identity. -/
def star_13_14_target (identityXY psiX psiY : Elementary Γ) : Raw Γ :=
  imp (conj (.elementary psiX) (.neg (.elementary psiY)))
    (.neg (.elementary identityXY))

/-- PM I ✱13·15. This is PM object-language identity, not Lean equality. -/
def star_13_15_target (identityXX : Elementary Γ) : Raw Γ :=
  .elementary identityXX

end PM.Architecture.Star13Q291Targets
