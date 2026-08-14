import Principia.Architecture.Q261DisjunctionKernel

namespace PM.Architecture.Q262MonotonicityKernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.Star921MatrixKernel
open PM.Architecture.CanonicalOrderedAdapters
open PM.CanonicalOrderedFormula

abbrev Quantifier := Q261DisjunctionKernel.Quantifier

def quantifiedRaw (kind : Quantifier)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  Q261DisjunctionKernel.quantifiedRaw kind φ

def impRaw (p q : Raw Γ) : Raw Γ := .disj (.neg p) q

def star5Target (kind : Quantifier) (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  impRaw (impRaw (.elementary p) (.elementary q))
    (impRaw (.disj (.elementary p) (quantifiedRaw kind φ))
      (.disj (.elementary q) (quantifiedRaw kind φ)))

def star51Target (kind : Quantifier) (p r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  impRaw (impRaw (.elementary p) (quantifiedRaw kind φ))
    (impRaw (.disj (.elementary p) (.elementary r))
      (.disj (quantifiedRaw kind φ) (.elementary r)))

def star52Target (kind : Quantifier) (q r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  impRaw (impRaw (quantifiedRaw kind φ) (.elementary q))
    (impRaw (.disj (quantifiedRaw kind φ) (.elementary r))
      (.disj (.elementary q) (.elementary r)))

/- No assertion or prerequisite package is exported here.  The former six
numbered declarations and their three Prop-valued constructor families were
not derivations of these targets and have been removed.  Formalization is
blocked until the source-scoped first-order detachment used by the printed
demonstrations is itself kernel-derived. -/

end PM.Architecture.Q262MonotonicityKernel
