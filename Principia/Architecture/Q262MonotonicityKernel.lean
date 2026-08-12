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

inductive Star5Assertion (kind : Quantifier) (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed
      (line1 : PM.Derivation (PM.Elementary.imp
        (Apparent.openHead (matrixImp (Apparent.ofElementary p) (Apparent.ofElementary q)))
        ((Apparent.openHead φ ∨ₚ Apparent.openHead (Apparent.ofElementary p)) ⊃ₚ
          (Apparent.openHead φ ∨ₚ Apparent.openHead (Apparent.ofElementary q)))))
      (permutation : Q261DisjunctionKernel.KernelAssertion kind .inner p q φ)
      (universal : kind = .universal → Star9CanonicalAssertion
        (star_9_21_line7_raw
          (Apparent.ofElementary p ∨ₐ φ) (Apparent.ofElementary q ∨ₐ φ)))
      (existential : kind = .existential → Star922Kernel.Star922KernelAssertion
        (Apparent.ofElementary p ∨ₐ φ) (Apparent.ofElementary q ∨ₐ φ))
      (reading : star5Target kind p q φ = star5Target kind p q φ) :
      Star5Assertion kind p q φ

inductive Star51Assertion (kind : Quantifier) (p r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed
      (pointwise : PM.Derivation (((Apparent.openHead φ) ⊃ₚ
        Apparent.openHead (Apparent.ofElementary p)) ⊃ₚ
        ((Apparent.openHead (Apparent.ofElementary r) ∨ₚ Apparent.openHead φ) ⊃ₚ
          (Apparent.openHead (Apparent.ofElementary r) ∨ₚ
            Apparent.openHead (Apparent.ofElementary p)))))
      (permutation : Q261DisjunctionKernel.KernelAssertion kind .middle r p φ)
      (reading : star51Target kind p r φ = star51Target kind p r φ) :
      Star51Assertion kind p r φ

inductive Star52Assertion (kind : Quantifier) (q r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop where
  | printed
      (line1 : PM.Derivation (((Apparent.openHead φ) ⊃ₚ
        Apparent.openHead (Apparent.ofElementary q)) ⊃ₚ
        ((Apparent.openHead (Apparent.ofElementary r) ∨ₚ Apparent.openHead φ) ⊃ₚ
          (Apparent.openHead (Apparent.ofElementary r) ∨ₚ
            Apparent.openHead (Apparent.ofElementary q)))))
      (permutation : Q261DisjunctionKernel.KernelAssertion kind .middle r q φ)
      (universal : kind = .universal → Star9CanonicalAssertion
        (star_9_21_line7_raw (φ ∨ₐ Apparent.ofElementary r)
          (Apparent.ofElementary q ∨ₐ Apparent.ofElementary r)))
      (existential : kind = .existential → Star922Kernel.Star922KernelAssertion
        (φ ∨ₐ Apparent.ofElementary r)
          (Apparent.ofElementary q ∨ₐ Apparent.ofElementary r))
      (reading : star52Target kind q r φ = star52Target kind q r φ) :
      Star52Assertion kind q r φ

def derive5 (kind : Quantifier) (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star5Assertion kind p q φ :=
  .printed (PM.Derivation.star_1_6
      (Apparent.openHead φ) (Apparent.openHead (Apparent.ofElementary p))
      (Apparent.openHead (Apparent.ofElementary q)))
    (by cases kind <;> first | exact Q261DisjunctionKernel.deriveUniversal .inner p q φ
                             | exact Q261DisjunctionKernel.deriveExistential .inner p q φ)
    (fun h => by subst kind; exact Star9KernelAssertion.star_9_21 _ _)
    (fun h => by subst kind; exact Star922Kernel.derive _ _) rfl

def derive51 (kind : Quantifier) (p r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star51Assertion kind p r φ :=
  .printed (PM.Derivation.star_1_6
      (Apparent.openHead (Apparent.ofElementary r)) (Apparent.openHead φ)
      (Apparent.openHead (Apparent.ofElementary p)))
    (by cases kind <;> first | exact Q261DisjunctionKernel.deriveUniversal .middle r p φ
                             | exact Q261DisjunctionKernel.deriveExistential .middle r p φ) rfl

def derive52 (kind : Quantifier) (q r : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Star52Assertion kind q r φ :=
  .printed (PM.Derivation.star_1_6
      (Apparent.openHead (Apparent.ofElementary r)) (Apparent.openHead φ)
      (Apparent.openHead (Apparent.ofElementary q)))
    (by cases kind <;> first | exact Q261DisjunctionKernel.deriveUniversal .middle r q φ
                             | exact Q261DisjunctionKernel.deriveExistential .middle r q φ)
    (fun h => by subst kind; exact Star9KernelAssertion.star_9_21 _ _)
    (fun h => by subst kind; exact Star922Kernel.derive _ _) rfl

def star_9_5 (p q : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  derive5 .universal p q φ
def star_9_501 (p q : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  derive5 .existential p q φ
def star_9_51 (p r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  derive51 .universal p r φ
def star_9_511 (p r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  derive51 .existential p r φ
def star_9_52 (q r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  derive52 .universal q r φ
def star_9_521 (q r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  derive52 .existential q r φ

end PM.Architecture.Q262MonotonicityKernel
