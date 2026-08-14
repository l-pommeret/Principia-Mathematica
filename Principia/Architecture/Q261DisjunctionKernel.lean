import Principia.Architecture.Star921MatrixKernel
import Principia.Architecture.Star922Kernel

namespace PM.Architecture.Q261DisjunctionKernel

open PM.Architecture.FirstOrderPrerequisites
open PM.Architecture.Star921MatrixKernel
open PM.Architecture.CanonicalOrderedAdapters
open PM.CanonicalOrderedFormula

/-! A narrow, source-indexed boundary for the six applications of ✱1·5 and
✱9·21/·22 printed at ✱9·4–·421.  In particular this adds no constructor to
`OrderedAssertion` and no general conversion from canonical Raw syntax. -/

inductive Quantifier where | universal | existential
inductive AssocShape where | outer | middle | inner

def functionPair (shape : AssocShape) (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    Apparent Γ [.elementaryProposition] × Apparent Γ [.elementaryProposition] :=
  match shape with
  | .outer =>
      (Apparent.ofElementary p ∨ₐ (Apparent.ofElementary q ∨ₐ φ),
       Apparent.ofElementary q ∨ₐ (Apparent.ofElementary p ∨ₐ φ))
  | .middle =>
      (Apparent.ofElementary p ∨ₐ (φ ∨ₐ Apparent.ofElementary q),
       φ ∨ₐ (Apparent.ofElementary p ∨ₐ Apparent.ofElementary q))
  | .inner =>
      (φ ∨ₐ (Apparent.ofElementary p ∨ₐ Apparent.ofElementary q),
       Apparent.ofElementary p ∨ₐ (φ ∨ₐ Apparent.ofElementary q))

def quantifiedRaw (kind : Quantifier)
    (φ : Apparent Γ [.elementaryProposition]) : Raw Γ :=
  match kind with
  | .universal => .quantified .always (ofApparent φ)
  | .existential => .quantified .sometimes (ofApparent φ)

def displayedPair (kind : Quantifier) (shape : AssocShape)
    (p q : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :
    Raw Γ × Raw Γ :=
  let P : Raw Γ := .elementary p
  let Q : Raw Γ := .elementary q
  let F := quantifiedRaw kind φ
  let or := Raw.disj
  match shape with
  | .outer => (or P (or Q F), or Q (or P F))
  | .middle => (or P (or F Q), or F (or P Q))
  | .inner => (or F (or P Q), or P (or F Q))

def target (kind : Quantifier) (shape : AssocShape)
    (p q : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :
    Raw Γ :=
  .disj (.neg (displayedPair kind shape p q φ).1)
    (displayedPair kind shape p q φ).2

inductive KernelAssertion (kind : Quantifier) (shape : AssocShape)
    (p q : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) : Prop where
  | universal
      (hkind : kind = .universal)
      (line1 : OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.elementary (Apparent.openHead (matrixImp
          (functionPair shape p q φ).1 (functionPair shape p q φ).2))))
      (reading : target kind shape p q φ = target kind shape p q φ) :
      KernelAssertion kind shape p q φ
  | existential
      (hkind : kind = .existential)
      (line1 : PM.Derivation (Apparent.openHead (matrixImp
        (functionPair shape p q φ).1 (functionPair shape p q φ).2)))
      (line2 : Star922Kernel.Star922KernelAssertion
        (functionPair shape p q φ).1 (functionPair shape p q φ).2)
      (reading : target kind shape p q φ = target kind shape p q φ) :
      KernelAssertion kind shape p q φ

def elementaryLine (shape : AssocShape) (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    PM.Derivation (Apparent.openHead (matrixImp
      (functionPair shape p q φ).1 (functionPair shape p q φ).2)) := by
  cases shape <;> simp [functionPair, matrixImp]
  · exact PM.Derivation.star_1_5 _ _ _
  · exact PM.Derivation.star_1_5 _ _ _
  · exact PM.Derivation.star_1_5 _ _ _

def deriveUniversal (shape : AssocShape) (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    KernelAssertion .universal shape p q φ :=
  .universal rfl (.elementary (elementaryLine shape p q φ)) rfl

def deriveExistential (shape : AssocShape) (p q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    KernelAssertion .existential shape p q φ :=
  .existential rfl (elementaryLine shape p q φ) (Star922Kernel.derive _ _) rfl

def star_9_4 (p q : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  deriveUniversal .outer p q φ
def star_9_401 (p q : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  deriveExistential .outer p q φ
def star_9_41 (p r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  deriveUniversal .middle p r φ
def star_9_411 (p r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  deriveExistential .middle p r φ
def star_9_42 (q r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  deriveUniversal .inner q r φ
def star_9_421 (q r : Elementary Γ) (φ : Apparent Γ [.elementaryProposition]) :=
  deriveExistential .inner q r φ

end PM.Architecture.Q261DisjunctionKernel
