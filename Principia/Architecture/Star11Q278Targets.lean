import Principia.Architecture.CanonicalOrderedAdapters
import Principia.Architecture.Star11Q275Definitions

namespace PM.Architecture.Star11Q278Targets

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)

/-- Exchange the two leading apparent variables, leaving the tail fixed. -/
def swapTwo : Apparent.Renaming
    [.elementaryProposition, .elementaryProposition]
    [.elementaryProposition, .elementaryProposition]
  | .zero => .succ .zero
  | .succ .zero => .zero

/-- The cyclic renaming printed at ✱11·21: `(x,y,z)` becomes `(y,z,x)`. -/
def rotateThree : Apparent.Renaming
    [.elementaryProposition, .elementaryProposition, .elementaryProposition]
    [.elementaryProposition, .elementaryProposition, .elementaryProposition]
  | .zero => .succ .zero
  | .succ .zero => .succ (.succ .zero)
  | .succ (.succ .zero) => .zero

private def allTwo
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  ofSecondOrder (.always (.always φ))

private def allThree
    (φ : Apparent Γ
      [.elementaryProposition, .elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always (.quantified .always (ofApparent φ)))

private def someTwo
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  ofSecondOrder (.sometimes (.sometimes φ))

private def someThree
    (φ : Apparent Γ
      [.elementaryProposition, .elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .sometimes (.quantified .sometimes
    (.quantified .sometimes (ofApparent φ)))

/-- Exact canonical endpoint of PM I ✱11·2. -/
def star_11_2_target
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (allTwo φ) (allTwo (Apparent.rename swapTwo φ))

/-- Exact canonical endpoint of PM I ✱11·21. -/
def star_11_21_target
    (φ : Apparent Γ
      [.elementaryProposition, .elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (allThree φ) (allThree (Apparent.rename rotateThree φ))

/-- Literal right member of ✱11·22, retaining the printed outer negation and
the inner matrix negation. `smartNeg` performs precisely the two primitive
quantifier-negation reductions. -/
def star_11_22_rhs
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  smartNeg (allTwo (Apparent.neg φ))

/-- Exact canonical endpoint of PM I ✱11·22. -/
def star_11_22_target
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (someTwo φ) (star_11_22_rhs φ)

/-- Kernel-checked definitional expansion used by ✱11·22.  This is deliberately
not mislabeled as a derivation of the displayed equivalence. -/
theorem star_11_22_definition
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) :
    star_11_22_rhs φ =
      .quantified .sometimes (.quantified .sometimes
        (.neg (.neg (ofApparent φ)))) := rfl

/-- Exact canonical endpoint of PM I ✱11·23. -/
def star_11_23_target
    (φ : Apparent Γ [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (someTwo φ) (someTwo (Apparent.rename swapTwo φ))

/-- Exact canonical endpoint of PM I ✱11·24. -/
def star_11_24_target
    (φ : Apparent Γ
      [.elementaryProposition, .elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (someThree φ) (someThree (Apparent.rename rotateThree φ))

end PM.Architecture.Star11Q278Targets
