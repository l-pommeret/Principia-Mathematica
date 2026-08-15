import Principia.Syntax.CanonicalOrderedFormula

namespace PM.Star11

open PM.CanonicalOrderedFormula

/-- Expand an elementary value before substituting it for an apparent
variable.  Kept local to ✱11 so this module depends directly on the pure
canonical syntax. -/
def ofElementaryRaw : Elementary Γ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .var entryVar => .elementary (.var entryVar)
  | .neg proposition => .neg (ofElementaryRaw proposition)
  | .disj left right => .disj (ofElementaryRaw left) (ofElementaryRaw right)

def instantiateBoundAt (cutoff : Nat) (value : Elementary Γ) : Raw Γ → Raw Γ
  | .elementary proposition => .elementary proposition
  | .schema slot => .schema slot
  | .bound index =>
      if index = cutoff then ofElementaryRaw value
      else if cutoff < index then .bound (index - 1) else .bound index
  | .quantified quantifier body =>
      .quantified quantifier (instantiateBoundAt (cutoff + 1) value body)
  | .neg proposition => .neg (instantiateBoundAt cutoff value proposition)
  | .disj left right =>
      .disj (instantiateBoundAt cutoff value left)
        (instantiateBoundAt cutoff value right)

def instantiateHeadRaw (value : Elementary Γ) (body : Raw Γ) : Raw Γ :=
  instantiateBoundAt 0 value body

/-- Exchange the two apparent variables bound at `depth` and `depth + 1`. -/
def swapAdjacentBoundAt (depth : Nat) : Raw Γ → Raw Γ
  | .elementary p => .elementary p
  | .schema slot => .schema slot
  | .bound index =>
      if index = depth then .bound (depth + 1)
      else if index = depth + 1 then .bound depth
      else .bound index
  | .quantified quantifier body =>
      .quantified quantifier (swapAdjacentBoundAt (depth + 1) body)
  | .neg p => .neg (swapAdjacentBoundAt depth p)
  | .disj p q =>
      .disj (swapAdjacentBoundAt depth p) (swapAdjacentBoundAt depth q)

/-- Exchange the two apparent variables immediately surrounding a matrix. -/
def swapHeadPair (body : Raw Γ) : Raw Γ :=
  swapAdjacentBoundAt 0 body

/-- The deduction judgement isolated at ✱11.

Its constructors are exactly the three primitive propositions printed in
✱11.  In particular, ✱11·01–·06 are definitions and add no constructors. -/
inductive Star11Derivation : {Γ : RealContext} → Raw Γ → Prop where
  /-- ✱11·07: the order of two universal apparent variables may be exchanged. -/
  | star_11_07 (body : Raw Γ) :
      Star11Derivation
        (smartImp
          (.quantified .always (.quantified .always body))
          (.quantified .always (.quantified .always (swapHeadPair body))))
  /-- ✱11·1: `⊢ : (x, y).φ(x, y) .⊃ .φ(z, w)`. -/
  | star_11_1 (body : Raw Γ) (z w : Elementary Γ) :
      Star11Derivation
        (smartImp
          (.quantified .always (.quantified .always body))
          (instantiateHeadRaw z (instantiateHeadRaw w body)))
  /-- ✱11·11: universal truth at two arguments licenses double generalization. -/
  | star_11_11 (body : Raw Γ) :
      (∀ z w : Elementary Γ,
        Star11Derivation (instantiateHeadRaw z (instantiateHeadRaw w body))) →
      Star11Derivation (.quantified .always (.quantified .always body))

/-- Short name for the isolated ✱11 judgement. -/
abbrev Assertion {Γ : RealContext} (formula : Raw Γ) : Prop :=
  Star11Derivation formula

/-- Catalogue text tied to the exact raw formula asserted at ✱11. -/
structure Reading (Γ : RealContext) where
  printed : String
  parsed : Raw Γ

def star_11_07_reading (body : Raw Γ) : Reading Γ where
  printed := "“Whatever possible argument x may be, φ(x, y) is true whatever\npossible argument y may be” implies the corresponding statement with x and y\ninterchanged."
  parsed := smartImp
    (.quantified .always (.quantified .always body))
    (.quantified .always (.quantified .always (swapHeadPair body)))

def star_11_1_reading (body : Raw Γ) (z w : Elementary Γ) : Reading Γ where
  printed := "⊢ : (x, y).φ(x, y) .⊃ .φ(z, w)"
  parsed := smartImp
    (.quantified .always (.quantified .always body))
    (instantiateHeadRaw z (instantiateHeadRaw w body))

def star_11_11_reading (body : Raw Γ) : Reading Γ where
  printed := "If φ(z, w) is true whatever possible arguments z and w may be,\nthen (x, y).φ(x, y) is true."
  parsed := .quantified .always (.quantified .always body)

theorem star_11_07 (body : Raw Γ) :
    Assertion (smartImp
      (.quantified .always (.quantified .always body))
      (.quantified .always (.quantified .always (swapHeadPair body)))) :=
  Star11Derivation.star_11_07 body

theorem star_11_1 (body : Raw Γ) (z w : Elementary Γ) :
    Assertion (smartImp
      (.quantified .always (.quantified .always body))
      (instantiateHeadRaw z (instantiateHeadRaw w body))) :=
  Star11Derivation.star_11_1 body z w

theorem star_11_11 (body : Raw Γ)
    (line1 : ∀ z w : Elementary Γ,
      Assertion (instantiateHeadRaw z (instantiateHeadRaw w body))) :
    Assertion (.quantified .always (.quantified .always body)) :=
  Star11Derivation.star_11_11 body line1

end PM.Star11
