import Principia.Deduction.Star9
import Principia.Syntax.Printed

namespace PM.Star10

open PM.Experimental.CanonicalOrderedFormula

/-- The three syntactic kinds of claim to which the four primitive
propositions printed in ✱10 belong.  This is syntax, not a certificate: the
only inhabitants of `Star10Derivation` are the four printed Pp. below. -/
inductive Claim where
  | assertion : {Γ : RealContext} → Raw Γ → Claim
  | significance : {Γ : RealContext} → {Δ : BoundContext} →
      Apparent Γ (.elementaryProposition :: Δ) → Claim
  | functionExistence : RealContext → BoundContext → Claim

/-- The deduction judgement introduced by ✱10.

Its constructors are exactly the four primitive propositions printed in
✱10.  In particular, the definitions ✱10·01–·03 and every proposition proved
later in the number are absent from this list. -/
inductive Star10Derivation : Claim → Prop where
  /-- ✱10·1: `⊢ : (x).φx .⊃ .φy`. -/
  | star_10_1 (body : Raw Γ) (value : Elementary Γ) :
      Star10Derivation (.assertion
        (smartImp (.quantified .always body)
          (instantiateHeadRaw value body)))
  /-- ✱10·11: truth for an arbitrary real value licenses universal assertion. -/
  | star_10_11 (body : Raw Γ) :
      Star10Derivation (.assertion (openHeadRaw body)) →
      Star10Derivation (.assertion (.quantified .always body))
  /-- ✱10·121: significance is preserved when an apparent argument is
  replaced by a real argument of the same type (and conversely). -/
  | star_10_121 (body : Apparent Γ (.elementaryProposition :: Δ)) :
      Star10Derivation (.significance body)
  /-- ✱10·122: a propositional value supplies a propositional function, and
  conversely. -/
  | star_10_122 (Γ : RealContext) (Δ : BoundContext) :
      Star10Derivation (.functionExistence Γ Δ)

/-- A catalogue reading for the heterogeneous primitive claims of ✱10. -/
structure Reading where
  printed : PM.PrintedFormula
  parsed : Claim

def star_10_1_reading (body : Raw Γ) (value : Elementary Γ) : Reading where
  printed := PM.pmPrinted "⊢ : (x).φx .⊃ .φy"
  parsed := .assertion
    (smartImp (.quantified .always body) (instantiateHeadRaw value body))

def star_10_11_reading (body : Raw Γ) : Reading where
  printed := PM.pmPrinted
    "If φy is true whatever possible argument y may be, then (x).φx is true."
  parsed := .assertion (.quantified .always body)

def star_10_121_reading
    (body : Apparent Γ (.elementaryProposition :: Δ)) : Reading where
  printed := PM.pmPrinted
    "If “φx” is significant, then if a is of the same type as x, “φa” is significant, and vice versa.  [✱9·14]"
  parsed := .significance body

def star_10_122_reading (Γ : RealContext) (Δ : BoundContext) : Reading where
  printed := PM.pmPrinted
    "If, for some a, there is a proposition φa, then there is a function φx̂, and vice versa.  [✱9·15]"
  parsed := .functionExistence Γ Δ

/-- The primitive instance printed as ✱10·1. -/
theorem star_10_1 (body : Raw Γ) (value : Elementary Γ) :
    Star10Derivation (star_10_1_reading body value).parsed :=
  Star10Derivation.star_10_1 body value

/-- The primitive generalization rule printed as ✱10·11. -/
theorem star_10_11 (body : Raw Γ)
    (line1 : Star10Derivation (.assertion (openHeadRaw body))) :
    Star10Derivation (star_10_11_reading body).parsed :=
  Star10Derivation.star_10_11 body line1

/-- The primitive same-type significance principle printed as ✱10·121. -/
theorem star_10_121
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    Star10Derivation (star_10_121_reading body).parsed :=
  Star10Derivation.star_10_121 body

/-- The primitive function-existence principle printed as ✱10·122. -/
theorem star_10_122 (Γ : RealContext) (Δ : BoundContext) :
    Star10Derivation (star_10_122_reading Γ Δ).parsed :=
  Star10Derivation.star_10_122 Γ Δ

end PM.Star10
