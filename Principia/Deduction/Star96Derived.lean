import Principia.FirstEdition.Volume1.Star96Source
import Principia.Syntax.Ramified
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-! # Derived definitions of PM I, ✱96 -/

/-- ✱96·01: membership in `I_Rʻx` unfolds to the intersection
`xR_*z . zRₚₒz`. -/
def star_96_01
    (posterityNegation : signature.Negation posterityOrder)
    (cycleNegation : signature.Negation cycleOrder)
    (outerNegation : signature.Negation
      (max posterityOrder cycleOrder))
    (intersectionDisjunction : signature.Disjunction
      (max posterityOrder cycleOrder))
    (posterityMembership : Formula signature real apparent posterityOrder)
    (cycleMembership : Formula signature real apparent cycleOrder) :
    Formula signature real apparent (max posterityOrder cycleOrder) :=
  mixedConjunction posterityNegation cycleNegation outerNegation
    intersectionDisjunction posterityMembership cycleMembership

theorem star_96_01_unfold
    (posterityNegation : signature.Negation posterityOrder)
    (cycleNegation : signature.Negation cycleOrder)
    (outerNegation : signature.Negation
      (max posterityOrder cycleOrder))
    (intersectionDisjunction : signature.Disjunction
      (max posterityOrder cycleOrder))
    (posterityMembership : Formula signature real apparent posterityOrder)
    (cycleMembership : Formula signature real apparent cycleOrder) :
    star_96_01 posterityNegation cycleNegation outerNegation
        intersectionDisjunction posterityMembership cycleMembership =
      .neg outerNegation
        (.disj intersectionDisjunction
          (.neg posterityNegation posterityMembership)
          (.neg cycleNegation cycleMembership)) := rfl

/-- ✱96·02: membership in `J_Rʻx` unfolds to
`xR_*z . ∼(z∈I_Rʻx)`. -/
def star_96_02
    (posterityNegation : signature.Negation posterityOrder)
    (cyclicPartNegation : signature.Negation cyclicPartOrder)
    (outerNegation : signature.Negation
      (max posterityOrder cyclicPartOrder))
    (differenceDisjunction : signature.Disjunction
      (max posterityOrder cyclicPartOrder))
    (posterityMembership : Formula signature real apparent posterityOrder)
    (cyclicPartMembership : Formula signature real apparent cyclicPartOrder) :
    Formula signature real apparent
      (max posterityOrder cyclicPartOrder) :=
  mixedConjunction posterityNegation cyclicPartNegation outerNegation
    differenceDisjunction posterityMembership
    (.neg cyclicPartNegation cyclicPartMembership)

theorem star_96_02_unfold
    (posterityNegation : signature.Negation posterityOrder)
    (cyclicPartNegation : signature.Negation cyclicPartOrder)
    (outerNegation : signature.Negation
      (max posterityOrder cyclicPartOrder))
    (differenceDisjunction : signature.Disjunction
      (max posterityOrder cyclicPartOrder))
    (posterityMembership : Formula signature real apparent posterityOrder)
    (cyclicPartMembership : Formula signature real apparent cyclicPartOrder) :
    star_96_02 posterityNegation cyclicPartNegation outerNegation
        differenceDisjunction posterityMembership cyclicPartMembership =
      .neg outerNegation
        (.disj differenceDisjunction
          (.neg posterityNegation posterityMembership)
          (.neg cyclicPartNegation
            (.neg cyclicPartNegation cyclicPartMembership))) := rfl

/-- Diplomatic reading of ✱96·01. -/
def star_96_01_reading
    (posterityNegation : signature.Negation posterityOrder)
    (cycleNegation : signature.Negation cycleOrder)
    (outerNegation : signature.Negation
      (max posterityOrder cycleOrder))
    (intersectionDisjunction : signature.Disjunction
      (max posterityOrder cycleOrder))
    (posterityMembership : Formula signature real [] posterityOrder)
    (cycleMembership : Formula signature real [] cycleOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted
    "✱96·01. I_Rʻx=R⃖_∗ʻx∩ ẑ(zRₚₒz) Dft [✱96]"
  parsed := .assertion
    (star_96_01 posterityNegation cycleNegation outerNegation
      intersectionDisjunction posterityMembership cycleMembership)
  scopeReading := "Membership z∈I_Rʻx unfolds to z∈R_*←ʻx conjoined with zR_po z."

/-- Diplomatic reading of ✱96·02. -/
def star_96_02_reading
    (posterityNegation : signature.Negation posterityOrder)
    (cyclicPartNegation : signature.Negation cyclicPartOrder)
    (outerNegation : signature.Negation
      (max posterityOrder cyclicPartOrder))
    (differenceDisjunction : signature.Disjunction
      (max posterityOrder cyclicPartOrder))
    (posterityMembership : Formula signature real [] posterityOrder)
    (cyclicPartMembership : Formula signature real [] cyclicPartOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱96·02. J_Rʻx=R⃖_∗ʻx-I_Rʻx Dft [✱96]"
  parsed := .assertion
    (star_96_02 posterityNegation cyclicPartNegation outerNegation
      differenceDisjunction posterityMembership cyclicPartMembership)
  scopeReading := "Membership z∈J_Rʻx unfolds to z∈R_*←ʻx and non-membership in I_Rʻx."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_96_01
#print axioms PM.RamifiedSyntax.star_96_01_unfold
#print axioms PM.RamifiedSyntax.star_96_02
#print axioms PM.RamifiedSyntax.star_96_02_unfold
#print axioms PM.RamifiedSyntax.star_96_01_reading
#print axioms PM.RamifiedSyntax.star_96_02_reading
