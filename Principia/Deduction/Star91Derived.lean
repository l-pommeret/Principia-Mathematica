import Principia.FirstEdition.Volume1.Star91Source
import Principia.Syntax.Ramified
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived definitions of PM I, ✱91

The class-valued signs `Pot` and `Potid`, and the relation-valued sign `Rₚₒ`,
are incomplete symbols.  As for the domain operators at ✱33, the definitions
below give their eliminable membership or application expansions; they do
not manufacture classes or relations as standalone terms.
-/

/-- ✱91·03: membership `P ∈ PotʻR` unfolds to the already-eliminated
application formula `P Rₜₛ R`.  The ancestral is not reified as a term. -/
def star_91_03
    (rightAncestralApplication : Formula signature real apparent
      ancestralOrder) : Formula signature real apparent ancestralOrder :=
  rightAncestralApplication

theorem star_91_03_unfold
    (rightAncestralApplication : Formula signature real apparent
      ancestralOrder) :
    star_91_03 rightAncestralApplication =
      rightAncestralApplication := rfl

/-- ✱91·04: membership `P ∈ PotidʻR` unfolds to
`P Rₜₛ (I↾CʻR)`. -/
def star_91_04
    (rightAncestralApplication : Formula signature real apparent
      ancestralOrder) : Formula signature real apparent ancestralOrder :=
  rightAncestralApplication

theorem star_91_04_unfold
    (rightAncestralApplication : Formula signature real apparent
      ancestralOrder) :
    star_91_04 rightAncestralApplication =
      rightAncestralApplication := rfl

/-- ✱91·05: application `x Rₚₒ y` is the union of all members of `PotʻR`,
namely `(∃P). P∈PotʻR . xPy`. -/
def star_91_05
    (existential : ExistentialVocabulary signature
      (relationSort relationOrder relationExcess)
      (max membershipOrder relationOrder))
    (membershipNegation : signature.Negation membershipOrder)
    (relationNegation : signature.Negation relationOrder)
    (outerNegation : signature.Negation
      (max membershipOrder relationOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max membershipOrder relationOrder))
    (potMembership : Formula signature real
      (relationSort relationOrder relationExcess :: apparent)
      membershipOrder)
    (relationApplication : Formula signature real
      (relationSort relationOrder relationExcess :: apparent)
      relationOrder) :
    Formula signature real apparent
      (bindOrder (max membershipOrder relationOrder)
        (relationSort relationOrder relationExcess)) :=
  .sometimes existential
    (mixedConjunction membershipNegation relationNegation outerNegation
      conjunctionDisjunction
      potMembership relationApplication)

theorem star_91_05_unfold
    (existential : ExistentialVocabulary signature
      (relationSort relationOrder relationExcess)
      (max membershipOrder relationOrder))
    (membershipNegation : signature.Negation membershipOrder)
    (relationNegation : signature.Negation relationOrder)
    (outerNegation : signature.Negation
      (max membershipOrder relationOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max membershipOrder relationOrder))
    (potMembership : Formula signature real
      (relationSort relationOrder relationExcess :: apparent)
      membershipOrder)
    (relationApplication : Formula signature real
      (relationSort relationOrder relationExcess :: apparent)
      relationOrder) :
    star_91_05 existential membershipNegation relationNegation
        outerNegation conjunctionDisjunction potMembership
        relationApplication =
      .sometimes existential
        (mixedConjunction membershipNegation relationNegation outerNegation
          conjunctionDisjunction
          potMembership relationApplication) := rfl

/-- Diplomatic reading of ✱91·03. -/
def star_91_03_reading
    (rightAncestralApplication : Formula signature real []
      ancestralOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱91·03. PotʻR=R⃗ₜₛʻR Df"
  parsed := .assertion (star_91_03 rightAncestralApplication)
  scopeReading := "The class application P∈PotʻR unfolds to the forward R_ts-image condition P R_ts R."

/-- Diplomatic reading of ✱91·04. -/
def star_91_04_reading
    (rightAncestralApplication : Formula signature real []
      ancestralOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱91·04. PotidʻR=R⃗ₜₛʻ(I↾ CʻR) Df"
  parsed := .assertion (star_91_04 rightAncestralApplication)
  scopeReading := "The class application P∈PotidʻR unfolds to P R_ts (I↾CʻR)."

/-- Diplomatic reading of ✱91·05. -/
def star_91_05_reading
    (existential : ExistentialVocabulary signature
      (relationSort relationOrder relationExcess)
      (max membershipOrder relationOrder))
    (membershipNegation : signature.Negation membershipOrder)
    (relationNegation : signature.Negation relationOrder)
    (outerNegation : signature.Negation
      (max membershipOrder relationOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max membershipOrder relationOrder))
    (potMembership : Formula signature real
      [relationSort relationOrder relationExcess] membershipOrder)
    (relationApplication : Formula signature real
      [relationSort relationOrder relationExcess] relationOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱91·05. Rₚₒ=ṡʻPotʻR Df"
  parsed := .assertion
    (star_91_05 existential membershipNegation relationNegation
      outerNegation conjunctionDisjunction potMembership
      relationApplication)
  scopeReading := "The union sign s-dot is eliminated as an existential relation member of PotʻR applied to x,y."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_91_03
#print axioms PM.RamifiedSyntax.star_91_03_unfold
#print axioms PM.RamifiedSyntax.star_91_04
#print axioms PM.RamifiedSyntax.star_91_04_unfold
#print axioms PM.RamifiedSyntax.star_91_05
#print axioms PM.RamifiedSyntax.star_91_05_unfold
#print axioms PM.RamifiedSyntax.star_91_03_reading
#print axioms PM.RamifiedSyntax.star_91_04_reading
#print axioms PM.RamifiedSyntax.star_91_05_reading
