import Principia.FirstEdition.Volume1.Star93Source
import Principia.Syntax.Ramified
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived definitions of PM I, ✱93

These are eliminable application expansions of the incomplete relation and
class signs printed at the opening of ✱93.  Their operands are ramified
formulae, never Lean predicates or sets.
-/

/-- ✱93·01: `xBP` unfolds to `x∈DʻP−ᗡʻP`. -/
def star_93_01
    (domainNegation : signature.Negation domainOrder)
    (converseDomainNegation : signature.Negation converseDomainOrder)
    (outerNegation : signature.Negation
      (max domainOrder converseDomainOrder))
    (differenceDisjunction : signature.Disjunction
      (max domainOrder converseDomainOrder))
    (domainMembership : Formula signature real apparent domainOrder)
    (converseDomainMembership : Formula signature real apparent
      converseDomainOrder) :
    Formula signature real apparent (max domainOrder converseDomainOrder) :=
  mixedConjunction domainNegation converseDomainNegation outerNegation
    differenceDisjunction domainMembership
    (.neg converseDomainNegation converseDomainMembership)

theorem star_93_01_unfold
    (domainNegation : signature.Negation domainOrder)
    (converseDomainNegation : signature.Negation converseDomainOrder)
    (outerNegation : signature.Negation
      (max domainOrder converseDomainOrder))
    (differenceDisjunction : signature.Disjunction
      (max domainOrder converseDomainOrder))
    (domainMembership : Formula signature real apparent domainOrder)
    (converseDomainMembership : Formula signature real apparent
      converseDomainOrder) :
    star_93_01 domainNegation converseDomainNegation outerNegation
        differenceDisjunction domainMembership converseDomainMembership =
      .neg outerNegation
        (.disj differenceDisjunction
          (.neg domainNegation domainMembership)
          (.neg converseDomainNegation
            (.neg converseDomainNegation converseDomainMembership))) := rfl

/-- ✱93·02: `x min_P α` unfolds to
`x∈α∩CʻP−P̌ʻʻα`, preserving the printed intersection-before-difference
grouping. -/
def star_93_02
    (alphaNegation : signature.Negation alphaOrder)
    (fieldNegation : signature.Negation fieldOrder)
    (intersectionNegation : signature.Negation
      (max alphaOrder fieldOrder))
    (intersectionDisjunction : signature.Disjunction
      (max alphaOrder fieldOrder))
    (imageNegation : signature.Negation imageOrder)
    (resultNegation : signature.Negation
      (max (max alphaOrder fieldOrder) imageOrder))
    (resultDisjunction : signature.Disjunction
      (max (max alphaOrder fieldOrder) imageOrder))
    (alphaMembership : Formula signature real apparent alphaOrder)
    (fieldMembership : Formula signature real apparent fieldOrder)
    (converseImageMembership : Formula signature real apparent imageOrder) :
    Formula signature real apparent
      (max (max alphaOrder fieldOrder) imageOrder) :=
  mixedConjunction intersectionNegation imageNegation resultNegation
    resultDisjunction
    (mixedConjunction alphaNegation fieldNegation intersectionNegation
      intersectionDisjunction alphaMembership fieldMembership)
    (.neg imageNegation converseImageMembership)

theorem star_93_02_unfold
    (alphaNegation : signature.Negation alphaOrder)
    (fieldNegation : signature.Negation fieldOrder)
    (intersectionNegation : signature.Negation
      (max alphaOrder fieldOrder))
    (intersectionDisjunction : signature.Disjunction
      (max alphaOrder fieldOrder))
    (imageNegation : signature.Negation imageOrder)
    (resultNegation : signature.Negation
      (max (max alphaOrder fieldOrder) imageOrder))
    (resultDisjunction : signature.Disjunction
      (max (max alphaOrder fieldOrder) imageOrder))
    (alphaMembership : Formula signature real apparent alphaOrder)
    (fieldMembership : Formula signature real apparent fieldOrder)
    (converseImageMembership : Formula signature real apparent imageOrder) :
    star_93_02 alphaNegation fieldNegation intersectionNegation
        intersectionDisjunction imageNegation resultNegation
        resultDisjunction alphaMembership fieldMembership
        converseImageMembership =
      mixedConjunction intersectionNegation imageNegation resultNegation
        resultDisjunction
        (mixedConjunction alphaNegation fieldNegation intersectionNegation
          intersectionDisjunction alphaMembership fieldMembership)
        (.neg imageNegation converseImageMembership) := rfl

/-- ✱93·03: membership in `genʻP` is the image expansion
`(∃T). T∈ᗡʻPotidʻP . A min_P T`. -/
def star_93_03
    (existential : ExistentialVocabulary signature sourceSort
      (max sourceOrder minimumOrder))
    (sourceNegation : signature.Negation sourceOrder)
    (minimumNegation : signature.Negation minimumOrder)
    (outerNegation : signature.Negation
      (max sourceOrder minimumOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max sourceOrder minimumOrder))
    (sourceMembership : Formula signature real (sourceSort :: apparent)
      sourceOrder)
    (minimumApplication : Formula signature real (sourceSort :: apparent)
      minimumOrder) :
    Formula signature real apparent
      (bindOrder (max sourceOrder minimumOrder) sourceSort) :=
  .sometimes existential
    (mixedConjunction sourceNegation minimumNegation outerNegation
      conjunctionDisjunction sourceMembership minimumApplication)

theorem star_93_03_unfold
    (existential : ExistentialVocabulary signature sourceSort
      (max sourceOrder minimumOrder))
    (sourceNegation : signature.Negation sourceOrder)
    (minimumNegation : signature.Negation minimumOrder)
    (outerNegation : signature.Negation
      (max sourceOrder minimumOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max sourceOrder minimumOrder))
    (sourceMembership : Formula signature real (sourceSort :: apparent)
      sourceOrder)
    (minimumApplication : Formula signature real (sourceSort :: apparent)
      minimumOrder) :
    star_93_03 existential sourceNegation minimumNegation outerNegation
        conjunctionDisjunction sourceMembership minimumApplication =
      .sometimes existential
        (mixedConjunction sourceNegation minimumNegation outerNegation
          conjunctionDisjunction sourceMembership minimumApplication) := rfl

/-- Diplomatic reading of ✱93·01. -/
def star_93_01_reading
    (domainNegation : signature.Negation domainOrder)
    (converseDomainNegation : signature.Negation converseDomainOrder)
    (outerNegation : signature.Negation
      (max domainOrder converseDomainOrder))
    (differenceDisjunction : signature.Disjunction
      (max domainOrder converseDomainOrder))
    (domainMembership : Formula signature real [] domainOrder)
    (converseDomainMembership : Formula signature real []
      converseDomainOrder) : RamifiedReading signature real where
  printed := PM.pmPrinted "✱93·01. B=x̂P̂(x∈ DʻP-ᗡʻP) Df"
  parsed := .assertion
    (star_93_01 domainNegation converseDomainNegation outerNegation
      differenceDisjunction domainMembership converseDomainMembership)
  scopeReading := "Application xBP is eliminated to membership in DʻP minus membership in ᗡʻP."

/-- Diplomatic reading of ✱93·02. -/
def star_93_02_reading
    (alphaNegation : signature.Negation alphaOrder)
    (fieldNegation : signature.Negation fieldOrder)
    (intersectionNegation : signature.Negation
      (max alphaOrder fieldOrder))
    (intersectionDisjunction : signature.Disjunction
      (max alphaOrder fieldOrder))
    (imageNegation : signature.Negation imageOrder)
    (resultNegation : signature.Negation
      (max (max alphaOrder fieldOrder) imageOrder))
    (resultDisjunction : signature.Disjunction
      (max (max alphaOrder fieldOrder) imageOrder))
    (alphaMembership : Formula signature real [] alphaOrder)
    (fieldMembership : Formula signature real [] fieldOrder)
    (converseImageMembership : Formula signature real [] imageOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted
    "✱93·02. min_P=min(P)=x̂α̂(x∈ α∩ CʻP-P̌ʻʻα) Df"
  parsed := .assertion
    (star_93_02 alphaNegation fieldNegation intersectionNegation
      intersectionDisjunction imageNegation resultNegation
      resultDisjunction alphaMembership fieldMembership
      converseImageMembership)
  scopeReading := "The matrix is grouped as (x∈α intersect x∈CʻP) minus x∈P-converse-image α."

/-- Diplomatic reading of ✱93·03. -/
def star_93_03_reading
    (existential : ExistentialVocabulary signature sourceSort
      (max sourceOrder minimumOrder))
    (sourceNegation : signature.Negation sourceOrder)
    (minimumNegation : signature.Negation minimumOrder)
    (outerNegation : signature.Negation
      (max sourceOrder minimumOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max sourceOrder minimumOrder))
    (sourceMembership : Formula signature real [sourceSort] sourceOrder)
    (minimumApplication : Formula signature real [sourceSort] minimumOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱93·03. genʻP=min⃗_PʻʻᗡʻʻPotidʻP Df"
  parsed := .assertion
    (star_93_03 existential sourceNegation minimumNegation outerNegation
      conjunctionDisjunction sourceMembership minimumApplication)
  scopeReading := "The forward minimum image is eliminated by binding one source member T and applying min_P to it."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_93_01
#print axioms PM.RamifiedSyntax.star_93_01_unfold
#print axioms PM.RamifiedSyntax.star_93_02
#print axioms PM.RamifiedSyntax.star_93_02_unfold
#print axioms PM.RamifiedSyntax.star_93_03
#print axioms PM.RamifiedSyntax.star_93_03_unfold
#print axioms PM.RamifiedSyntax.star_93_01_reading
#print axioms PM.RamifiedSyntax.star_93_02_reading
#print axioms PM.RamifiedSyntax.star_93_03_reading
