import Principia.FirstEdition.Volume1.Star97Source
import Principia.Syntax.Ramified
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-! # Derived definitions of PM I, ✱97 -/

/-- ✱97·01: membership in the symmetric neighbourhood `R⃡ʻx` unfolds,
in printed order, to the forward image, the singleton/field intersection,
and the backward image. -/
def star_97_01
    (identityNegation : signature.Negation identityOrder)
    (fieldNegation : signature.Negation fieldOrder)
    (middleNegation : signature.Negation
      (max identityOrder fieldOrder))
    (middleDisjunction : signature.Disjunction
      (max identityOrder fieldOrder))
    (firstUnionDisjunction : signature.Disjunction
      (max forwardOrder (max identityOrder fieldOrder)))
    (secondUnionDisjunction : signature.Disjunction
      (max (max forwardOrder (max identityOrder fieldOrder)) backwardOrder))
    (forwardMembership : Formula signature real apparent forwardOrder)
    (singletonMembership : Formula signature real apparent identityOrder)
    (fieldMembership : Formula signature real apparent fieldOrder)
    (backwardMembership : Formula signature real apparent backwardOrder) :
    Formula signature real apparent
      (max (max forwardOrder (max identityOrder fieldOrder)) backwardOrder) :=
  .disj secondUnionDisjunction
    (.disj firstUnionDisjunction forwardMembership
      (mixedConjunction identityNegation fieldNegation middleNegation
        middleDisjunction singletonMembership fieldMembership))
    backwardMembership

theorem star_97_01_unfold
    (identityNegation : signature.Negation identityOrder)
    (fieldNegation : signature.Negation fieldOrder)
    (middleNegation : signature.Negation
      (max identityOrder fieldOrder))
    (middleDisjunction : signature.Disjunction
      (max identityOrder fieldOrder))
    (firstUnionDisjunction : signature.Disjunction
      (max forwardOrder (max identityOrder fieldOrder)))
    (secondUnionDisjunction : signature.Disjunction
      (max (max forwardOrder (max identityOrder fieldOrder)) backwardOrder))
    (forwardMembership : Formula signature real apparent forwardOrder)
    (singletonMembership : Formula signature real apparent identityOrder)
    (fieldMembership : Formula signature real apparent fieldOrder)
    (backwardMembership : Formula signature real apparent backwardOrder) :
    star_97_01 identityNegation fieldNegation middleNegation
        middleDisjunction firstUnionDisjunction secondUnionDisjunction
        forwardMembership singletonMembership fieldMembership
        backwardMembership =
      .disj secondUnionDisjunction
        (.disj firstUnionDisjunction forwardMembership
          (mixedConjunction identityNegation fieldNegation middleNegation
            middleDisjunction singletonMembership fieldMembership))
        backwardMembership := rfl

/-- Diplomatic reading of ✱97·01. -/
def star_97_01_reading
    (identityNegation : signature.Negation identityOrder)
    (fieldNegation : signature.Negation fieldOrder)
    (middleNegation : signature.Negation
      (max identityOrder fieldOrder))
    (middleDisjunction : signature.Disjunction
      (max identityOrder fieldOrder))
    (firstUnionDisjunction : signature.Disjunction
      (max forwardOrder (max identityOrder fieldOrder)))
    (secondUnionDisjunction : signature.Disjunction
      (max (max forwardOrder (max identityOrder fieldOrder)) backwardOrder))
    (forwardMembership : Formula signature real [] forwardOrder)
    (singletonMembership : Formula signature real [] identityOrder)
    (fieldMembership : Formula signature real [] fieldOrder)
    (backwardMembership : Formula signature real [] backwardOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted
    "✱97·01. R⃡ʻx=R⃗ʻx∪(ιʻx∩ CʻR)∪R⃖ʻx Df"
  parsed := .assertion
    (star_97_01 identityNegation fieldNegation middleNegation
      middleDisjunction firstUnionDisjunction secondUnionDisjunction
      forwardMembership singletonMembership fieldMembership
      backwardMembership)
  scopeReading := "Membership y∈R-double-arrowʻx is the printed left-associated union of yRx, the singleton/field guard, and xRy."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_97_01
#print axioms PM.RamifiedSyntax.star_97_01_unfold
#print axioms PM.RamifiedSyntax.star_97_01_reading
