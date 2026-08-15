import Principia.Deduction.Star52Derived
import Principia.FirstEdition.Volume1.Star54Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Definitions and derived propositions of PM I, ✱54

The opening definitions are systematic-ambiguity instances of the contextual
class abstraction used at ✱52·01. Their elements are themselves classes, so
neither `0` nor `2` is manufactured as a standalone class-valued term.

The 34-item catalogue is present, but no ✱54 theorem can yet be replayed
honestly in `Derivation`. The deduction judgement currently has no derived
definition-elimination theorem connecting these scopes to the identity
formula of ✱13·01. The earliest cited derived dependencies (notably ✱51·41
and ✱51·43) are likewise not exposed as ramified derivations.

Consequently this module records no theorem declaration beyond the required
definitional unfold equations. Replacing a printed proposition by a
host-logic statement, or assuming its desired assertion as a Lean premise,
would violate the certification contract.
-/

/-- Vocabulary for a contextual class whose elements have the class sort
`classSort objectClassOrder 0`. -/
structure Star54DefinitionVocabulary (signature : Signature)
    (objectClassOrder resultOrder scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (.function [classSort objectClassOrder 0] resultOrder 0)
    (max (bindOrder resultOrder (classSort objectClassOrder 0)) scopeOrder)
  universal : signature.Universal (classSort objectClassOrder 0) resultOrder
  equivalenceNegation : signature.Negation resultOrder
  equivalenceDisjunction : signature.Disjunction resultOrder
  leftNegation : signature.Negation
    (bindOrder resultOrder (classSort objectClassOrder 0))
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder resultOrder (classSort objectClassOrder 0)) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder resultOrder (classSort objectClassOrder 0)) scopeOrder)

/-- ✱54·01, `0 = ιʻΛ`, after eliminating the unit-class notation: the
definiens is the contextual class abstraction of the exact `α = Λ` matrix. -/
def star_54_01
    (vocabulary : Star54DefinitionVocabulary signature objectClassOrder
      resultOrder scopeOrder)
    (unitNullMatrix : Formula signature real
      (classSort objectClassOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort objectClassOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :=
  star_52_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction unitNullMatrix continuation

theorem star_54_01_unfold
    (vocabulary : Star54DefinitionVocabulary signature objectClassOrder
      resultOrder scopeOrder)
    (unitNullMatrix : Formula signature real
      (classSort objectClassOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort objectClassOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    star_54_01 vocabulary unitNullMatrix continuation =
      star_52_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        unitNullMatrix continuation := rfl

/-- ✱54·02, the contextual class abstraction of the exact printed matrix
`(∃x,y). x ≠ y . α = ιʻx ∪ ιʻy`. -/
def star_54_02
    (vocabulary : Star54DefinitionVocabulary signature objectClassOrder
      resultOrder scopeOrder)
    (coupleMatrix : Formula signature real
      (classSort objectClassOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort objectClassOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :=
  star_52_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction coupleMatrix continuation

theorem star_54_02_unfold
    (vocabulary : Star54DefinitionVocabulary signature objectClassOrder
      resultOrder scopeOrder)
    (coupleMatrix : Formula signature real
      (classSort objectClassOrder 0 :: apparent) resultOrder)
    (continuation : Formula signature real
      (.function [classSort objectClassOrder 0] resultOrder 0 :: apparent)
      scopeOrder) :
    star_54_02 vocabulary coupleMatrix continuation =
      star_52_01 vocabulary.existential vocabulary.universal
        vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
        vocabulary.leftNegation vocabulary.rightNegation
        vocabulary.outerNegation vocabulary.conjunctionDisjunction
        coupleMatrix continuation := rfl

/-- Audited definitional reading of the PM-VERBATIM block ✱54·01. -/
def star_54_01_reading
    (vocabulary : Star54DefinitionVocabulary signature objectClassOrder
      resultOrder scopeOrder)
    (unitNullMatrix : Formula signature real
      [classSort objectClassOrder 0] resultOrder)
    (continuation : Formula signature real
      [.function [classSort objectClassOrder 0] resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱54·01.  0 = ιʻΛ  Df"
  parsed := .assertion (star_54_01 vocabulary unitNullMatrix continuation)
  scopeReading :=
    "The unit class of Λ is eliminated as a contextual class-of-classes abstraction."

/-- Audited definitional reading of the PM-VERBATIM block ✱54·02. -/
def star_54_02_reading
    (vocabulary : Star54DefinitionVocabulary signature objectClassOrder
      resultOrder scopeOrder)
    (coupleMatrix : Formula signature real
      [classSort objectClassOrder 0] resultOrder)
    (continuation : Formula signature real
      [.function [classSort objectClassOrder 0] resultOrder 0] scopeOrder) :
    RamifiedReading signature real where
  printed := PM.pmPrinted
    "✱54·02.  2 = α̂{(∃x,y). x ≠ y . α = ιʻx ∪ ιʻy}  Df"
  parsed := .assertion (star_54_02 vocabulary coupleMatrix continuation)
  scopeReading :=
    "The class abstraction defining 2 has the scope supplied by the continuation."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_54_01
#print axioms PM.RamifiedSyntax.star_54_01_unfold
#print axioms PM.RamifiedSyntax.star_54_01_reading
#print axioms PM.RamifiedSyntax.star_54_02
#print axioms PM.RamifiedSyntax.star_54_02_unfold
#print axioms PM.RamifiedSyntax.star_54_02_reading
