import Principia.Syntax.DescriptionDefinitions

/-!
# PM I, Q298: exact contextual targets at ✱14·202/·204/·205/·28/·13

Descriptions remain incomplete symbols.  Every displayed occurrence below is
therefore eliminated by `Formula.descriptionScope`; none is inserted into
`Term`.  These are target constructors only.  The repository still lacks the
source-licensed description assertion calculus needed to prove them.
-/

namespace PM.Architecture.Star14Q298Targets

open PM.DescriptionSyntax
open PM.DescriptionSyntax.Formula

private def headSubstitution
    (term : Term signature realContext apparentContext sort) :
    Substitution signature realContext (sort :: apparentContext) apparentContext
  | _, .zero => term
  | _, .succ entry => .apparent entry

private def candidate :
    Term signature realContext (sort :: apparentContext) sort :=
  .apparent .zero

private def weakenTerm
    (term : Term signature realContext apparentContext sort) :
    Term signature realContext (fresh :: apparentContext) sort :=
  term.substitute weakeningSubstitution

private def formalUniqueAt
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order)
    (term : Term signature realContext apparentContext sort) :
    Formula signature realContext apparentContext order :=
  (uniqueMatrix vocabulary condition).substitute (headSubstitution term)

private def reverseUniqueMatrix
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext (sort :: apparentContext) order :=
  let conditionAtFresh := condition.substitute
    (insertAfterHeadSubstitution (inserted := sort))
  let fresh : Term signature realContext
      (sort :: sort :: apparentContext) sort := .apparent .zero
  let witness : Term signature realContext
      (sort :: sort :: apparentContext) sort := .apparent (.succ .zero)
  .always vocabulary.universal
    (iff vocabulary conditionAtFresh
      (.equal vocabulary.equality witness fresh))

private def reverseFormalUniqueAt
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order)
    (term : Term signature realContext apparentContext sort) :
    Formula signature realContext apparentContext order :=
  (reverseUniqueMatrix vocabulary condition).substitute (headSubstitution term)

/-- Contextual reading of `(℩x)(φx) = b`; the description is not a term. -/
def descriptionEquals
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order)
    (term : Term signature realContext apparentContext sort) :
    Formula signature realContext apparentContext order :=
  .descriptionScope vocabulary condition
    (.equal vocabulary.equality candidate (weakenTerm term))

/-- Contextual reading of `b = (℩x)(φx)`. -/
def equalsDescription
    (vocabulary : DescriptionVocabulary signature sort order)
    (term : Term signature realContext apparentContext sort)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .descriptionScope vocabulary condition
    (.equal vocabulary.equality (weakenTerm term) candidate)

/-- The four exact members of the equivalence chain printed at ✱14·202. -/
structure Star_14_202Target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order)
    (term : Term signature realContext apparentContext sort) where
  formalIdentity : Formula signature realContext apparentContext order :=
    formalUniqueAt vocabulary condition term
  descriptionIdentity : Formula signature realContext apparentContext order :=
    descriptionEquals vocabulary condition term
  reversedFormalIdentity : Formula signature realContext apparentContext order :=
    reverseFormalUniqueAt vocabulary condition term
  reversedDescriptionIdentity : Formula signature realContext apparentContext order :=
    equalsDescription vocabulary term condition

def star_14_202_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order)
    (term : Term signature realContext apparentContext sort) :
    Star_14_202Target vocabulary condition term := {}

private def existsDescriptionEquals
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .sometimes vocabulary.existential
    (.descriptionScope vocabulary condition.weaken
      (.equal vocabulary.equality candidate (.apparent (.succ .zero))))

/-- Exact target of ✱14·204. -/
def star_14_204_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  iff vocabulary (descriptionExists vocabulary condition)
    (existsDescriptionEquals vocabulary condition)

private def existsEqualsDescriptionAnd
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext
      (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .sometimes vocabulary.existential
    (.descriptionScope vocabulary condition.weaken
      (conj vocabulary
        (.equal vocabulary.equality (.apparent (.succ .zero)) candidate)
        matrix.weaken))

/-- Exact target of ✱14·205. -/
def star_14_205_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext
      (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  iff vocabulary (.descriptionScope vocabulary condition matrix)
    (existsEqualsDescriptionAnd vocabulary condition matrix)

/-- Exact contextual reading of `(℩x)(φx) = (℩x)(φx)`.  The single scope
binds both printed occurrences of the same incomplete symbol. -/
def descriptionSelfIdentity
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .descriptionScope vocabulary condition
    (.equal vocabulary.equality candidate candidate)

/-- Exact target of ✱14·28. -/
def star_14_28_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  iff vocabulary (descriptionExists vocabulary condition)
    (descriptionSelfIdentity vocabulary condition)

/-- Exact target of ✱14·13, with both orientations independently reduced by
the contextual-description constructor. -/
def star_14_13_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order)
    (term : Term signature realContext apparentContext sort) :
    Formula signature realContext apparentContext order :=
  iff vocabulary (equalsDescription vocabulary term condition)
    (descriptionEquals vocabulary condition term)

end PM.Architecture.Star14Q298Targets
