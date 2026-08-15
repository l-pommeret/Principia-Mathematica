import Principia.FirstEdition.Volume2.Star100Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Definitions of PM II, ✱100

The value `Ncʻα` is a class of classes.  Since class abstractions are
incomplete symbols, it is not manufactured as a `Term`: application of `Nc`
is expanded contextually as Leibniz identity with the predicative class
`β̂(β sm α)`.  `NC` is then the domain `DʻNc`, represented by existentially
binding the argument of that expanded application.
-/

/-- The predicative class sort of a class-valued relation. -/
def classValueSort (elementSort : RSort) (resultOrder : Nat) : RSort :=
  .function [elementSort] resultOrder 0

/-- Order of Leibniz identity between values of a class-valued relation. -/
def classValueIdentityOrder (elementSort : RSort) (resultOrder
    identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder identityBaseOrder
    (.function [classValueSort elementSort resultOrder]
      identityBaseOrder identityExcess)

/-- Order of one class-valued application after its abstraction is expanded. -/
def classValuedApplicationOrder (elementSort : RSort) (resultOrder
    identityBaseOrder identityExcess : Nat) : Nat :=
  bindOrder
    (max (bindOrder resultOrder elementSort)
      (classValueIdentityOrder elementSort resultOrder identityBaseOrder
        identityExcess))
    (classValueSort elementSort resultOrder)

/-- Logical vocabulary shared by the eliminable class-valued definitions in
✱100--✱106.  It packages meanings already present in `Signature`; it adds no
rule or object-language constructor. -/
structure ClassValuedDefinitionVocabulary (signature : Signature)
    (elementSort parameterSort : RSort) (resultOrder identityBaseOrder
      identityExcess : Nat) where
  abstractionExistential : ExistentialVocabulary signature
    (classValueSort elementSort resultOrder)
    (max (bindOrder resultOrder elementSort)
      (classValueIdentityOrder elementSort resultOrder identityBaseOrder
        identityExcess))
  elementUniversal : signature.Universal elementSort resultOrder
  equivalenceNegation : signature.Negation resultOrder
  equivalenceDisjunction : signature.Disjunction resultOrder
  abstractionLeftNegation : signature.Negation
    (bindOrder resultOrder elementSort)
  abstractionRightNegation : signature.Negation
    (classValueIdentityOrder elementSort resultOrder identityBaseOrder
      identityExcess)
  abstractionOuterNegation : signature.Negation
    (max (bindOrder resultOrder elementSort)
      (classValueIdentityOrder elementSort resultOrder identityBaseOrder
        identityExcess))
  abstractionDisjunction : signature.Disjunction
    (max (bindOrder resultOrder elementSort)
      (classValueIdentityOrder elementSort resultOrder identityBaseOrder
        identityExcess))
  identity : IdentityVocabulary signature
    (classValueSort elementSort resultOrder) identityBaseOrder identityExcess
  domainExistential : ExistentialVocabulary signature parameterSort
    (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
      identityExcess)

/-- Primitive expansion of a class-valued relation application.  `matrix`
describes membership in the value class, and `value` is identified with its
predicative abstraction by ✱13·01. -/
def classValuedApplication
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (matrix : Formula signature real (elementSort :: apparent) resultOrder)
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    Formula signature real apparent
      (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
        identityExcess) :=
  .sometimes vocabulary.abstractionExistential
    (mixedConjunction vocabulary.abstractionLeftNegation
      vocabulary.abstractionRightNegation
      vocabulary.abstractionOuterNegation vocabulary.abstractionDisjunction
      (.always vocabulary.elementUniversal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      (star_13_01 vocabulary.identity value.weaken (.apparent .zero)))

theorem classValuedApplication_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (matrix : Formula signature real (elementSort :: apparent) resultOrder)
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    classValuedApplication vocabulary matrix value =
      .sometimes vocabulary.abstractionExistential
        (mixedConjunction vocabulary.abstractionLeftNegation
          vocabulary.abstractionRightNegation
          vocabulary.abstractionOuterNegation
          vocabulary.abstractionDisjunction
          (.always vocabulary.elementUniversal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (matrix.rename (liftRenaming (fun v => .succ v)))))
          (star_13_01 vocabulary.identity value.weaken
            (.apparent .zero))) := rfl

/-- ✱100·01, `Nc = sm⃗`: pointwise, a candidate value is the class of
classes similar to the argument. -/
def star_100_01
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    Formula signature real apparent
      (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
        identityExcess) :=
  classValuedApplication vocabulary
    (applyBinary similarity.weaken (.apparent .zero) parameter.weaken) value

/-- Full eliminable expansion of ✱100·01. -/
theorem star_100_01_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_100_01 vocabulary similarity value parameter =
      classValuedApplication vocabulary
        (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
        value := rfl

/-- Contextual printed-to-AST reading of ✱100·01. -/
def star_100_01_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱100·01. Nc = sm⃗ Df"
  parsed := .assertion (star_100_01 vocabulary similarity value parameter)
  scopeReading := "Nc is read pointwise: its candidate value has the scope of identity with the predicative class β̂(β sm α)."

/-- ✱100·02, `NC = DʻNc`: membership in `NC` is existential application
of the fully expanded class-valued relation of ✱100·01. -/
def star_100_02
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    Formula signature real apparent
      (bindOrder
        (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
          identityExcess)
        parameterSort) :=
  .sometimes vocabulary.domainExistential
    (star_100_01 vocabulary similarity.weaken value.weaken
      (.apparent .zero))

/-- Full eliminable expansion of ✱100·02. -/
theorem star_100_02_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    star_100_02 vocabulary similarity value =
      .sometimes vocabulary.domainExistential
        (star_100_01 vocabulary similarity.weaken value.weaken
          (.apparent .zero)) := rfl

/-- Contextual printed-to-AST reading of ✱100·02. -/
def star_100_02_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱100·02. NC = DʻNc Df"
  parsed := .assertion (star_100_02 vocabulary similarity value)
  scopeReading := "DʻNc is read by existentially binding α in the contextual application μ=Ncʻα."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.classValueSort
#print axioms PM.RamifiedSyntax.classValueIdentityOrder
#print axioms PM.RamifiedSyntax.classValuedApplicationOrder
#print axioms PM.RamifiedSyntax.ClassValuedDefinitionVocabulary
#print axioms PM.RamifiedSyntax.classValuedApplication
#print axioms PM.RamifiedSyntax.classValuedApplication_unfold
#print axioms PM.RamifiedSyntax.star_100_01
#print axioms PM.RamifiedSyntax.star_100_01_unfold
#print axioms PM.RamifiedSyntax.star_100_01_reading
#print axioms PM.RamifiedSyntax.star_100_02
#print axioms PM.RamifiedSyntax.star_100_02_unfold
#print axioms PM.RamifiedSyntax.star_100_02_reading
