import Principia.Deduction.Star100Derived
import Principia.FirstEdition.Volume2.Star105Source

namespace PM.RamifiedSyntax

/-!
# Definitions of PM II, ✱105

Each value `Nᵢcʻα` is the predicative class whose membership matrix is the
conjunction printed by PM.  The global class `NᵢC` is its `D`-class, so its
membership expansion existentially binds `α`.
-/

/-- Pointwise expansion shared by the two intersections of ✱105. -/
def star105ClassValue
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (typeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    Formula signature real apparent
      (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
        identityExcess) :=
  classValuedApplication vocabulary
    (conjunction negation disjunction
      (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
      (applyBinary typeLevel.weaken (.apparent .zero) parameter.weaken))
    value

theorem star105ClassValue_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (typeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star105ClassValue vocabulary negation disjunction similarity typeLevel
        value parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary typeLevel.weaken (.apparent .zero) parameter.weaken))
        value := rfl

/-- ✱105·01, `N₁cʻα=Ncʻα∩tʻt₁ʻα`. -/
def star_105_01
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (firstTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :=
  star105ClassValue vocabulary negation disjunction similarity firstTypeLevel
    value parameter

theorem star_105_01_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (firstTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_105_01 vocabulary negation disjunction similarity firstTypeLevel
        value parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary firstTypeLevel.weaken (.apparent .zero)
            parameter.weaken))
        value := rfl

def star_105_01_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (firstTypeLevel : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱105·01. N₁cʻα=Ncʻα∩tʻt₁ʻα Df"
  parsed := .assertion (star_105_01 vocabulary negation disjunction similarity
    firstTypeLevel value parameter)
  scopeReading := "The incomplete intersection has the scope of identity between the candidate N₁c-value and its predicative class abstraction."

/-- ✱105·011, `N₂cʻα=Ncʻα∩tʻt₂ʻα`. -/
def star_105_011
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (secondTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :=
  star105ClassValue vocabulary negation disjunction similarity secondTypeLevel
    value parameter

theorem star_105_011_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (secondTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_105_011 vocabulary negation disjunction similarity secondTypeLevel
        value parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary secondTypeLevel.weaken (.apparent .zero)
            parameter.weaken))
        value := rfl

def star_105_011_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (secondTypeLevel : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱105·011. N₂cʻα=Ncʻα∩tʻt₂ʻα Df"
  parsed := .assertion (star_105_011 vocabulary negation disjunction similarity
    secondTypeLevel value parameter)
  scopeReading := "The incomplete intersection has the scope of identity between the candidate N₂c-value and its predicative class abstraction."

/-- ✱105·02, `N₁C=DʻN₁c`. -/
def star_105_02
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (firstTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    Formula signature real apparent
      (bindOrder
        (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
          identityExcess)
        parameterSort) :=
  .sometimes vocabulary.domainExistential
    (star_105_01 vocabulary negation disjunction similarity.weaken
      firstTypeLevel.weaken value.weaken (.apparent .zero))

theorem star_105_02_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (firstTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    star_105_02 vocabulary negation disjunction similarity firstTypeLevel
        value =
      .sometimes vocabulary.domainExistential
        (star_105_01 vocabulary negation disjunction similarity.weaken
          firstTypeLevel.weaken value.weaken (.apparent .zero)) := rfl

def star_105_02_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (firstTypeLevel : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱105·02. N₁C=DʻN₁c Df"
  parsed := .assertion (star_105_02 vocabulary negation disjunction similarity
    firstTypeLevel value)
  scopeReading := "DʻN₁c is read by existentially binding α in the contextual N₁c application."

/-- ✱105·021, `N₂C=DʻN₂c`. -/
def star_105_021
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (secondTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    Formula signature real apparent
      (bindOrder
        (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
          identityExcess)
        parameterSort) :=
  .sometimes vocabulary.domainExistential
    (star_105_011 vocabulary negation disjunction similarity.weaken
      secondTypeLevel.weaken value.weaken (.apparent .zero))

theorem star_105_021_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (secondTypeLevel : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    star_105_021 vocabulary negation disjunction similarity secondTypeLevel
        value =
      .sometimes vocabulary.domainExistential
        (star_105_011 vocabulary negation disjunction similarity.weaken
          secondTypeLevel.weaken value.weaken (.apparent .zero)) := rfl

def star_105_021_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (secondTypeLevel : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱105·021. N₂C=DʻN₂c Df"
  parsed := .assertion (star_105_021 vocabulary negation disjunction similarity
    secondTypeLevel value)
  scopeReading := "DʻN₂c is read by existentially binding α in the contextual N₂c application."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star105ClassValue
#print axioms PM.RamifiedSyntax.star105ClassValue_unfold
#print axioms PM.RamifiedSyntax.star_105_01
#print axioms PM.RamifiedSyntax.star_105_01_unfold
#print axioms PM.RamifiedSyntax.star_105_01_reading
#print axioms PM.RamifiedSyntax.star_105_011
#print axioms PM.RamifiedSyntax.star_105_011_unfold
#print axioms PM.RamifiedSyntax.star_105_011_reading
#print axioms PM.RamifiedSyntax.star_105_02
#print axioms PM.RamifiedSyntax.star_105_02_unfold
#print axioms PM.RamifiedSyntax.star_105_02_reading
#print axioms PM.RamifiedSyntax.star_105_021
#print axioms PM.RamifiedSyntax.star_105_021_unfold
#print axioms PM.RamifiedSyntax.star_105_021_reading
