import Principia.Deduction.Star105Derived
import Principia.FirstEdition.Volume2.Star106Source

namespace PM.RamifiedSyntax

/-!
# Definitions of PM II, ✱106

The five displayed `c`-operators differ only in the relative type stratum
supplied as `typeLevel`.  Their common expansion remains an eliminable
predicative class abstraction.  The `etc.` in ✱106·03 is retained by keeping
that stratum parametric.
-/

/-- ✱106·01, `N₀₀cʻα = Ncʻα ∩ tʻt₀₀ʻα`. -/
def star_106_01
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type00Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :=
  star105ClassValue vocabulary negation disjunction similarity type00Level value
    parameter

theorem star_106_01_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type00Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_106_01 vocabulary negation disjunction similarity type00Level value
        parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary type00Level.weaken (.apparent .zero) parameter.weaken))
        value := rfl

def star_106_01_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type00Level : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱106·01. N₀₀cʻα = Ncʻα ∩ tʻt₀₀ʻα Df"
  parsed := .assertion (star_106_01 vocabulary negation disjunction similarity
    type00Level value parameter)
  scopeReading := "The N₀₀c-value is identified with the predicative class whose membership matrix is the printed intersection."

/-- ✱106·011, `N¹¹cʻα = Ncʻα ∩ tʻt¹¹ʻα`. -/
def star_106_011
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type11Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :=
  star105ClassValue vocabulary negation disjunction similarity type11Level value
    parameter

theorem star_106_011_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type11Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_106_011 vocabulary negation disjunction similarity type11Level value
        parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary type11Level.weaken (.apparent .zero) parameter.weaken))
        value := rfl

def star_106_011_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type11Level : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱106·011. N¹¹cʻα = Ncʻα ∩ tʻt¹¹ʻα Df"
  parsed := .assertion (star_106_011 vocabulary negation disjunction similarity
    type11Level value parameter)
  scopeReading := "The N¹¹c-value is identified with the predicative class whose membership matrix is the printed intersection."

/-- ✱106·012, `N₀₁cʻα = Ncʻα ∩ tʻt₀₁ʻα`. -/
def star_106_012
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type01Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :=
  star105ClassValue vocabulary negation disjunction similarity type01Level value
    parameter

theorem star_106_012_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type01Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_106_012 vocabulary negation disjunction similarity type01Level value
        parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary type01Level.weaken (.apparent .zero) parameter.weaken))
        value := rfl

def star_106_012_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type01Level : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱106·012. N₀₁cʻα = Ncʻα ∩ tʻt₀₁ʻα Df etc."
  parsed := .assertion (star_106_012 vocabulary negation disjunction similarity
    type01Level value parameter)
  scopeReading := "The N₀₁c-value is identified with the predicative class whose membership matrix is the printed intersection."

/-- ✱106·02, `N¹₀cʻα = Ncʻα ∩ tʻt¹₀ʻα`. -/
def star_106_02
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type10Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :=
  star105ClassValue vocabulary negation disjunction similarity type10Level value
    parameter

theorem star_106_02_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type10Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_106_02 vocabulary negation disjunction similarity type10Level value
        parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary type10Level.weaken (.apparent .zero) parameter.weaken))
        value := rfl

def star_106_02_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type10Level : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱106·02. N¹₀cʻα = Ncʻα ∩ tʻt¹₀ʻα Df etc."
  parsed := .assertion (star_106_02 vocabulary negation disjunction similarity
    type10Level value parameter)
  scopeReading := "The N¹₀c-value is identified with the predicative class whose membership matrix is the printed intersection."

/-- ✱106·021, `¹N₀cʻα = Ncʻα ∩ tʻ¹t₀ʻα`. -/
def star_106_021
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (converseType10Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :=
  star105ClassValue vocabulary negation disjunction similarity
    converseType10Level value
    parameter

theorem star_106_021_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (converseType10Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real apparent parameterSort) :
    star_106_021 vocabulary negation disjunction similarity converseType10Level
        value parameter =
      classValuedApplication vocabulary
        (conjunction negation disjunction
          (applyBinary similarity.weaken (.apparent .zero) parameter.weaken)
          (applyBinary converseType10Level.weaken (.apparent .zero)
            parameter.weaken))
        value := rfl

def star_106_021_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (converseType10Level : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder))
    (parameter : Term signature real [] parameterSort) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱106·021. ¹N₀cʻα = Ncʻα ∩ tʻ¹t₀ʻα Df etc."
  parsed := .assertion (star_106_021 vocabulary negation disjunction similarity
    converseType10Level value parameter)
  scopeReading := "The ¹N₀c-value is identified with the predicative class whose membership matrix is the printed intersection."

/-- ✱106·03, `N₀₀C = DʻN₀₀c` (and the printed systematic variants). -/
def star_106_03
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type00Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    Formula signature real apparent
      (bindOrder
        (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
          identityExcess)
        parameterSort) :=
  .sometimes vocabulary.domainExistential
    (star_106_01 vocabulary negation disjunction similarity.weaken
      type00Level.weaken value.weaken (.apparent .zero))

theorem star_106_03_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type00Level : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    star_106_03 vocabulary negation disjunction similarity type00Level value =
      .sometimes vocabulary.domainExistential
        (star_106_01 vocabulary negation disjunction similarity.weaken
          type00Level.weaken value.weaken (.apparent .zero)) := rfl

def star_106_03_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (similarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (type00Level : Term signature real []
      (.function [elementSort, parameterSort] resultOrder typeExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱106·03. N₀₀C = DʻN₀₀c Df etc."
  parsed := .assertion (star_106_03 vocabulary negation disjunction similarity
    type00Level value)
  scopeReading := "The D-expansion binds α in the contextual N₀₀c application; the type-level parameter also covers PM's printed systematic variants."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_106_01
#print axioms PM.RamifiedSyntax.star_106_01_unfold
#print axioms PM.RamifiedSyntax.star_106_01_reading
#print axioms PM.RamifiedSyntax.star_106_011
#print axioms PM.RamifiedSyntax.star_106_011_unfold
#print axioms PM.RamifiedSyntax.star_106_011_reading
#print axioms PM.RamifiedSyntax.star_106_012
#print axioms PM.RamifiedSyntax.star_106_012_unfold
#print axioms PM.RamifiedSyntax.star_106_012_reading
#print axioms PM.RamifiedSyntax.star_106_02
#print axioms PM.RamifiedSyntax.star_106_02_unfold
#print axioms PM.RamifiedSyntax.star_106_02_reading
#print axioms PM.RamifiedSyntax.star_106_021
#print axioms PM.RamifiedSyntax.star_106_021_unfold
#print axioms PM.RamifiedSyntax.star_106_021_reading
#print axioms PM.RamifiedSyntax.star_106_03
#print axioms PM.RamifiedSyntax.star_106_03_unfold
#print axioms PM.RamifiedSyntax.star_106_03_reading
