import Principia.Deduction.Star100Derived

namespace PM.RamifiedSyntax

/-!
# Definition of PM II, ✱102

The two endpoint types remain independent in the parameters `elementSort` and
`parameterSort`.  Thus the assigned-type `Nc(αᵦ)` is not collapsed to the
homogeneous instance of ✱100.
-/

/-- ✱102·01, `NCᵝ(α) = DʻNc(αᵦ)`: the heterogeneous domain of the typed
class-valued relation. -/
def star_102_01
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (typedSimilarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    Formula signature real apparent
      (bindOrder
        (classValuedApplicationOrder elementSort resultOrder identityBaseOrder
          identityExcess)
        parameterSort) :=
  .sometimes vocabulary.domainExistential
    (star_100_01 vocabulary typedSimilarity.weaken value.weaken
      (.apparent .zero))

/-- Full eliminable expansion of ✱102·01. -/
theorem star_102_01_unfold
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (typedSimilarity : Term signature real apparent
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real apparent
      (classValueSort elementSort resultOrder)) :
    star_102_01 vocabulary typedSimilarity value =
      .sometimes vocabulary.domainExistential
        (star_100_01 vocabulary typedSimilarity.weaken value.weaken
          (.apparent .zero)) := rfl

/-- Contextual printed-to-AST reading of ✱102·01. -/
def star_102_01_reading
    (vocabulary : ClassValuedDefinitionVocabulary signature elementSort
      parameterSort resultOrder identityBaseOrder identityExcess)
    (typedSimilarity : Term signature real []
      (.function [elementSort, parameterSort] resultOrder similarityExcess))
    (value : Term signature real []
      (classValueSort elementSort resultOrder)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱102·01.  NCᵝ(α) = DʻNc(αᵦ)  Df"
  parsed := .assertion (star_102_01 vocabulary typedSimilarity value)
  scopeReading := "The α- and β-assigned class sorts stay distinct; D binds the β-side argument of the typed Nc relation."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_102_01
#print axioms PM.RamifiedSyntax.star_102_01_unfold
#print axioms PM.RamifiedSyntax.star_102_01_reading
