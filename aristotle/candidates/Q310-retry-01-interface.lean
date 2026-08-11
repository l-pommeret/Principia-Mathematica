-- PM-INTERFACE-ONLY-TRANSPLANT
-- This is a candidate body bundle, not a canonical integration or CI result.
-- Archive SHA-256: e0b85df9919ddad3146ea439617eb8b032f9e027da525ee81cabe294b23b161f
-- Report SHA-256: 343e5738675d8faa21b761520f104347186877fd509f7d7d72c5c7fad4a864be

namespace PM.FirstEdition.Volume1.Star14Source

theorem star_14_02
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    descriptionExists vocabulary condition =
      .sometimes vocabulary.existential (uniqueMatrix vocabulary condition) := by
  rfl

end PM.FirstEdition.Volume1.Star14Source

namespace PM.FirstEdition.Volume1.Star14Source

theorem star_14_03
    (outerVocabulary : DescriptionVocabulary signature outerSort order)
    (innerVocabulary : DescriptionVocabulary signature innerSort order)
    (outerCondition : Formula signature realContext (outerSort :: apparentContext) order)
    (innerCondition : Formula signature realContext (innerSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (innerSort :: outerSort :: apparentContext) order) :
    descriptionScopePair outerVocabulary innerVocabulary outerCondition
        innerCondition continuation =
      .descriptionScope outerVocabulary outerCondition
        (.descriptionScope innerVocabulary
          (conditionUnderOuter innerCondition)
          continuation) := by
  rfl

end PM.FirstEdition.Volume1.Star14Source

namespace PM.FirstEdition.Volume1.Star14Source

theorem star_14_04
    (laterVocabulary : DescriptionVocabulary signature laterSort order)
    (earlierVocabulary : DescriptionVocabulary signature earlierSort order)
    (laterCondition : Formula signature realContext (laterSort :: apparentContext) order)
    (earlierCondition : Formula signature realContext (earlierSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (earlierSort :: laterSort :: apparentContext) order) :
    laterDescriptionOuterScope laterVocabulary earlierVocabulary laterCondition
        earlierCondition continuation =
      descriptionScopePair laterVocabulary earlierVocabulary laterCondition
        earlierCondition continuation := by
  rfl


end PM.FirstEdition.Volume1.Star14Source
