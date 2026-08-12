import Principia.Syntax.Description

namespace PM.DescriptionSyntax.Formula

/-- PM I ✱14·01. The description remains a scoped formula constructor and
reduces definitionally to PM's existential definiens. -/
theorem star_14_01
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition continuation :
      Formula signature realContext (sort :: apparentContext) order) :
    expand (.descriptionScope vocabulary condition continuation) =
      .sometimes vocabulary.existential
        (CoreFormula.conj vocabulary
          (CoreFormula.uniquely vocabulary condition.expand)
          continuation.expand) := by
  rfl

end PM.DescriptionSyntax.Formula
