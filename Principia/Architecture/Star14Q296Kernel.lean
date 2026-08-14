import Principia.Syntax.Description

namespace PM.DescriptionSyntax.Formula

/-- PM I ✱14·01. The description remains a scoped formula constructor and
reduces definitionally to PM's existential definiens. -/
def star_14_01
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition continuation :
      Formula signature realContext (sort :: apparentContext) order) :
    CoreFormula signature realContext apparentContext order :=
  .sometimes vocabulary.existential
    (CoreFormula.conj vocabulary
      (CoreFormula.uniquely vocabulary condition.expand)
      continuation.expand)

end PM.DescriptionSyntax.Formula
