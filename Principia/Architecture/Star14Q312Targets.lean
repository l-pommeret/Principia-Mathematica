import Principia.Syntax.DescriptionDefinitions

/-!
# PM I, ✱14·33–34

Exact contextual targets for the four apparent-proposition-variable forms on
p. 195.  A description remains an incomplete symbol eliminated by its scope;
`p` is an explicitly supplied formula at the same assigned order.  These are
targets only: the ramified proposition hierarchy and reducibility principle
needed by the printed assertions are not introduced here.
-/

namespace PM.Architecture.Star14Q312Targets

open PM.DescriptionSyntax
open PM.DescriptionSyntax.Formula

private def scope
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext
      (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .descriptionScope vocabulary condition matrix

/-- ✱14·33:
`E!Desc ⊃ ([Desc]. p ⊃ χDesc ≡ p ⊃ [Desc].χDesc)`. -/
def star_14_33_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext
      (sort :: apparentContext) order)
    (p : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  imp vocabulary (descriptionExists vocabulary condition)
    (iff vocabulary
      (scope vocabulary condition (imp vocabulary p.weaken matrix))
      (imp vocabulary p (scope vocabulary condition matrix)))

/-- ✱14·331:
`E!Desc ⊃ ([Desc]. χDesc ⊃ p ≡ [Desc].χDesc ⊃ p)`.  On the left the
implication lies inside the bracket; on the right it lies outside. -/
def star_14_331_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext
      (sort :: apparentContext) order)
    (p : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  imp vocabulary (descriptionExists vocabulary condition)
    (iff vocabulary
      (scope vocabulary condition (imp vocabulary matrix p.weaken))
      (imp vocabulary (scope vocabulary condition matrix) p))

/-- ✱14·332:
`E!Desc ⊃ ([Desc]. p ≡ χDesc ≡ p ≡ [Desc].χDesc)`. -/
def star_14_332_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext
      (sort :: apparentContext) order)
    (p : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  imp vocabulary (descriptionExists vocabulary condition)
    (iff vocabulary
      (scope vocabulary condition (iff vocabulary p.weaken matrix))
      (iff vocabulary p (scope vocabulary condition matrix)))

/-- ✱14·34:
`p . [Desc].χDesc ≡ [Desc]. p . χDesc`. -/
def star_14_34_target
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition matrix : Formula signature realContext
      (sort :: apparentContext) order)
    (p : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  iff vocabulary
    (conj vocabulary p (scope vocabulary condition matrix))
    (scope vocabulary condition (conj vocabulary p.weaken matrix))

end PM.Architecture.Star14Q312Targets
