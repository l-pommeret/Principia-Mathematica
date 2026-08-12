import Principia.Syntax.Description

namespace PM.Architecture.Star13Q292Targets

open PM.DescriptionSyntax

private def eq (vocabulary : DescriptionVocabulary signature sort order)
    (x y : Term signature realContext apparentContext sort) :
    CoreFormula signature realContext apparentContext order :=
  .equal vocabulary.equality x y

private def neg (vocabulary : DescriptionVocabulary signature sort order)
    (p : CoreFormula signature realContext apparentContext order) :
    CoreFormula signature realContext apparentContext order :=
  .neg vocabulary.negation p

private def imp (vocabulary : DescriptionVocabulary signature sort order)
    (p q : CoreFormula signature realContext apparentContext order) :
    CoreFormula signature realContext apparentContext order :=
  .disj vocabulary.disjunction (neg vocabulary p) q

private def conj (vocabulary : DescriptionVocabulary signature sort order)
    (p q : CoreFormula signature realContext apparentContext order) :
    CoreFormula signature realContext apparentContext order :=
  neg vocabulary (.disj vocabulary.disjunction (neg vocabulary p) (neg vocabulary q))

private def iff (vocabulary : DescriptionVocabulary signature sort order)
    (p q : CoreFormula signature realContext apparentContext order) :
    CoreFormula signature realContext apparentContext order :=
  conj vocabulary (imp vocabulary p q) (imp vocabulary q p)

/-- PM I ✱13·16: `x = y ≡ y = x`, with identity retained as the explicitly
assigned equality meaning rather than replaced by Lean equality. -/
def star_13_16_target (vocabulary : DescriptionVocabulary signature sort order)
    (x y : Term signature realContext apparentContext sort) :
    CoreFormula signature realContext apparentContext order :=
  iff vocabulary (eq vocabulary x y) (eq vocabulary y x)

/-- PM I ✱13·17: `x = y . y = z ⊃ x = z`. -/
def star_13_17_target (vocabulary : DescriptionVocabulary signature sort order)
    (x y z : Term signature realContext apparentContext sort) :
    CoreFormula signature realContext apparentContext order :=
  imp vocabulary (conj vocabulary (eq vocabulary x y) (eq vocabulary y z))
    (eq vocabulary x z)

/-- PM I ✱13·171: `x = y . x = z ⊃ y = z`. -/
def star_13_171_target (vocabulary : DescriptionVocabulary signature sort order)
    (x y z : Term signature realContext apparentContext sort) :
    CoreFormula signature realContext apparentContext order :=
  imp vocabulary (conj vocabulary (eq vocabulary x y) (eq vocabulary x z))
    (eq vocabulary y z)

/-- PM I ✱13·172: `y = x . z = x ⊃ y = z`. -/
def star_13_172_target (vocabulary : DescriptionVocabulary signature sort order)
    (x y z : Term signature realContext apparentContext sort) :
    CoreFormula signature realContext apparentContext order :=
  imp vocabulary (conj vocabulary (eq vocabulary y x) (eq vocabulary z x))
    (eq vocabulary y z)

/-- PM I ✱13·18: `x = y . x ≠ z ⊃ y ≠ z`; each inequality is the printed
✱13·02 negation of identity. -/
def star_13_18_target (vocabulary : DescriptionVocabulary signature sort order)
    (x y z : Term signature realContext apparentContext sort) :
    CoreFormula signature realContext apparentContext order :=
  imp vocabulary
    (conj vocabulary (eq vocabulary x y) (neg vocabulary (eq vocabulary x z)))
    (neg vocabulary (eq vocabulary y z))

end PM.Architecture.Star13Q292Targets
