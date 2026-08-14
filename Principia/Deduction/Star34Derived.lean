import Principia.Deduction.Star33Derived
import Principia.FirstEdition.Volume1.Star34Source

namespace PM.RamifiedSyntax

/-! # PM I, ✱34 — relative product -/

/-- Conjunction at one ramified order, PM's ✱3·01 abbreviation. -/
private def conjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation (sameDisjunction disjunction
    (.neg negation left) (.neg negation right))

/-- The matrix `(∃y).xRy.ySz` in the definition ✱34·01.

This is the eliminable application of `R|S` to `x,z`.  The relation
abstraction itself remains contextual, as required by ✱21·01. -/
def star_34_01
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (left : Term signature real apparent
      (relationSort relationOrder leftExcess))
    (right : Term signature real apparent
      (relationSort relationOrder rightExcess))
    (x z : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  .sometimes existential
    (conjunction negation disjunction
      (applyBinary left.weaken x.weaken (.apparent .zero))
      (applyBinary right.weaken (.apparent .zero) z.weaken))

/-- The eliminable application `xR²z` from the definition ✱34·02. -/
def star_34_02
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x z : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  star_34_01 existential negation disjunction relation relation x z

/-- The eliminable application `xR³z` from the definition ✱34·03. -/
def star_34_03
    (existential : ExistentialVocabulary signature .individual relationOrder)
    (negation : signature.Negation relationOrder)
    (disjunction : signature.Disjunction relationOrder)
    (square relation : Term signature real apparent
      (relationSort relationOrder relationExcess))
    (x z : Term signature real apparent .individual) :
    Formula signature real apparent (bindOrder relationOrder .individual) :=
  star_34_01 existential negation disjunction square relation x z

/-!
✱34·01--·03 cannot honestly be definitions returning relation terms:
`RamifiedSyntax` deliberately has no term constructor for an incomplete
relation abstraction.  The definitions above therefore give their eliminable
applications.  Likewise ✱34·1 needs the missing derivational
conversion ✱21·3 between that contextual abstraction and its application.
No assertion is therefore weakened to the reflexive expansion above.
-/

end PM.RamifiedSyntax
