import Principia.Deduction.Star34Derived
import Principia.FirstEdition.Volume1.Star35Source

namespace PM.RamifiedSyntax

/-- Conjunction at one ramified order, PM's ✱3·01 abbreviation. -/
private def conjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation (sameDisjunction disjunction
    (.neg negation left) (.neg negation right))

/-- The eliminable application `x(α↿R)y` from the definition ✱35·01. -/
def star_35_01
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order classExcess))
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  conjunction negation disjunction
    (applyUnary alpha x) (applyBinary relation x y)

/-- The eliminable application `x(R↾β)y` from the definition ✱35·02. -/
def star_35_02
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (beta : Term signature real apparent (classSort order classExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  conjunction negation disjunction
    (applyBinary relation x y) (applyUnary beta y)

/-- The eliminable application `x(α↿R↾β)y` from the definition ✱35·03. -/
def star_35_03
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order leftClassExcess))
    (relation : Term signature real apparent
      (relationSort order relationExcess))
    (beta : Term signature real apparent (classSort order rightClassExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  conjunction negation disjunction (applyUnary alpha x)
    (conjunction negation disjunction
      (applyBinary relation x y) (applyUnary beta y))

/-- The eliminable application `x(α↑β)y` from the definition ✱35·04. -/
def star_35_04
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real apparent (classSort order leftClassExcess))
    (beta : Term signature real apparent (classSort order rightClassExcess))
    (x y : Term signature real apparent .individual) :
    Formula signature real apparent order :=
  conjunction negation disjunction (applyUnary alpha x) (applyUnary beta y)

/-!
# Derived propositions of PM I, ✱35

The ramified syntax is the required object language for this section.  The
printed demonstrations of ✱35·21, ·26, ·31, ·35, ·354, ·43, ·44, ·451, ·46,
·471, ·48, and ·51 were audited before adding declarations here.

Their first steps use object-calculus versions of ✱34·1 and ✱35·1/·101/·102,
and their final `⊃⊢.Prop` steps use relational extensionality.  None of those
derived rules is presently exposed as a `Derivation` theorem in the ramified
calculus.  Consequently this module deliberately declares none of the twelve
catalogue theorems yet: taking the displayed equality as a premise, or taking
an arbitrary implication to it as a premise, would only hide the missing
derivation and would violate the certification contract.

The relevant syntax is not missing: `star_13_01`, `star_20_01`, and
`star_21_01` provide equality, class abstraction, and relation abstraction.
What remains missing is the preceding derived deduction layer needed by the
printed proofs.
-/

end PM.RamifiedSyntax
