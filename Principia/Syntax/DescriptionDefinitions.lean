import Principia.Syntax.Description

namespace PM.DescriptionSyntax.Formula

/-! # The reductional description definitions ✱14·02–·04

This module extends the kernel-checked ✱14·01 syntax without changing it, so
the immutable Q296 interface remains reproducible.  The three constructions
below are definitions of formulae and scope brackets.  They introduce no
description-valued term, semantic existence predicate, assertion rule, or
object-language `Prop`.

Source witnesses: first-edition volume I, leaf 204 / printed p. 182, SHA-256
`23427375b6f708a53ed91a28fb43eed247d732ff4047ee7e88fd779e2a50ad28`.
-/

/-- Conjunction at one assigned order, expressed through PM's negation and
disjunction meanings rather than a global connective. -/
def conj (vocabulary : DescriptionVocabulary signature sort order)
    (left right : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  .neg vocabulary.negation
    (.disj vocabulary.disjunction (.neg vocabulary.negation left)
      (.neg vocabulary.negation right))

/-- Formal equivalence at one assigned order. -/
def iff (vocabulary : DescriptionVocabulary signature sort order)
    (left right : Formula signature realContext apparentContext order) :
    Formula signature realContext apparentContext order :=
  conj vocabulary (imp vocabulary left right) (imp vocabulary right left)

/-- Insert a fresh outer candidate immediately below an existing head
binder.  The old head remains index zero and every tail index crosses the new
candidate. -/
def insertAfterHeadSubstitution :
    Substitution signature realContext (head :: tail) (head :: inserted :: tail)
  | _, .zero => .apparent .zero
  | _, .succ entry => .apparent (.succ (.succ entry))

/-- The surface formula `(x) : φx ≡ x=b`, in the context of candidate `b`.
This is the exact uniqueness matrix printed in ✱14·01/·02; no redundant `φb`
conjunct is inserted. -/
def uniqueMatrix (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext (sort :: apparentContext) order :=
  let conditionAtFresh := condition.substitute
    (insertAfterHeadSubstitution (inserted := sort))
  let fresh : Term signature realContext (sort :: sort :: apparentContext) sort :=
    .apparent .zero
  let candidate : Term signature realContext (sort :: sort :: apparentContext) sort :=
    .apparent (.succ .zero)
  let equality := Formula.equal vocabulary.equality fresh candidate
  .always vocabulary.universal (iff vocabulary conditionAtFresh equality)

/-- ✱14·02 definiendum `E!(℩x)(φx)`, represented as a contextual formula and
never as a predicate applied to a description term. -/
def descriptionExists
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .sometimes vocabulary.existential (uniqueMatrix vocabulary condition)

/-- Exact reduction of ✱14·02:
`E!(℩x)(φx) .=: (∃b) : φx ≡ₓ x=b`. -/
theorem star_14_02_reduction
    (vocabulary : DescriptionVocabulary signature sort order)
    (condition : Formula signature realContext (sort :: apparentContext) order) :
    descriptionExists vocabulary condition =
      .sometimes vocabulary.existential (uniqueMatrix vocabulary condition) := rfl

/-- Lift an independently written one-variable condition beneath an already
active outer description candidate. -/
def conditionUnderOuter
    (condition : Formula signature realContext (innerSort :: apparentContext) order) :
    Formula signature realContext
      (innerSort :: outerSort :: apparentContext) order :=
  condition.substitute (insertAfterHeadSubstitution (inserted := outerSort))

/-- The comma scope introduced at ✱14·03.  `[Descφ, Descψ]. f(Descφ,Descψ)`
is definitionally the nested scope `[Descφ] : [Descψ]. f(Descφ,Descψ)`.
The inner candidate is de Bruijn index zero; the outer candidate is index one. -/
def descriptionScopePair
    (outerVocabulary : DescriptionVocabulary signature outerSort order)
    (innerVocabulary : DescriptionVocabulary signature innerSort order)
    (outerCondition :
      Formula signature realContext (outerSort :: apparentContext) order)
    (innerCondition :
      Formula signature realContext (innerSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (innerSort :: outerSort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  .descriptionScope outerVocabulary outerCondition
    (.descriptionScope innerVocabulary
      (conditionUnderOuter innerCondition)
      continuation)

/-- Exact reduction of the comma bracket in ✱14·03. -/
theorem star_14_03_reduction
    (outerVocabulary : DescriptionVocabulary signature outerSort order)
    (innerVocabulary : DescriptionVocabulary signature innerSort order)
    (outerCondition :
      Formula signature realContext (outerSort :: apparentContext) order)
    (innerCondition :
      Formula signature realContext (innerSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (innerSort :: outerSort :: apparentContext) order) :
    descriptionScopePair outerVocabulary innerVocabulary outerCondition
        innerCondition continuation =
      .descriptionScope outerVocabulary outerCondition
        (.descriptionScope innerVocabulary
          (conditionUnderOuter innerCondition)
          continuation) := rfl

/-- ✱14·04 makes the later, explicitly bracketed description the outer
scope.  This is not commutation: the two candidate indices and conditions are
passed in the printed elimination order. -/
def laterDescriptionOuterScope
    (laterVocabulary : DescriptionVocabulary signature laterSort order)
    (earlierVocabulary : DescriptionVocabulary signature earlierSort order)
    (laterCondition :
      Formula signature realContext (laterSort :: apparentContext) order)
    (earlierCondition :
      Formula signature realContext (earlierSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (earlierSort :: laterSort :: apparentContext) order) :
    Formula signature realContext apparentContext order :=
  descriptionScopePair laterVocabulary earlierVocabulary laterCondition
    earlierCondition continuation

/-- Exact scope-order reduction of ✱14·04. -/
theorem star_14_04_reduction
    (laterVocabulary : DescriptionVocabulary signature laterSort order)
    (earlierVocabulary : DescriptionVocabulary signature earlierSort order)
    (laterCondition :
      Formula signature realContext (laterSort :: apparentContext) order)
    (earlierCondition :
      Formula signature realContext (earlierSort :: apparentContext) order)
    (continuation : Formula signature realContext
      (earlierSort :: laterSort :: apparentContext) order) :
    laterDescriptionOuterScope laterVocabulary earlierVocabulary laterCondition
        earlierCondition continuation =
      descriptionScopePair laterVocabulary earlierVocabulary laterCondition
        earlierCondition continuation := rfl

end PM.DescriptionSyntax.Formula
