import Principia.Deduction.Star33Derived
import Principia.Deduction.Star34Derived
import Principia.FirstEdition.Volume1.Star43Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱43 — relations of relations

✱43 works with the two *sections* of the relative product, `(R |)` and
`(| R)`, and with their relative product `R ∥ S`.  A section is not a new
primitive: ✱38·01 reads `x♀ = ûŷ(u = x♀y)`, so with `♀ := |` and `x := R` the
section `R |` is the relation abstraction `P̂Q̂(P = R | Q)`.  The relata of that
abstraction are relations, not individuals, which is why the elimination used
here is the heterogeneous ✱21·3 instance `binaryElimination` of ✱33 rather
than the individual-typed `star_38_1`.

Nothing below introduces a `Term` for a section, for a relative product, or
for `∥`: each remains an incomplete symbol whose numbered definition expands
contextually.
-/

/-! ## ✱43·01, an eliminable definition -/

/-- ✱43·01: `R ∥ S = (R |) | (| S)  Df`.

The right member is a relative product, so by ✱34·01 — read at the type whose
relata are relations, as PM's typical ambiguity requires — the application
`P(R ∥ S)Q` is `(∃M). P(R |)M . M(| S)Q`.  The two section applications are
themselves incomplete symbols and are therefore taken as the printed section
formulae, exactly as ✱38·01's `operationEquation` is taken at ✱38.

The bound middle relation is the apparent variable of index zero in both
sections; the two conjuncts keep independent ramified orders. -/
def star_43_01
    (existential : ExistentialVocabulary signature middleSort
      (max leftOrder rightOrder))
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (leftSection : Formula signature real (middleSort :: apparent) leftOrder)
    (rightSection : Formula signature real (middleSort :: apparent) rightOrder) :
    Formula signature real apparent
      (bindOrder (max leftOrder rightOrder) middleSort) :=
  .sometimes existential
    (mixedConjunction leftNegation rightNegation outerNegation disjunction
      leftSection rightSection)

theorem star_43_01_unfold
    (existential : ExistentialVocabulary signature middleSort
      (max leftOrder rightOrder))
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (leftSection : Formula signature real (middleSort :: apparent) leftOrder)
    (rightSection : Formula signature real (middleSort :: apparent) rightOrder) :
    star_43_01 existential leftNegation rightNegation outerNegation disjunction
        leftSection rightSection =
      .neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation
            (.neg outerNegation
              (.disj disjunction
                (.neg leftNegation leftSection)
                (.neg rightNegation rightSection))))) := rfl

/-! ## The two sections and their product, eliminated by ✱21·3

`binaryElimination` of ✱33 is the ✱21·3 instance whose two relata carry
independent sorts.  Taking both of them to be a relation sort is what PM's
typical ambiguity licenses, and it is what ✱43 needs: `P`, `Q` and the bound
witness of ✱21·01 all range over relations.
-/

/-- The sort of the relata throughout ✱43. -/
abbrev star_43_relatumSort (memberOrder memberExcess : Nat) : RSort :=
  relationSort memberOrder memberExcess

/-- Audited contextual reading of ✱43·1. -/
def star_43_1_reading
    (vocabulary : BinaryEliminationVocabulary signature
      (star_43_relatumSort memberOrder memberExcess)
      (star_43_relatumSort memberOrder memberExcess) resultOrder)
    (operationEquation : Formula signature real
      [star_43_relatumSort memberOrder memberExcess,
        star_43_relatumSort memberOrder memberExcess] resultOrder)
    (p q : Term signature real []
      (star_43_relatumSort memberOrder memberExcess)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱43·1. ⊢ : P(R |)Q .≡ . P = R | Q"
  scopeReading :=
    "The left section is eliminated by ✱38·01 read at the type of relations; its relation abstraction has the scope of the displayed equivalence."
  parsed := .assertion (binaryEliminationFormula
    vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction operationEquation p q)

/-- ✱43·1, the ✱21·3 elimination of the left section `(R |)`.

PM prints no demonstration for this line, so the route is chosen here: it is
✱38·1 read at the type of relations.  The remaining premise is the same
reducibility-scope transport that ✱21·3 still carries.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_43_1
    (vocabulary : BinaryEliminationVocabulary signature
      (star_43_relatumSort memberOrder memberExcess)
      (star_43_relatumSort memberOrder memberExcess) resultOrder)
    (operationEquation : Formula signature real
      [star_43_relatumSort memberOrder memberExcess,
        star_43_relatumSort memberOrder memberExcess] resultOrder)
    (p q : Term signature real []
      (star_43_relatumSort memberOrder memberExcess))
    (star_10_35_hypothesis : BinaryEliminationHypothesis vocabulary
      operationEquation p q) :
    Derivation (star_43_1_reading vocabulary operationEquation p q).parsed :=
  binaryElimination vocabulary operationEquation p q star_10_35_hypothesis

/-- Audited contextual reading of ✱43·101. -/
def star_43_101_reading
    (vocabulary : BinaryEliminationVocabulary signature
      (star_43_relatumSort memberOrder memberExcess)
      (star_43_relatumSort memberOrder memberExcess) resultOrder)
    (operationEquation : Formula signature real
      [star_43_relatumSort memberOrder memberExcess,
        star_43_relatumSort memberOrder memberExcess] resultOrder)
    (p q : Term signature real []
      (star_43_relatumSort memberOrder memberExcess)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱43·101. ⊢ : P(| R)Q .≡ . P = Q | R"
  scopeReading :=
    "The right section is independently eliminated by ✱38·02 read at the type of relations; its relation abstraction has the scope of the displayed equivalence."
  parsed := .assertion (binaryEliminationFormula
    vocabulary.abstractionExistential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction operationEquation p q)

/-- ✱43·101, the ✱21·3 elimination of the right section `(| R)`.

Its operation equation is `P = Q | R`, printed with the two relata in the
other order; the section is built from ✱38·02, not from ✱43·1.
`demonstration_provenance: editorial-reconstruction`.
`direct_assumptions: PM1:REDUCIBILITY-SCOPE-TRANSPORT`. -/
theorem star_43_101
    (vocabulary : BinaryEliminationVocabulary signature
      (star_43_relatumSort memberOrder memberExcess)
      (star_43_relatumSort memberOrder memberExcess) resultOrder)
    (operationEquation : Formula signature real
      [star_43_relatumSort memberOrder memberExcess,
        star_43_relatumSort memberOrder memberExcess] resultOrder)
    (p q : Term signature real []
      (star_43_relatumSort memberOrder memberExcess))
    (star_10_35_hypothesis : BinaryEliminationHypothesis vocabulary
      operationEquation p q) :
    Derivation (star_43_101_reading vocabulary operationEquation p q).parsed :=
  binaryElimination vocabulary operationEquation p q star_10_35_hypothesis

/-! ## ✱43·102, the two members built apart

`∥` is *not* a double descriptive function: ✱43·01 defines it as the relative
product of the two sections, so the left member of ✱43·102 must be built by
✱34·01 out of `(R |)` and `(| S)`, never by giving `∥` a section's abstraction
matrix.  Doing the latter would put the content of ✱43·102 into the reading
instead of deriving it.
-/

/-- The left member of ✱43·102: `P(R ∥ S)Q`, expanded by ✱43·01 into the
relative product `(∃M). P(R |)M . M(| S)Q`. -/
def star_43_102_left
    (existential : ExistentialVocabulary signature
      (star_43_relatumSort memberOrder memberExcess)
      (max leftOrder rightOrder))
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (leftSection : Formula signature real
      [star_43_relatumSort memberOrder memberExcess] leftOrder)
    (rightSection : Formula signature real
      [star_43_relatumSort memberOrder memberExcess] rightOrder) :
    Formula signature real []
      (bindOrder (max leftOrder rightOrder)
        (star_43_relatumSort memberOrder memberExcess)) :=
  star_43_01 existential leftNegation rightNegation outerNegation disjunction
    leftSection rightSection

/-- The right member of ✱43·102: the printed identity `P = R | Q | S`.

It is an assumed formula for the same reason ✱38·01's `operationEquation` is:
`R | Q | S` is an incomplete symbol of ✱34·01 nested inside the ✱13·01
identity, and this module introduces no relation term for it. -/
def star_43_102_right
    (productIdentity : Formula signature real []
      (bindOrder (max leftOrder rightOrder)
        (star_43_relatumSort memberOrder memberExcess))) :
    Formula signature real []
      (bindOrder (max leftOrder rightOrder)
        (star_43_relatumSort memberOrder memberExcess)) :=
  productIdentity

/-- Audited reading of ✱43·102. -/
def star_43_102_reading
    (existential : ExistentialVocabulary signature
      (star_43_relatumSort memberOrder memberExcess)
      (max leftOrder rightOrder))
    (leftNegation : signature.Negation leftOrder)
    (rightNegation : signature.Negation rightOrder)
    (outerNegation : signature.Negation (max leftOrder rightOrder))
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (equalityNegation : signature.Negation
      (bindOrder (max leftOrder rightOrder)
        (star_43_relatumSort memberOrder memberExcess)))
    (equalityDisjunction : signature.Disjunction
      (bindOrder (max leftOrder rightOrder)
        (star_43_relatumSort memberOrder memberExcess)))
    (leftSection : Formula signature real
      [star_43_relatumSort memberOrder memberExcess] leftOrder)
    (rightSection : Formula signature real
      [star_43_relatumSort memberOrder memberExcess] rightOrder)
    (productIdentity : Formula signature real []
      (bindOrder (max leftOrder rightOrder)
        (star_43_relatumSort memberOrder memberExcess))) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "✱43·102. ⊢ : P(R ∥ S)Q .≡ . P = R | Q | S"
  scopeReading :=
    "`R ∥ S` is eliminated by ✱43·01, so the left member is the ✱34·01 relative product of the two sections; the bound middle relation has the scope of that member only."
  parsed := .assertion (star_4_01 equalityNegation equalityDisjunction
    (star_43_102_left existential leftNegation rightNegation outerNegation
      disjunction leftSection rightSection)
    (star_43_102_right productIdentity))

/-!
## What still resists, at the level of `Formula` constructors

* ✱43·102 is recorded as a reading only.  Its two members are
  ```
  left  = .neg out (.always uni (.neg mat
            (.neg o (.disj d (.neg ln SECTION_LEFT) (.neg rn SECTION_RIGHT)))))
  right = PRODUCT_IDENTITY
  ```
  and no reduction takes one to the other: the left is rooted at `.neg`
  above an `.always`, the right at whatever ✱13·01 builds over `.always`
  binding a predicate variable.  PM closes the gap by replacing each section
  with its ✱43·1·101 equation and then eliminating the existential by ✱13·195
  — and ✱13·195 is presently a self-hypothesis, not a derived proposition.
  Identifying the two members here would be exactly the collapse the two-sided
  gate exists to catch.
* ✱43·11 `(R |)ʻQ = R | Q`, ✱43·111, ✱43·112 and the existence lines
  ✱43·12·121·122 are about the *descriptive function* `(R |)ʻQ`, whose ✱30·01
  expansion is a `Formula.descriptionScope` node.  No rule of `Derivation`
  eliminates `descriptionScope`, and `.descriptionScope` does not reduce to
  the `.neg (.always (.neg _))` tree that ✱43·1 delivers: the two trees differ
  at their root constructor.
* ✱43·2·201·202·21·211·212·213·22 assert *equalities between relations of
  relations*.  After ✱21·01 each member is a `Formula.sometimes` tree rooted
  at `.neg`, and PM's equality sign between them is ✱13·01, i.e. a further
  `.always` over a predicate variable of the sort
  `.function [relationSort (relationSort …) …] … …`.  Building that identity
  is possible; discharging it needs ✱21·43, which is not yet derived.
* ✱43·3·301·302 need the converse domain ✱33·02 of a relation *of relations*
  and then ✱43·1; ✱43·31·311·312 additionally need the restriction `↾` of
  ✱35·02.  Both are class-valued incomplete symbols whose elimination goes
  back through ✱20·3.
* ✱43·34 to ✱43·51 combine the above with images (✱37·01), sums (✱41·02) and
  limited domains; none is reachable while the ✱21·3 transport premise of
  ✱43·1 is itself open.

Nothing here is asserted without its premise, and no relation term has been
invented to make an equality reflexive.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_43_01_unfold
#print axioms PM.RamifiedSyntax.star_43_1
#print axioms PM.RamifiedSyntax.star_43_101
