import Principia.Deduction.Star13Derived
import Principia.Deduction.Star33Derived
import Principia.FirstEdition.Volume1.Star55Source
import Principia.Syntax.RamifiedReading

namespace PM.RamifiedSyntax

/-!
# Definitions and derived propositions of PM I, ✱55

The ordinal-couple definition is a contextual binary relation abstraction.
After eliminating the unit classes and their Cartesian product, its matrix is
exactly `z = x . w = y`, with both equalities interpreted by ✱13·01.

Among the 81 catalogue items assigned to ✱55, the propositions listed below
have printed demonstrations whose first indispensable object-judgement premise
is not yet available in the ramified deduction layer:

* ✱55·2: ✱30·37 (and then ✱55·11/·12);
* ✱55·224: ✱55·222/·223;
* ✱55·232: ✱55·231 and ✱11·55;
* ✱55·24: ✱41·11;
* ✱55·241: the complete derivation of ✱55·24;
* ✱55·25: ✱37·67 and ✱33·12;
* ✱55·251: the complete derivation of ✱55·25;
* ✱55·32: ✱55·3;
* ✱55·341: ✱4·42 and ✱25·54;
* ✱55·36: ✱55·3 and ✱23·62;
* ✱55·37: ✱35·103 and ✱55·3;
* ✱55·42: ✱55·4;
* ✱55·431: ✱55·4 and ✱55·43;
* ✱55·44: ✱55·43, ✱55·431, and ✱55·202;
* ✱55·5: ✱25·12, ✱23·58/·42, and ✱55·341.

Thus none of the exact asserted claims is declared here. A theorem taking its
own conclusion as a premise, a host-logic set-theoretic surrogate, or a new
`Derivation` constructor would all be false progress under T3/T6/T10.
-/

/-- Vocabulary for the contextual binary abstraction defining an ordinal
couple. -/
structure Star55DefinitionVocabulary (signature : Signature)
    (resultOrder scopeOrder : Nat) where
  existential : ExistentialVocabulary signature (relationSort resultOrder 0)
    (max (bindOrder (bindOrder resultOrder .individual) .individual)
      scopeOrder)
  leftUniversal : signature.Universal .individual resultOrder
  rightUniversal : signature.Universal .individual
    (bindOrder resultOrder .individual)
  equivalenceNegation : signature.Negation resultOrder
  equivalenceDisjunction : signature.Disjunction resultOrder
  leftNegation : signature.Negation
    (bindOrder (bindOrder resultOrder .individual) .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder resultOrder .individual) .individual)
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder resultOrder .individual) .individual)
      scopeOrder)

/-- The fully eliminated product-of-unit-classes matrix at ✱55·01. -/
def star_55_01_matrix
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real apparent .individual) :
    Formula signature real (.individual :: .individual :: apparent)
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)) :=
  conjunction negation disjunction
    (star_13_01 identity (.apparent .zero) x.weaken.weaken)
    (star_13_01 identity (.apparent (.succ .zero)) y.weaken.weaken)

theorem star_55_01_matrix_unfold
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real apparent .individual) :
    star_55_01_matrix identity negation disjunction x y =
      conjunction negation disjunction
        (star_13_01 identity (.apparent .zero) x.weaken.weaken)
        (star_13_01 identity (.apparent (.succ .zero)) y.weaken.weaken) := rfl

/-- ✱55·01, `x↓y = ιʻx ↑ ιʻy`, with all three incomplete symbols
eliminated contextually. -/
def star_55_01
    (vocabulary : Star55DefinitionVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real apparent .individual)
    (continuation : Formula signature real
      (relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder identityExcess)) 0 :: apparent)
      scopeOrder) :=
  binaryAbstraction vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (star_55_01_matrix identity negation disjunction x y) continuation

theorem star_55_01_unfold
    (vocabulary : Star55DefinitionVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real apparent .individual)
    (continuation : Formula signature real
      (relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder identityExcess)) 0 :: apparent)
      scopeOrder) :
    star_55_01 vocabulary identity negation disjunction x y continuation =
      binaryAbstraction vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_55_01_matrix identity negation disjunction x y) continuation := rfl

/-- ✱55·02, `Rʻx↓y = Rʻ(x↓y)`: the application formula is placed in the
continuation of the ordinal-couple abstraction, so the parentheses and scope
are represented in the AST rather than by a relation-valued term. -/
def star_55_02
    (vocabulary : Star55DefinitionVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real apparent .individual)
    (application : Formula signature real
      (relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder identityExcess)) 0 :: apparent)
      scopeOrder) :=
  star_55_01 vocabulary identity negation disjunction x y application

theorem star_55_02_unfold
    (vocabulary : Star55DefinitionVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real apparent .individual)
    (application : Formula signature real
      (relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder identityExcess)) 0 :: apparent)
      scopeOrder) :
    star_55_02 vocabulary identity negation disjunction x y application =
      binaryAbstraction vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction
        (star_55_01_matrix identity negation disjunction x y) application := rfl

/-- Audited definitional reading of the PM-VERBATIM block ✱55·01. -/
def star_55_01_reading
    (vocabulary : Star55DefinitionVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real [] .individual)
    (continuation : Formula signature real
      [relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder identityExcess)) 0]
      scopeOrder) : RamifiedReading signature real where
  printed := PM.pmPrinted "✱55·01. x↓y = ιʻx ↑ ιʻy  Df"
  parsed := .assertion
    (star_55_01 vocabulary identity negation disjunction x y continuation)
  scopeReading :=
    "The two unit classes and their product are eliminated inside the contextual ordinal-couple abstraction."

/-- Audited definitional reading of the PM-VERBATIM block ✱55·02. -/
def star_55_02_reading
    (vocabulary : Star55DefinitionVocabulary signature
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)) scopeOrder)
    (identity : IdentityVocabulary signature .individual identityOrder
      identityExcess)
    (negation : signature.Negation
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (disjunction : signature.Disjunction
      (bindOrder identityOrder
        (.function [.individual] identityOrder identityExcess)))
    (x y : Term signature real [] .individual)
    (application : Formula signature real
      [relationSort
        (bindOrder identityOrder
          (.function [.individual] identityOrder identityExcess)) 0]
      scopeOrder) : RamifiedReading signature real where
  printed := PM.pmPrinted "✱55·02. Rʻx↓y = Rʻ(x↓y)  Df"
  parsed := .assertion
    (star_55_02 vocabulary identity negation disjunction x y application)
  scopeReading :=
    "The ordinal couple is the bound relation argument of the contextual R-application."

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_55_01_matrix
#print axioms PM.RamifiedSyntax.star_55_01_matrix_unfold
#print axioms PM.RamifiedSyntax.star_55_01
#print axioms PM.RamifiedSyntax.star_55_01_unfold
#print axioms PM.RamifiedSyntax.star_55_01_reading
#print axioms PM.RamifiedSyntax.star_55_02
#print axioms PM.RamifiedSyntax.star_55_02_unfold
#print axioms PM.RamifiedSyntax.star_55_02_reading
