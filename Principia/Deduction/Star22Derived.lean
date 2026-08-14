import Principia.Deduction.Star4Ramified
import Principia.FirstEdition.Volume1.Star22Source

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱22

The class-forming signs of this number are incomplete symbols.  The four
class-valued operations below therefore take a continuation and expand by
✱20·01; they do not manufacture class terms.  Membership is ✱20·02.
-/

/-- The vocabulary needed by one predicative class abstraction ✱20·01. -/
structure Star22ClassVocabulary (signature : Signature)
    (order scopeOrder : Nat) where
  existential : ExistentialVocabulary signature (classSort order 0)
    (max (bindOrder order .individual) scopeOrder)
  universal : signature.Universal .individual order
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation (bindOrder order .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder order .individual) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder order .individual) scopeOrder)

/-- ✱22·01: inclusion, expanded as universal pointwise implication. -/
def star_22_01
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    Formula signature real [] (bindOrder order .individual) :=
  .always universal
    (implication negation disjunction
      (star_20_02 alpha.weaken (.apparent .zero))
      (star_20_02 beta.weaken (.apparent .zero)))

/-- ✱22·02: intersection, as the contextual abstraction ✱20·01. -/
def star_22_02 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (sameDisjunction disjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      (.neg negation (star_20_02 beta.weaken (.apparent .zero))))) continuation

/-- ✱22·03: union, as the contextual abstraction ✱20·01. -/
def star_22_03 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (sameDisjunction disjunction
      (star_20_02 alpha.weaken (.apparent .zero))
      (star_20_02 beta.weaken (.apparent .zero))) continuation

/-- ✱22·04: complement, as the contextual abstraction ✱20·01. -/
def star_22_04 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (alpha : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (star_20_02 alpha.weaken (.apparent .zero))) continuation

/-- ✱22·05: difference, with ✱22·02 and ✱22·04 fully eliminated. -/
def star_22_05 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (sameDisjunction disjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      (.neg negation (.neg negation
        (star_20_02 beta.weaken (.apparent .zero)))))) continuation

/-- Audited scope reading of ✱22·42. -/
def star_22_42_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order 0)) :
    ClaimReading signature real where
  printed := "⊢ . α ⊂ α"
  parsed := .assertion (star_22_01 universal negation disjunction alpha alpha)

/-- ✱22·42, following PM's printed `[Id.*10·11]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_42
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order 0)) :
    Derivation (star_22_42_reading universal negation disjunction alpha).parsed := by
  let body := star_20_02 alpha.weaken (.apparent .zero)
  let value : Term signature (.individual :: real) [] .individual :=
    .real (.zero : Var (.individual :: real) .individual)
  have line1 : Derivation (.assertion
      ((implication negation disjunction body body).weakenReal.instantiate value)) := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    exact star_2_08 negation disjunction (body.weakenReal.instantiate value)
  have line2 := Derivation.star_10_11 universal
    (implication negation disjunction body body) line1
  exact line2

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_22_42
