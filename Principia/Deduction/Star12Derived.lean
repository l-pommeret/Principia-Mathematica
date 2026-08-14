import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Primitive propositions of PM I, ✱12

The two reducibility assertions are primitive propositions of PM and therefore
have no derivational premises.  Their non-logical assumption is recorded as
`PM1:REDUCIBILITY` in the certification metadata.
-/

/-- ✱12·1.  The non-logical assumption is `PM1:REDUCIBILITY`. -/
theorem star_12_1
    (existential : ExistentialVocabulary signature
      (.function [argument] order 0) (bindOrder order argument))
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [argument] order) :
    ⊢ᵣ star_12_1_formula existential universal negation disjunction phi := by
  exact Derivation.star_12_1 existential universal negation disjunction phi

/-- ✱12·11.  The non-logical assumption is `PM1:REDUCIBILITY`. -/
theorem star_12_11
    (existential : ExistentialVocabulary signature
      (.function [leftSort, rightSort] order 0)
      (bindOrder (bindOrder order leftSort) rightSort))
    (leftUniversal : signature.Universal leftSort order)
    (rightUniversal : signature.Universal rightSort
      (bindOrder order leftSort))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [leftSort, rightSort] order) :
    ⊢ᵣ star_12_11_formula existential leftUniversal rightUniversal
      negation disjunction phi := by
  exact Derivation.star_12_11 existential leftUniversal rightUniversal
    negation disjunction phi

end PM.RamifiedSyntax
