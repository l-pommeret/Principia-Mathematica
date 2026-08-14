import Principia.Deduction.Star23Derived
import Principia.FirstEdition.Volume1.Star24Source

namespace PM.RamifiedSyntax

/-!
# Derived declarations of PM I, ✱24

The opening definitions that the present vocabulary can express are
represented as eliminable contextual abbreviations.  ✱24·02 is withdrawn:
the ramified complement expansion from ✱22 is not yet available here.  No
theorem is claimed: every displayed proposition of the chapter first needs
either elimination of a class abstraction under Leibniz identity or one of
the still-unavailable ramified ✱22 class rules.
-/

/-- ✱24·01: the universal class, contextually, is `ẑx(x = x)`. -/
def star_24_01
    (identity : IdentityVocabulary signature .individual order excess)
    (existential : ExistentialVocabulary signature
      (classSort (bindOrder order
        (.function [.individual] order excess)) 0)
      (max
        (bindOrder (bindOrder order
          (.function [.individual] order excess)) .individual)
        scopeOrder))
    (universal : signature.Universal .individual
      (bindOrder order (.function [.individual] order excess)))
    (equivalenceNegation : signature.Negation
      (bindOrder order (.function [.individual] order excess)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder order (.function [.individual] order excess)))
    (leftNegation : signature.Negation
      (bindOrder (bindOrder order
        (.function [.individual] order excess)) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max
        (bindOrder (bindOrder order
          (.function [.individual] order excess)) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max
        (bindOrder (bindOrder order
          (.function [.individual] order excess)) .individual)
        scopeOrder))
    (continuation : Formula signature real
      (classSort (bindOrder order
        (.function [.individual] order excess)) 0 :: apparent)
      scopeOrder) : Formula signature real apparent
        (bindOrder
          (max
            (bindOrder (bindOrder order
              (.function [.individual] order excess)) .individual)
            scopeOrder)
          (classSort (bindOrder order
            (.function [.individual] order excess)) 0)) :=
  star_20_01 existential universal equivalenceNegation
    equivalenceDisjunction leftNegation rightNegation outerNegation
    conjunctionDisjunction
    (star_13_01 identity (.apparent .zero) (.apparent .zero))
    continuation

/-- ✱24·03: class existence is existential membership. -/
def star_24_03
    (existential : ExistentialVocabulary signature .individual order)
    (membership : Formula signature real [.individual] order) :
    Formula signature real [] (bindOrder order .individual) :=
  .sometimes existential membership

end PM.RamifiedSyntax
