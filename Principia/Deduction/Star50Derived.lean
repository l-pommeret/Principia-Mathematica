import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star50Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱50

The identity relation of ✱50·01 is an eliminable abbreviation.  Pointwise,
its matrix is the Leibniz identity of ✱13·01.
-/

/-- ✱50·01 applied to two arguments.  A printed `Df` remains reducible. -/
def star_50_01_application
    (vocabulary : IdentityVocabulary signature sort order excess)
    (x y : Term signature real [] sort) :
    Formula signature real []
      (bindOrder order (.function [sort] order excess)) :=
  star_13_01 vocabulary x y

/-- Audited object-syntax reading of ✱50·1. -/
def star_50_1_reading
    (vocabulary : IdentityVocabulary signature sort order excess)
    (negation : signature.Negation
      (bindOrder order (.function [sort] order excess)))
    (disjunction : signature.Disjunction
      (bindOrder order (.function [sort] order excess)))
    (x y : Term signature real [] sort) : ClaimReading signature real where
  printed := "⊢ : xIy .≡. x = y  [✱21·3.(✱50·01)]"
  parsed := .assertion (equivalence negation disjunction
    (star_50_01_application vocabulary x y) (star_13_01 vocabulary x y))

/-!
The order-cast purity obstruction formerly recorded here has been repaired:
ramified ✱13·1 is now unconditional and axiom-free.  Nevertheless ✱50·1 is not
declared, because PM's printed justification is specifically
`[✱21·3.(✱50·01)]`, and no ramified theorem `star_21_3` is currently available.
Using the propositionally sufficient ✱4·2 after unfolding the definition would
not follow the printed dependency path required by the certification contract.
-/

end PM.RamifiedSyntax
