import Principia.FirstEdition.Volume2.Star112Source
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Definition of PM II, ✱112

The sum `Σʻκ` is a class.  Its defining right member is therefore supplied as
its exact membership matrix, and class abstraction is eliminated in the scope
of a continuation.
-/

structure Star112DefinitionVocabulary (signature : Signature)
    (summandSort : RSort) (matrixOrder scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (.function [summandSort] matrixOrder 0)
    (max (bindOrder matrixOrder summandSort) scopeOrder)
  universal : signature.Universal summandSort matrixOrder
  equivalenceNegation : signature.Negation matrixOrder
  equivalenceDisjunction : signature.Disjunction matrixOrder
  leftNegation : signature.Negation (bindOrder matrixOrder summandSort)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder matrixOrder summandSort) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder matrixOrder summandSort) scopeOrder)

/-- ✱112·01, with `sʻ∈↧ʻʻκ` represented by its exact membership matrix. -/
def star_112_01
    (vocabulary : Star112DefinitionVocabulary signature summandSort
      matrixOrder scopeOrder)
    (sumMembership : Formula signature real [summandSort] matrixOrder)
    (continuation : Formula signature real
      [.function [summandSort] matrixOrder 0] scopeOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder matrixOrder summandSort) scopeOrder)
        (.function [summandSort] matrixOrder 0)) :=
  .sometimes vocabulary.existential
    (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.always vocabulary.universal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (sumMembership.rename (liftRenaming (fun v => .succ v)))))
      continuation)

theorem star_112_01_unfold
    (vocabulary : Star112DefinitionVocabulary signature summandSort
      matrixOrder scopeOrder)
    (sumMembership : Formula signature real [summandSort] matrixOrder)
    (continuation : Formula signature real
      [.function [summandSort] matrixOrder 0] scopeOrder) :
    star_112_01 vocabulary sumMembership continuation =
      .sometimes vocabulary.existential
        (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
          vocabulary.outerNegation vocabulary.conjunctionDisjunction
          (.always vocabulary.universal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (sumMembership.rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

def star_112_01_reading
    (vocabulary : Star112DefinitionVocabulary signature summandSort
      matrixOrder scopeOrder)
    (sumMembership : Formula signature real [summandSort] matrixOrder)
    (continuation : Formula signature real
      [.function [summandSort] matrixOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱112·01. Σʻκ = sʻ∈↧ʻʻκ Df"
  parsed := .assertion (star_112_01 vocabulary sumMembership continuation)

end PM.RamifiedSyntax
