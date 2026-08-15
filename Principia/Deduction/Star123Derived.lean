import Principia.FirstEdition.Volume2.Star123Source
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-! # Definition of PM II, ✱123 -/

/-- Vocabulary for the contextual class of classes `ℵ₀`. -/
structure Star123DefinitionVocabulary (signature : Signature)
    (classOrder relationOrder conditionOrder scopeOrder : Nat) where
  classExistential : ExistentialVocabulary signature
    (.function [classSort classOrder 0]
      (bindOrder conditionOrder (relationSort relationOrder 0)) 0)
    (max
      (bindOrder
        (bindOrder conditionOrder (relationSort relationOrder 0))
        (classSort classOrder 0))
      scopeOrder)
  classUniversal : signature.Universal (classSort classOrder 0)
    (bindOrder conditionOrder (relationSort relationOrder 0))
  equivalenceNegation : signature.Negation
    (bindOrder conditionOrder (relationSort relationOrder 0))
  equivalenceDisjunction : signature.Disjunction
    (bindOrder conditionOrder (relationSort relationOrder 0))
  leftNegation : signature.Negation
    (bindOrder
      (bindOrder conditionOrder (relationSort relationOrder 0))
      (classSort classOrder 0))
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max
      (bindOrder
        (bindOrder conditionOrder (relationSort relationOrder 0))
        (classSort classOrder 0))
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max
      (bindOrder
        (bindOrder conditionOrder (relationSort relationOrder 0))
        (classSort classOrder 0))
      scopeOrder)

/-- The matrix `R∈Prog . A=DʻR`, existentially closed over `R`. -/
def star_123_01_matrix
    (relationExistential : ExistentialVocabulary signature
      (relationSort relationOrder 0) conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (progression domainIdentity : Formula signature real
      (relationSort relationOrder 0 :: classSort classOrder 0 :: [])
      conditionOrder) :
    Formula signature real [classSort classOrder 0]
      (bindOrder conditionOrder (relationSort relationOrder 0)) :=
  .sometimes relationExistential
    (conjunction negation disjunction progression domainIdentity)

theorem star_123_01_matrix_unfold
    (relationExistential : ExistentialVocabulary signature
      (relationSort relationOrder 0) conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (progression domainIdentity : Formula signature real
      (relationSort relationOrder 0 :: classSort classOrder 0 :: [])
      conditionOrder) :
    star_123_01_matrix relationExistential negation disjunction
        progression domainIdentity =
      .sometimes relationExistential
        (conjunction negation disjunction progression domainIdentity) := rfl

/-- ✱123·01: `ℵ₀` is the eliminable class of domains of progressions. -/
def star_123_01
    (vocabulary : Star123DefinitionVocabulary signature classOrder
      relationOrder conditionOrder scopeOrder)
    (relationExistential : ExistentialVocabulary signature
      (relationSort relationOrder 0) conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (progression domainIdentity : Formula signature real
      (relationSort relationOrder 0 :: classSort classOrder 0 :: [])
      conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0]
        (bindOrder conditionOrder (relationSort relationOrder 0)) 0]
      scopeOrder) :
    Formula signature real []
      (bindOrder
        (max
          (bindOrder
            (bindOrder conditionOrder (relationSort relationOrder 0))
            (classSort classOrder 0))
          scopeOrder)
        (.function [classSort classOrder 0]
          (bindOrder conditionOrder (relationSort relationOrder 0)) 0)) :=
  .sometimes vocabulary.classExistential
    (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.always vocabulary.classUniversal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          ((star_123_01_matrix relationExistential negation disjunction
            progression domainIdentity).rename
              (liftRenaming (fun v => .succ v)))))
      continuation)

theorem star_123_01_unfold
    (vocabulary : Star123DefinitionVocabulary signature classOrder
      relationOrder conditionOrder scopeOrder)
    (relationExistential : ExistentialVocabulary signature
      (relationSort relationOrder 0) conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (progression domainIdentity : Formula signature real
      (relationSort relationOrder 0 :: classSort classOrder 0 :: [])
      conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0]
        (bindOrder conditionOrder (relationSort relationOrder 0)) 0]
      scopeOrder) :
    star_123_01 vocabulary relationExistential negation disjunction
        progression domainIdentity continuation =
      .sometimes vocabulary.classExistential
        (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
          vocabulary.outerNegation vocabulary.conjunctionDisjunction
          (.always vocabulary.classUniversal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              ((star_123_01_matrix relationExistential negation disjunction
                progression domainIdentity).rename
                  (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

def star_123_01_reading
    (vocabulary : Star123DefinitionVocabulary signature classOrder
      relationOrder conditionOrder scopeOrder)
    (relationExistential : ExistentialVocabulary signature
      (relationSort relationOrder 0) conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (progression domainIdentity : Formula signature real
      (relationSort relationOrder 0 :: classSort classOrder 0 :: [])
      conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0]
        (bindOrder conditionOrder (relationSort relationOrder 0)) 0]
      scopeOrder) :
    ClaimReading signature real where
  printed := "✱123·01. ℵ₀=DʻʻProg Df"
  parsed := .assertion (star_123_01 vocabulary relationExistential negation
    disjunction progression domainIdentity continuation)

end PM.RamifiedSyntax
