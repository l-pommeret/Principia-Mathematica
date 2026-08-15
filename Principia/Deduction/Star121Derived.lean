import Principia.FirstEdition.Volume2.Star121Source
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-! # Definitions of PM II, ✱121 -/

/-- Vocabulary for unary contextual abstractions used by the interval and
finite-distance-class definitions. -/
structure Star121UnaryDefinitionVocabulary (signature : Signature)
    (argumentSort : RSort) (matrixOrder scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (.function [argumentSort] matrixOrder 0)
    (max (bindOrder matrixOrder argumentSort) scopeOrder)
  universal : signature.Universal argumentSort matrixOrder
  equivalenceNegation : signature.Negation matrixOrder
  equivalenceDisjunction : signature.Disjunction matrixOrder
  leftNegation : signature.Negation (bindOrder matrixOrder argumentSort)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder matrixOrder argumentSort) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder matrixOrder argumentSort) scopeOrder)

def star_121_unaryDefinition
    (vocabulary : Star121UnaryDefinitionVocabulary signature argumentSort
      matrixOrder scopeOrder)
    (matrix : Formula signature real [argumentSort] matrixOrder)
    (continuation : Formula signature real
      [.function [argumentSort] matrixOrder 0] scopeOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder matrixOrder argumentSort) scopeOrder)
        (.function [argumentSort] matrixOrder 0)) :=
  .sometimes vocabulary.existential
    (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.always vocabulary.universal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      continuation)

theorem star_121_unaryDefinition_unfold
    (vocabulary : Star121UnaryDefinitionVocabulary signature argumentSort
      matrixOrder scopeOrder)
    (matrix : Formula signature real [argumentSort] matrixOrder)
    (continuation : Formula signature real
      [.function [argumentSort] matrixOrder 0] scopeOrder) :
    star_121_unaryDefinition vocabulary matrix continuation =
      .sometimes vocabulary.existential
        (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
          vocabulary.outerNegation vocabulary.conjunctionDisjunction
          (.always vocabulary.universal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (matrix.rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

/-- Vocabulary for the binary contextual relation abstraction at ✱121·02. -/
structure Star121BinaryDefinitionVocabulary (signature : Signature)
    (matrixOrder scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (relationSort matrixOrder 0)
    (max (bindOrder (bindOrder matrixOrder .individual) .individual)
      scopeOrder)
  leftUniversal : signature.Universal .individual matrixOrder
  rightUniversal : signature.Universal .individual
    (bindOrder matrixOrder .individual)
  equivalenceNegation : signature.Negation matrixOrder
  equivalenceDisjunction : signature.Disjunction matrixOrder
  leftNegation : signature.Negation
    (bindOrder (bindOrder matrixOrder .individual) .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder (bindOrder matrixOrder .individual) .individual)
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder (bindOrder matrixOrder .individual) .individual)
      scopeOrder)

def star_121_binaryDefinition
    (vocabulary : Star121BinaryDefinitionVocabulary signature matrixOrder
      scopeOrder)
    (matrix : Formula signature real [.individual, .individual] matrixOrder)
    (continuation : Formula signature real
      [relationSort matrixOrder 0] scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction matrix continuation

theorem star_121_binaryDefinition_unfold
    (vocabulary : Star121BinaryDefinitionVocabulary signature matrixOrder
      scopeOrder)
    (matrix : Formula signature real [.individual, .individual] matrixOrder)
    (continuation : Formula signature real
      [relationSort matrixOrder 0] scopeOrder) :
    star_121_binaryDefinition vocabulary matrix continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction matrix continuation := rfl

/-- Common matrix of the four interval definitions: the two displayed
relation memberships joined in their printed order. -/
def star_121_intervalMatrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order) :
    Formula signature real [.individual] order :=
  conjunction negation disjunction left right

theorem star_121_intervalMatrix_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order) :
    star_121_intervalMatrix negation disjunction left right =
      conjunction negation disjunction left right := rfl

/-- ✱121·01: open interval. -/
def star_121_01
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_121_unaryDefinition vocabulary
    (star_121_intervalMatrix negation disjunction left right) continuation

theorem star_121_01_unfold
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_121_01 vocabulary negation disjunction left right continuation =
      star_121_unaryDefinition vocabulary
        (star_121_intervalMatrix negation disjunction left right)
        continuation := rfl

def star_121_01_reading
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱121·01. P(x−y)=P⃖poʻx∩P⃗poʻy Df"
  parsed := .assertion
    (star_121_01 vocabulary negation disjunction left right continuation)

/-- ✱121·011: interval closed at the right endpoint. -/
def star_121_011
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_121_unaryDefinition vocabulary
    (star_121_intervalMatrix negation disjunction left right) continuation

theorem star_121_011_unfold
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_121_011 vocabulary negation disjunction left right continuation =
      star_121_unaryDefinition vocabulary
        (star_121_intervalMatrix negation disjunction left right)
        continuation := rfl

def star_121_011_reading
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱121·011. P(x⊣y)=P⃖poʻx∩P⃗∗ʻy Df"
  parsed := .assertion
    (star_121_011 vocabulary negation disjunction left right continuation)

/-- ✱121·012: interval closed at the left endpoint. -/
def star_121_012
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_121_unaryDefinition vocabulary
    (star_121_intervalMatrix negation disjunction left right) continuation

theorem star_121_012_unfold
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_121_012 vocabulary negation disjunction left right continuation =
      star_121_unaryDefinition vocabulary
        (star_121_intervalMatrix negation disjunction left right)
        continuation := rfl

def star_121_012_reading
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱121·012. P(x⟝y)=P⃖∗ʻx∩P⃗poʻy Df"
  parsed := .assertion
    (star_121_012 vocabulary negation disjunction left right continuation)

/-- ✱121·013: interval closed at both endpoints. -/
def star_121_013
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_121_unaryDefinition vocabulary
    (star_121_intervalMatrix negation disjunction left right) continuation

theorem star_121_013_unfold
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_121_013 vocabulary negation disjunction left right continuation =
      star_121_unaryDefinition vocabulary
        (star_121_intervalMatrix negation disjunction left right)
        continuation := rfl

def star_121_013_reading
    (vocabulary : Star121UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱121·013. P(x⊢⊣y)=P⃖∗ʻx∩P⃗∗ʻy Df"
  parsed := .assertion
    (star_121_013 vocabulary negation disjunction left right continuation)

/-- ✱121·02: `P_ν` is the contextual binary relation whose matrix is the
printed cardinal identity `N₀cʻP(x⊢⊣y)=ν+_c1`. -/
def star_121_02
    (vocabulary : Star121BinaryDefinitionVocabulary signature order scopeOrder)
    (cardinalIdentity :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :=
  star_121_binaryDefinition vocabulary cardinalIdentity continuation

theorem star_121_02_unfold
    (vocabulary : Star121BinaryDefinitionVocabulary signature order scopeOrder)
    (cardinalIdentity :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    star_121_02 vocabulary cardinalIdentity continuation =
      star_121_binaryDefinition vocabulary cardinalIdentity continuation := rfl

def star_121_02_reading
    (vocabulary : Star121BinaryDefinitionVocabulary signature order scopeOrder)
    (cardinalIdentity :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱121·02. P_ν=x̂ŷ{N₀cʻP(x⊢⊣y)=ν+_c1} Df"
  parsed := .assertion
    (star_121_02 vocabulary cardinalIdentity continuation)

/-- The existential index matrix common to ✱121·03 and ✱121·031. -/
def star_121_finiteMatrix
    (existential : ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder) :
    Formula signature real [relationSort levelOrder 0]
      (bindOrder conditionOrder indexSort) :=
  .sometimes existential
    (conjunction negation disjunction admissible levelIdentity)

theorem star_121_finiteMatrix_unfold
    (existential : ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder) :
    star_121_finiteMatrix existential negation disjunction
        admissible levelIdentity =
      .sometimes existential
        (conjunction negation disjunction admissible levelIdentity) := rfl

/-- ✱121·03: the class of finite-distance levels. -/
def star_121_03
    (vocabulary : Star121UnaryDefinitionVocabulary signature
      (relationSort levelOrder 0) (bindOrder conditionOrder indexSort)
      scopeOrder)
    (indexExistential :
      ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder)
    (continuation : Formula signature real
      [.function [relationSort levelOrder 0]
        (bindOrder conditionOrder indexSort) 0] scopeOrder) :=
  star_121_unaryDefinition vocabulary
    (star_121_finiteMatrix indexExistential negation disjunction
      admissible levelIdentity)
    continuation

theorem star_121_03_unfold
    (vocabulary : Star121UnaryDefinitionVocabulary signature
      (relationSort levelOrder 0) (bindOrder conditionOrder indexSort)
      scopeOrder)
    (indexExistential :
      ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder)
    (continuation : Formula signature real
      [.function [relationSort levelOrder 0]
        (bindOrder conditionOrder indexSort) 0] scopeOrder) :
    star_121_03 vocabulary indexExistential negation disjunction
        admissible levelIdentity continuation =
      star_121_unaryDefinition vocabulary
        (star_121_finiteMatrix indexExistential negation disjunction
          admissible levelIdentity)
        continuation := rfl

def star_121_03_reading
    (vocabulary : Star121UnaryDefinitionVocabulary signature
      (relationSort levelOrder 0) (bindOrder conditionOrder indexSort)
      scopeOrder)
    (indexExistential :
      ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder)
    (continuation : Formula signature real
      [.function [relationSort levelOrder 0]
        (bindOrder conditionOrder indexSort) 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱121·03. finidʻP=R̂{(∃ν).ν∈NC induct−ιʻΛ.R=P_ν} Df"
  parsed := .assertion (star_121_03 vocabulary indexExistential negation
    disjunction admissible levelIdentity continuation)

/-- ✱121·031: the class of positive finite-distance levels.  The stricter
printed index class is the `admissible` matrix supplied here. -/
def star_121_031
    (vocabulary : Star121UnaryDefinitionVocabulary signature
      (relationSort levelOrder 0) (bindOrder conditionOrder indexSort)
      scopeOrder)
    (indexExistential :
      ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder)
    (continuation : Formula signature real
      [.function [relationSort levelOrder 0]
        (bindOrder conditionOrder indexSort) 0] scopeOrder) :=
  star_121_unaryDefinition vocabulary
    (star_121_finiteMatrix indexExistential negation disjunction
      admissible levelIdentity)
    continuation

theorem star_121_031_unfold
    (vocabulary : Star121UnaryDefinitionVocabulary signature
      (relationSort levelOrder 0) (bindOrder conditionOrder indexSort)
      scopeOrder)
    (indexExistential :
      ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder)
    (continuation : Formula signature real
      [.function [relationSort levelOrder 0]
        (bindOrder conditionOrder indexSort) 0] scopeOrder) :
    star_121_031 vocabulary indexExistential negation disjunction
        admissible levelIdentity continuation =
      star_121_unaryDefinition vocabulary
        (star_121_finiteMatrix indexExistential negation disjunction
          admissible levelIdentity)
        continuation := rfl

def star_121_031_reading
    (vocabulary : Star121UnaryDefinitionVocabulary signature
      (relationSort levelOrder 0) (bindOrder conditionOrder indexSort)
      scopeOrder)
    (indexExistential :
      ExistentialVocabulary signature indexSort conditionOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (admissible levelIdentity : Formula signature real
      (indexSort :: relationSort levelOrder 0 :: []) conditionOrder)
    (continuation : Formula signature real
      [.function [relationSort levelOrder 0]
        (bindOrder conditionOrder indexSort) 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱121·031. finʻP=R̂{(∃ν).ν∈NC induct−ιʻΛ−ιʻ0.R=P_ν} Df"
  parsed := .assertion (star_121_031 vocabulary indexExistential negation
    disjunction admissible levelIdentity continuation)

end PM.RamifiedSyntax
