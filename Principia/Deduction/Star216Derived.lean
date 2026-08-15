import Principia.SecondEdition.Volume2.Star216Source
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-! # Definitions of PM II, ✱216 -/

structure Star216UnaryDefinitionVocabulary (signature : Signature)
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

def star_216_unaryDefinition
    (vocabulary : Star216UnaryDefinitionVocabulary signature argumentSort
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

theorem star_216_unaryDefinition_unfold
    (vocabulary : Star216UnaryDefinitionVocabulary signature argumentSort
      matrixOrder scopeOrder)
    (matrix : Formula signature real [argumentSort] matrixOrder)
    (continuation : Formula signature real
      [.function [argumentSort] matrixOrder 0] scopeOrder) :
    star_216_unaryDefinition vocabulary matrix continuation =
      .sometimes vocabulary.existential
        (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
          vocabulary.outerNegation vocabulary.conjunctionDisjunction
          (.always vocabulary.universal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (matrix.rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

structure Star216BinaryDefinitionVocabulary (signature : Signature)
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

def star_216_binaryDefinition
    (vocabulary : Star216BinaryDefinitionVocabulary signature matrixOrder
      scopeOrder)
    (matrix : Formula signature real [.individual, .individual] matrixOrder)
    (continuation : Formula signature real
      [relationSort matrixOrder 0] scopeOrder) :=
  star_21_01 vocabulary.existential vocabulary.leftUniversal
    vocabulary.rightUniversal vocabulary.equivalenceNegation
    vocabulary.equivalenceDisjunction vocabulary.leftNegation
    vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction matrix continuation

theorem star_216_binaryDefinition_unfold
    (vocabulary : Star216BinaryDefinitionVocabulary signature matrixOrder
      scopeOrder)
    (matrix : Formula signature real [.individual, .individual] matrixOrder)
    (continuation : Formula signature real
      [relationSort matrixOrder 0] scopeOrder) :
    star_216_binaryDefinition vocabulary matrix continuation =
      star_21_01 vocabulary.existential vocabulary.leftUniversal
        vocabulary.rightUniversal vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction vocabulary.leftNegation
        vocabulary.rightNegation vocabulary.outerNegation
        vocabulary.conjunctionDisjunction matrix continuation := rfl

/-- ✱216·01: the derivative class, with the displayed limit-image expression
supplied as its exact point-membership matrix. -/
def star_216_01
    (vocabulary : Star216UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (limitMembership : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_216_unaryDefinition vocabulary limitMembership continuation

theorem star_216_01_unfold
    (vocabulary : Star216UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (limitMembership : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    star_216_01 vocabulary limitMembership continuation =
      star_216_unaryDefinition vocabulary limitMembership continuation := rfl

def star_216_01_reading
    (vocabulary : Star216UnaryDefinitionVocabulary signature .individual
      order scopeOrder)
    (limitMembership : Formula signature real [.individual] order)
    (continuation : Formula signature real [classSort order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱216·01. δₚʻα=ltₚʻʻCl exʻ(α∩CʻP) Df"
  parsed := .assertion
    (star_216_01 vocabulary limitMembership continuation)

/-- ✱216·02: the class of dense classes. -/
def star_216_02
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (densityCondition : Formula signature real [classSort classOrder 0]
      conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :=
  star_216_unaryDefinition vocabulary densityCondition continuation

theorem star_216_02_unfold
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (densityCondition : Formula signature real [classSort classOrder 0]
      conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :
    star_216_02 vocabulary densityCondition continuation =
      star_216_unaryDefinition vocabulary densityCondition continuation := rfl

def star_216_02_reading
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (densityCondition : Formula signature real [classSort classOrder 0]
      conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱216·02. denseʻP=α̂(α−→minₚʻα⊂δₚʻα) Df"
  parsed := .assertion
    (star_216_02 vocabulary densityCondition continuation)

/-- ✱216·03: the class of closed classes; the eligibility and derivative
inclusions remain separately visible in the AST. -/
def star_216_03
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (eligible derivativeIncluded : Formula signature real
      [classSort classOrder 0] conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :=
  star_216_unaryDefinition vocabulary
    (conjunction negation disjunction eligible derivativeIncluded)
    continuation

theorem star_216_03_unfold
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (eligible derivativeIncluded : Formula signature real
      [classSort classOrder 0] conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :
    star_216_03 vocabulary negation disjunction eligible
        derivativeIncluded continuation =
      star_216_unaryDefinition vocabulary
        (conjunction negation disjunction eligible derivativeIncluded)
        continuation := rfl

def star_216_03_reading
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (eligible derivativeIncluded : Formula signature real
      [classSort classOrder 0] conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱216·03. closedʻP=α̂{Cl exʻ(α∩CʻP)⊂ᗡʻlimaxₚ.δₚʻα⊂α} Df"
  parsed := .assertion (star_216_03 vocabulary negation disjunction
    eligible derivativeIncluded continuation)

/-- ✱216·04: pointwise intersection of the dense and closed classes. -/
def star_216_04
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (denseMembership closedMembership : Formula signature real
      [classSort classOrder 0] conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :=
  star_216_unaryDefinition vocabulary
    (conjunction negation disjunction denseMembership closedMembership)
    continuation

theorem star_216_04_unfold
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (denseMembership closedMembership : Formula signature real
      [classSort classOrder 0] conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :
    star_216_04 vocabulary negation disjunction denseMembership
        closedMembership continuation =
      star_216_unaryDefinition vocabulary
        (conjunction negation disjunction denseMembership closedMembership)
        continuation := rfl

def star_216_04_reading
    (vocabulary : Star216UnaryDefinitionVocabulary signature
      (classSort classOrder 0) conditionOrder scopeOrder)
    (negation : signature.Negation conditionOrder)
    (disjunction : signature.Disjunction conditionOrder)
    (denseMembership closedMembership : Formula signature real
      [classSort classOrder 0] conditionOrder)
    (continuation : Formula signature real
      [.function [classSort classOrder 0] conditionOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱216·04. perfʻP=denseʻP∩closedʻP Df"
  parsed := .assertion (star_216_04 vocabulary negation disjunction
    denseMembership closedMembership continuation)

/-- The restriction matrix of ✱216·05.  Both displayed domain memberships
from ✱216·6 are retained before the relation membership. -/
def star_216_05_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (leftInDomain rightInDomain relationMembership :
      Formula signature real [.individual, .individual] order) :
    Formula signature real [.individual, .individual] order :=
  conjunction negation disjunction
    (conjunction negation disjunction leftInDomain rightInDomain)
    relationMembership

theorem star_216_05_matrix_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (leftInDomain rightInDomain relationMembership :
      Formula signature real [.individual, .individual] order) :
    star_216_05_matrix negation disjunction leftInDomain rightInDomain
        relationMembership =
      conjunction negation disjunction
        (conjunction negation disjunction leftInDomain rightInDomain)
        relationMembership := rfl

/-- ✱216·05: `∇ʻP` is the contextual restriction of `P` to `Dʻltₚ`. -/
def star_216_05
    (vocabulary : Star216BinaryDefinitionVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (leftInDomain rightInDomain relationMembership :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :=
  star_216_binaryDefinition vocabulary
    (star_216_05_matrix negation disjunction leftInDomain rightInDomain
      relationMembership)
    continuation

theorem star_216_05_unfold
    (vocabulary : Star216BinaryDefinitionVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (leftInDomain rightInDomain relationMembership :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    star_216_05 vocabulary negation disjunction leftInDomain rightInDomain
        relationMembership continuation =
      star_216_binaryDefinition vocabulary
        (star_216_05_matrix negation disjunction leftInDomain rightInDomain
          relationMembership)
        continuation := rfl

def star_216_05_reading
    (vocabulary : Star216BinaryDefinitionVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (leftInDomain rightInDomain relationMembership :
      Formula signature real [.individual, .individual] order)
    (continuation : Formula signature real [relationSort order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱216·05. ∇ʻP=P↏Dʻltₚ Df"
  parsed := .assertion (star_216_05 vocabulary negation disjunction
    leftInDomain rightInDomain relationMembership continuation)

end PM.RamifiedSyntax
