import Principia.FirstEdition.Volume2.Star111Source
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Definitions of PM II, ✱111

The values defined at ✱111·01 and ✱111·02 are classes of correlations.
Accordingly they are represented contextually: the correlation is bound in
the defining matrix and the resulting predicative class is bound only in the
continuation.  No class-valued term is added to `Term`.
-/

/-- Logical vocabulary for the contextual correlation classes of ✱111. -/
structure Star111DefinitionVocabulary (signature : Signature)
    (correlationSort : RSort) (matrixOrder scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (.function [correlationSort] matrixOrder 0)
    (max (bindOrder matrixOrder correlationSort) scopeOrder)
  universal : signature.Universal correlationSort matrixOrder
  equivalenceNegation : signature.Negation matrixOrder
  equivalenceDisjunction : signature.Disjunction matrixOrder
  leftNegation : signature.Negation
    (bindOrder matrixOrder correlationSort)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder matrixOrder correlationSort) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder matrixOrder correlationSort) scopeOrder)

/-- A unary contextual abstraction at an arbitrary ramified argument sort. -/
def star_111_correlationClass
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      matrixOrder scopeOrder)
    (matrix : Formula signature real [correlationSort] matrixOrder)
    (continuation : Formula signature real
      [.function [correlationSort] matrixOrder 0] scopeOrder) :
    Formula signature real []
      (bindOrder
        (max (bindOrder matrixOrder correlationSort) scopeOrder)
        (.function [correlationSort] matrixOrder 0)) :=
  .sometimes vocabulary.existential
    (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      (.always vocabulary.universal
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
          (matrix.rename (liftRenaming (fun v => .succ v)))))
      continuation)

theorem star_111_correlationClass_unfold
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      matrixOrder scopeOrder)
    (matrix : Formula signature real [correlationSort] matrixOrder)
    (continuation : Formula signature real
      [.function [correlationSort] matrixOrder 0] scopeOrder) :
    star_111_correlationClass vocabulary matrix continuation =
      .sometimes vocabulary.existential
        (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
          vocabulary.outerNegation vocabulary.conjunctionDisjunction
          (.always vocabulary.universal
            (equivalence vocabulary.equivalenceNegation
              vocabulary.equivalenceDisjunction
              (applyUnary (.apparent (.succ .zero)) (.apparent .zero))
              (matrix.rename (liftRenaming (fun v => .succ v)))))
          continuation) := rfl

/-- The three displayed conditions on `T` in ✱111·01, associated to the
left exactly as the printed dotted conjunction. -/
def star_111_01_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (oneToOne mapsClasses carriesKappa :
      Formula signature real [correlationSort] order) :
    Formula signature real [correlationSort] order :=
  conjunction negation disjunction
    (conjunction negation disjunction oneToOne mapsClasses) carriesKappa

theorem star_111_01_matrix_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (oneToOne mapsClasses carriesKappa :
      Formula signature real [correlationSort] order) :
    star_111_01_matrix negation disjunction oneToOne mapsClasses carriesKappa =
      conjunction negation disjunction
        (conjunction negation disjunction oneToOne mapsClasses)
        carriesKappa := rfl

/-- ✱111·01.  `κ sm sm λ` is the eliminable class of correlations `T`
satisfying the three conditions printed on the right of the definition. -/
def star_111_01
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      order scopeOrder)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (oneToOne mapsClasses carriesKappa :
      Formula signature real [correlationSort] order)
    (continuation : Formula signature real
      [.function [correlationSort] order 0] scopeOrder) :=
  star_111_correlationClass vocabulary
    (star_111_01_matrix matrixNegation matrixDisjunction
      oneToOne mapsClasses carriesKappa)
    continuation

theorem star_111_01_unfold
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      order scopeOrder)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (oneToOne mapsClasses carriesKappa :
      Formula signature real [correlationSort] order)
    (continuation : Formula signature real
      [.function [correlationSort] order 0] scopeOrder) :
    star_111_01 vocabulary matrixNegation matrixDisjunction
        oneToOne mapsClasses carriesKappa continuation =
      star_111_correlationClass vocabulary
        (star_111_01_matrix matrixNegation matrixDisjunction
          oneToOne mapsClasses carriesKappa)
        continuation := rfl

/-- Exact diplomatic reading linked to the contextual AST of ✱111·01. -/
def star_111_01_reading
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      order scopeOrder)
    (matrixNegation : signature.Negation order)
    (matrixDisjunction : signature.Disjunction order)
    (oneToOne mapsClasses carriesKappa :
      Formula signature real [correlationSort] order)
    (continuation : Formula signature real
      [.function [correlationSort] order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱111·01. κ sm sm λ=(1→1)∩α̂Ŝα∩T̂(κ=T̆ʻλ) Df"
  parsed := .assertion (star_111_01 vocabulary matrixNegation
    matrixDisjunction oneToOne mapsClasses carriesKappa continuation)

/-- ✱111·02.  The correspondence class unfolds to the supplied exact
membership matrix for `(Sʻβ) sm β`. -/
def star_111_02
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      order scopeOrder)
    (similarityMatrix : Formula signature real [correlationSort] order)
    (continuation : Formula signature real
      [.function [correlationSort] order 0] scopeOrder) :=
  star_111_correlationClass vocabulary similarityMatrix continuation

theorem star_111_02_unfold
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      order scopeOrder)
    (similarityMatrix : Formula signature real [correlationSort] order)
    (continuation : Formula signature real
      [.function [correlationSort] order 0] scopeOrder) :
    star_111_02 vocabulary similarityMatrix continuation =
      star_111_correlationClass vocabulary similarityMatrix continuation := rfl

/-- Exact diplomatic reading linked to the contextual AST of ✱111·02. -/
def star_111_02_reading
    (vocabulary : Star111DefinitionVocabulary signature correlationSort
      order scopeOrder)
    (similarityMatrix : Formula signature real [correlationSort] order)
    (continuation : Formula signature real
      [.function [correlationSort] order 0] scopeOrder) :
    ClaimReading signature real where
  printed := "✱111·02. Crp(S)ʻβ=(Sʻβ) sm β Df"
  parsed := .assertion
    (star_111_02 vocabulary similarityMatrix continuation)

end PM.RamifiedSyntax
