import Principia.FirstEdition.Volume1.Star62Source
import Principia.Syntax.Printed
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-- T4 reading specialized to the ramified claims of ✱62. -/
structure Star62Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-!
# Derived propositions of PM I, ✱62

The relation `ε` introduced at ✱62·01 is an incomplete relation symbol.  Its
right argument is a class, not an individual, so the abstraction below keeps
the two binder sorts independent.  Nothing below turns the class argument
into a class-valued Lean object.
-/

/-- Vocabulary for the contextual definition ✱62·01 at its independently
assigned ramified orders. -/
structure Star62DefinitionVocabulary (signature : Signature) (order excess
    scopeOrder : Nat) where
  existential : ExistentialVocabulary signature
    (.function [.individual, classSort order excess] order 0)
    (max
      (bindOrder (bindOrder order .individual) (classSort order excess))
      scopeOrder)
  leftUniversal : signature.Universal .individual order
  rightUniversal : signature.Universal (classSort order excess)
    (bindOrder order .individual)
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation
    (bindOrder (bindOrder order .individual) (classSort order excess))
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max
      (bindOrder (bindOrder order .individual) (classSort order excess))
      scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max
      (bindOrder (bindOrder order .individual) (classSort order excess))
      scopeOrder)

/-- The definiens `x ε α` of ✱62·01, with `x` and `α` still apparent. -/
def star_62_01_matrix :
    Formula signature real [.individual, classSort order excess] order :=
  membership (.apparent .zero) (.apparent (.succ .zero))

/-- The membership matrix of ✱62·01 is itself eliminable application syntax. -/
theorem star_62_01_matrix_unfold :
    (star_62_01_matrix :
      Formula signature real [.individual, classSort order excess] order) =
      membership (.apparent .zero) (.apparent (.succ .zero)) := rfl

/-- ✱62·01: `ε = ẑxα(x ε α)` as a contextual, heterogeneous relation
abstraction. -/
def star_62_01
    (vocabulary : Star62DefinitionVocabulary signature order excess scopeOrder)
    (continuation : Formula signature real
      [.function [.individual, classSort order excess] order 0] scopeOrder) :
    Formula signature real []
      (bindOrder
        (max
          (bindOrder (bindOrder order .individual) (classSort order excess))
          scopeOrder)
        (.function [.individual, classSort order excess] order 0)) :=
  Formula.sometimes vocabulary.existential
    (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
      vocabulary.outerNegation vocabulary.conjunctionDisjunction
      ((equivalence vocabulary.equivalenceNegation
        vocabulary.equivalenceDisjunction
        (applyBinary (.apparent (.succ (.succ .zero)))
          (.apparent .zero) (.apparent (.succ .zero)))
        (star_62_01_matrix.rename
          (liftRenamingN [.individual, classSort order excess]
            (fun v => .succ v)))).always₂
              vocabulary.leftUniversal vocabulary.rightUniversal)
      continuation)

/-- The full eliminable expansion printed at ✱62·01. -/
theorem star_62_01_unfold
    (vocabulary : Star62DefinitionVocabulary signature order excess scopeOrder)
    (continuation : Formula signature real
      [.function [.individual, classSort order excess] order 0] scopeOrder) :
    star_62_01 vocabulary continuation =
      Formula.sometimes vocabulary.existential
        (mixedConjunction vocabulary.leftNegation vocabulary.rightNegation
          vocabulary.outerNegation vocabulary.conjunctionDisjunction
          ((equivalence vocabulary.equivalenceNegation
            vocabulary.equivalenceDisjunction
            (applyBinary (.apparent (.succ (.succ .zero)))
              (.apparent .zero) (.apparent (.succ .zero)))
            (star_62_01_matrix.rename
              (liftRenamingN [.individual, classSort order excess]
                (fun v => .succ v)))).always₂
                  vocabulary.leftUniversal vocabulary.rightUniversal)
          continuation) := rfl

/-- The object formula printed at ✱62·1 after expanding ✱62·01 in the scope
of its displayed equivalence. -/
def star_62_1_formula
    (vocabulary : Star62DefinitionVocabulary signature order excess order)
    (x : Term signature real [] .individual)
    (alpha : Term signature real [] (classSort order excess)) :
    Formula signature real []
      (bindOrder
        (max
          (bindOrder (bindOrder order .individual) (classSort order excess))
          order)
        (.function [.individual, classSort order excess] order 0)) :=
  star_62_01 vocabulary
    (equivalence vocabulary.equivalenceNegation
      vocabulary.equivalenceDisjunction
      (applyBinary (.apparent .zero) x.weaken alpha.weaken)
      ((star_62_01_matrix.instantiate₂ x alpha).rename
        (emptyRenaming (target :=
          [.function [.individual, classSort order excess] order 0]))))

/-- The expansion of the whole ✱62·1 scope.  In particular its root is the
existential relation-abstraction expansion, not the reflexive equivalence
`x ε α ≡ x ε α` taken in isolation. -/
theorem star_62_1_formula_unfold
    (vocabulary : Star62DefinitionVocabulary signature order excess order)
    (x : Term signature real [] .individual)
    (alpha : Term signature real [] (classSort order excess)) :
    star_62_1_formula vocabulary x alpha =
      star_62_01 vocabulary
        (equivalence vocabulary.equivalenceNegation
          vocabulary.equivalenceDisjunction
          (applyBinary (.apparent .zero) x.weaken alpha.weaken)
          ((star_62_01_matrix.instantiate₂ x alpha).rename
            (emptyRenaming (target :=
              [.function [.individual, classSort order excess] order 0])))) := rfl

/-- Audited scope reading of ✱62·1. -/
def star_62_1_reading
    (vocabulary : Star62DefinitionVocabulary signature order excess order)
    (x : Term signature real [] .individual)
    (alpha : Term signature real [] (classSort order excess)) :
    Star62Reading signature real where
  printed := PM.pmPrinted
    "✱62·1.  ⊢ : x ε α .≡ . x ε α  [✱21·3.(✱62·01)]"
  parsed := .assertion (star_62_1_formula vocabulary x alpha)
  scopeReading := "The relation abstraction of ✱62·01 has the scope of the displayed equivalence; its right argument has the class sort of α."

/-!
No theorem `star_62_1` is declared here.  The printed route is ✱21·3, whose
heterogeneous implementation requires the still-unproved ✱10·35 scope
bridge.  Adding that premise would make ✱62·1 a conditional result; replacing
`star_62_1_formula` by its right member would instead collapse the outer
`sometimes` tree and reproduce the forbidden reflexivity shortcut.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_62_01_unfold
#print axioms PM.RamifiedSyntax.star_62_01_matrix_unfold
#print axioms PM.RamifiedSyntax.star_62_1_formula_unfold
