import Principia.Experimental.RamifiedToy

namespace PM.Experimental.TypicalAmbiguityToy

/-!
# Minimal test of typical ambiguity

This module is an isolated architecture test, not an edition of a numbered PM
proposition.  `classSchema` is one type-schematic object-language formula.  Its
parameter is the reified PM sort `RamifiedSort`, rather than a Lean universe
parameter.  The two instances below therefore exercise PM type variation
inside the deep embedding.

The example deliberately does not claim that PM's convention of typical
ambiguity has already been reconstructed in full.  It tests the minimum
invariant needed before the class calculus is industrialised: one declaration
can be instantiated at genuinely distinct PM types, while object-language
substitution remains sort preserving.
-/

open PM.Experimental.RamifiedToy

/-- A class predicate is indexed by the reified PM sort of its members. -/
inductive ClassSymbol : RamifiedSort → Type where
  | membership (memberSort : RamifiedSort) :
      ClassSymbol (.function [memberSort] 0 0)

inductive ClassNegation : Nat → Type where
  | order0 : ClassNegation 0

inductive ClassDisjunction : Nat → Nat → Type where
  | order00 : ClassDisjunction 0 0

def classSignature : Signature where
  Symbol := ClassSymbol
  NegationMeaning := ClassNegation
  DisjunctionMeaning := ClassDisjunction

/-- The single class proposition schema.  Its free apparent variable and its
class symbol carry the same explicit PM sort. -/
def classSchema (memberSort : RamifiedSort) :
    Formula classSignature [] [memberSort] 0 :=
  .apply (.symbol (.membership memberSort))
    (.cons (.apparent .zero) .nil)

/-- Close the one schema at any reified PM type. -/
def closedClassSchema (memberSort : RamifiedSort) :
    Formula classSignature [] [] (bindOrder 0 memberSort) :=
  .always (classSchema memberSort)

/-- First instance: classes of individuals. -/
def individualClassInstance :
    Formula classSignature [] [] (bindOrder 0 individualSort) :=
  closedClassSchema individualSort

/-- Second instance of the very same declaration: classes whose members are
predicative unary functions of individuals. -/
def predicativeFunctionClassInstance :
    Formula classSignature [] [] (bindOrder 0 predicateSort) :=
  closedClassSchema predicateSort

/-- An object-language instance consumes only a term of the schema's exact
reified PM sort.  Thus Lean cannot pass a predicate term to the individual
instance (or conversely) without first manufacturing a false sort equality. -/
def instantiateClassSchema {memberSort : RamifiedSort}
    (member : Term classSignature [] [] memberSort) :
    Formula classSignature [] [] 0 :=
  (classSchema memberSort).instantiate member

/-- The two PM sorts used above are definitionally different constructors.
This is the negative substitution test: a proposed cross-type instantiation
would require an inhabitant of this refuted equality. -/
theorem noIndividualPredicateSortIdentification :
    individualSort ≠ predicateSort := by
  intro equality
  cases equality

end PM.Experimental.TypicalAmbiguityToy
