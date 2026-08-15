import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star23Derived
import Principia.FirstEdition.Volume1.Star24Source

namespace PM.RamifiedSyntax

/-!
# Derived declarations of PM I, ✱24

The universal class and class existence are eliminable contextual
abbreviations.  The asserted definitional equivalence ✱24·5 and the
existence-transport proposition ✱24·58 are derived in the ramified judgement.
The null class remains nested contextual notation: it cannot be manufactured
as a standalone class-valued term.
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

theorem star_24_01_unfold
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
      scopeOrder) :
    star_24_01 identity existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction continuation =
      star_20_01 existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction
        (star_13_01 identity (.apparent .zero) (.apparent .zero))
        continuation := rfl

/-! ### ✱24·02 — Null class (definition, fully expanded)

After eliminating ✱22·04 and ✱24·01, the membership matrix of `Λ = −V`
is the negation of the identity matrix.  The class abstraction remains a
contextual ✱20·01 abbreviation, just as it does for ✱24·01.
-/

def star_24_02
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
    (.neg equivalenceNegation
      (star_13_01 identity (.apparent .zero) (.apparent .zero)))
    continuation

theorem star_24_02_unfold
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
      scopeOrder) :
    star_24_02 identity existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction continuation =
      star_20_01 existential universal equivalenceNegation
        equivalenceDisjunction leftNegation rightNegation outerNegation
        conjunctionDisjunction
        (.neg equivalenceNegation
          (star_13_01 identity (.apparent .zero) (.apparent .zero)))
        continuation := rfl

/-- ✱24·03: class existence is existential membership. -/
def star_24_03
    (existential : ExistentialVocabulary signature .individual order)
    (membership : Formula signature real [.individual] order) :
    Formula signature real [] (bindOrder order .individual) :=
  .sometimes existential membership

theorem star_24_03_unfold
    (existential : ExistentialVocabulary signature .individual order)
    (membership : Formula signature real [.individual] order) :
    star_24_03 existential membership = .sometimes existential membership := rfl

/-- Audited scope reading of ✱24·5. -/
def star_24_5_reading
    (existential : ExistentialVocabulary signature .individual order)
    (membership : Formula signature real [.individual] order)
    (negation : signature.Negation (bindOrder order .individual))
    (disjunction : signature.Disjunction (bindOrder order .individual)) :
    ClaimReading signature real where
  printed := "✱24·5. ⊢:∃!α.≡.(∃ x).x ∈ α [✱4·2.(✱24·03)]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_24_03 existential membership)
    (.sometimes existential membership))

/-- ✱24·5, following PM's printed `[✱4·2.(✱24·03)]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_24_5
    (existential : ExistentialVocabulary signature .individual order)
    (membership : Formula signature real [.individual] order)
    (negation : signature.Negation (bindOrder order .individual))
    (disjunction : signature.Disjunction (bindOrder order .individual)) :
    Derivation (star_24_5_reading existential membership negation disjunction).parsed := by
  have line1 := star_24_03_unfold existential membership
  change Derivation (.assertion (star_4_01 negation disjunction
    (star_24_03 existential membership) (.sometimes existential membership)))
  rw [line1]
  have line2 := star_4_2 negation disjunction (.sometimes existential membership)
  exact line2

/-- The `α` membership matrix printed on the left of ✱24·58. -/
def star_24_58_leftMatrix
    (alpha : Term signature real [] (classSort 0 0)) :
    Formula signature real [.individual] 0 :=
  star_20_02 alpha.weaken (.apparent .zero)

/-- The independently constructed `β` membership matrix printed on the
right of ✱24·58. -/
def star_24_58_rightMatrix
    (beta : Term signature real [] (classSort 0 0)) :
    Formula signature real [.individual] 0 :=
  star_20_02 beta.weaken (.apparent .zero)

/-- Audited scope reading of ✱24·58. -/
def star_24_58_reading
    (existential0 : ExistentialVocabulary signature .individual 0)
    (existential1 : ExistentialVocabulary signature .individual
      (bindOrder 0 .individual))
    (universal2 : signature.Universal .individual
      (bindOrder (bindOrder 0 .individual) .individual))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (alpha beta : Term signature real [] (classSort 0 0)) :
    ClaimReading signature real where
  printed := "✱24·58. ⊢:.α⊃β.⊃:∃!α.⊃.∃!β [✱10·28]"
  parsed := (star_10_28_reading existential0 existential1 universal2
    negation0 disjunction0 (star_24_58_leftMatrix alpha)
    (star_24_58_rightMatrix beta)).parsed

/-- ✱24·58, exactly the printed ✱10·28 instance for the independently
constructed membership matrices of `α` and `β`.
`demonstration_provenance: follows-printed`. -/
theorem star_24_58
    (existential0 : ExistentialVocabulary signature .individual 0)
    (existential1 : ExistentialVocabulary signature .individual
      (bindOrder 0 .individual))
    (universal2 : signature.Universal .individual
      (bindOrder (bindOrder 0 .individual) .individual))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (disjunction01 : signature.Disjunction
      (max 0 (bindOrder 0 .individual)))
    (negation1 : signature.Negation (bindOrder 0 .individual))
    (disjunction12 : signature.Disjunction
      (max (bindOrder 0 .individual)
        (bindOrder (bindOrder 0 .individual) .individual)))
    (alpha beta : Term signature real [] (classSort 0 0)) :
    Derivation (star_24_58_reading existential0 existential1 universal2
      negation0 disjunction0 alpha beta).parsed := by
  have line1 := star_10_28 existential0 existential1 universal2 negation0
    disjunction0 disjunction01 negation1 disjunction12
    (star_24_58_leftMatrix alpha) (star_24_58_rightMatrix beta)
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_24_5
#print axioms PM.RamifiedSyntax.star_24_01_unfold
#print axioms PM.RamifiedSyntax.star_24_02_unfold
#print axioms PM.RamifiedSyntax.star_24_03_unfold
#print axioms PM.RamifiedSyntax.star_24_58
