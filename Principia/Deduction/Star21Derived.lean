import Principia.FirstEdition.Volume1.Star21Source
import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star10Derived
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱21 -/

/-- ✱21·07: quantification over relations is quantification over
predicative two-place functions. -/
def star_21_07
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (relationSort resultOrder 0)) :=
  .always universal body

theorem star_21_07_unfold
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    star_21_07 universal body = .always universal body := rfl

/-- ✱21·071: existential relation quantification has the same predicative
two-place-function expansion as ✱21·07. -/
def star_21_071
    (existential : ExistentialVocabulary signature
      (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    Formula signature real apparent
      (bindOrder scopeOrder (relationSort resultOrder 0)) :=
  .sometimes existential body

theorem star_21_071_unfold
    (existential : ExistentialVocabulary signature
      (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real
      (relationSort resultOrder 0 :: apparent) scopeOrder) :
    star_21_071 existential body = .sometimes existential body := rfl

/-- Audited catalogue reading of ✱21·1.  The apparent relation on the left
is eliminated by ✱21·01, so both sides parse as its existential expansion. -/
def star_21_1_reading
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (continuation : Formula signature real
      [relationSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "⊢ : f{ẑxẑyψ(x,y)} .≡ : (∃φ) : φ!(x,y) .≡₍x,y₎. ψ(x,y) : f{φ!(ẑu,ẑv)}"
  parsed := .assertion (star_4_01 finalNegation finalDisjunction
    (star_21_01 existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
    (star_21_01 existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation))

/-- ✱21·1, following PM's printed `[✱4·2.(✱21·01)]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_21_1
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (leftUniversal : signature.Universal .individual resultOrder)
    (rightUniversal : signature.Universal .individual
      (bindOrder resultOrder .individual))
    (equivalenceNegation : signature.Negation resultOrder)
    (equivalenceDisjunction : signature.Disjunction resultOrder)
    (leftNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (rightNegation : signature.Negation scopeOrder)
    (outerNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (conjunctionDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        scopeOrder))
    (finalNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (finalDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          scopeOrder)
        (relationSort resultOrder 0)))
    (matrix : Formula signature real [.individual, .individual] resultOrder)
    (continuation : Formula signature real
      [relationSort resultOrder 0] scopeOrder) :
    Derivation (star_21_1_reading existential leftUniversal rightUniversal
      equivalenceNegation equivalenceDisjunction leftNegation rightNegation
      outerNegation conjunctionDisjunction finalNegation finalDisjunction
      matrix continuation).parsed := by
  have line1 := star_21_01_unfold existential leftUniversal rightUniversal
    equivalenceNegation equivalenceDisjunction leftNegation rightNegation
    outerNegation conjunctionDisjunction matrix continuation
  have line2 := star_4_2 finalNegation finalDisjunction
    (star_21_01 existential leftUniversal rightUniversal equivalenceNegation
      equivalenceDisjunction leftNegation rightNegation outerNegation
      conjunctionDisjunction matrix continuation)
  rw [line1] at line2
  exact line2

/-- Audited catalogue reading of ✱21·6. -/
def star_21_6_reading
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (body : Formula signature real [relationSort resultOrder 0] matrixOrder) :
    ClaimReading signature real where
  printed := "⊢ : (∃R). fR .≡ . ∼{(R). ∼fR}"
  parsed := .assertion (star_4_01 equivalenceNegation equivalenceDisjunction
    (star_21_071 existential body)
    (.neg existential.outerNegation
      (star_21_07 existential.universal
        (.neg existential.matrixNegation body))))

/-- ✱21·6, following the printed instruction `[Proof as in ✱20·6]`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_6
    (existential : ExistentialVocabulary signature (relationSort resultOrder 0)
      matrixOrder)
    (equivalenceNegation : signature.Negation
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder matrixOrder (relationSort resultOrder 0)))
    (body : Formula signature real [relationSort resultOrder 0] matrixOrder) :
    Derivation (star_21_6_reading existential equivalenceNegation
      equivalenceDisjunction body).parsed := by
  have line1 := star_4_2 equivalenceNegation equivalenceDisjunction
    (star_21_071 existential body)
  have line2 : star_21_071 existential body =
      .neg existential.outerNegation
        (.always existential.universal
          (.neg existential.matrixNegation body)) :=
    star_10_01_unfold existential body
  have line3 := star_21_07_unfold existential.universal
    (.neg existential.matrixNegation body)
  exact Derivation.castAssertion
    (congrArg
      (star_4_01 equivalenceNegation equivalenceDisjunction
        (star_21_071 existential body))
      (Eq.trans line2
        (congrArg
          (fun formula => Formula.neg existential.outerNegation formula)
          line3).symm))
    line1

/-- Audited catalogue reading of ✱21·61. -/
def star_21_61_reading
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (relationSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder)
    (relation : Term signature real [] (relationSort resultOrder 0)) :
    ClaimReading signature real where
  printed := "⊢ : (R). fR .⊃ . fS"
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal body) (body.instantiate relation))

/-- ✱21·61, following the proof of ✱20·61 via ✱10·1.
`demonstration_provenance: follows-printed`. -/
theorem star_21_61
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (negation : signature.Negation
      (bindOrder scopeOrder (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder scopeOrder (relationSort resultOrder 0)) scopeOrder))
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder)
    (relation : Term signature real [] (relationSort resultOrder 0)) :
    Derivation
      (star_21_61_reading universal negation disjunction body relation).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction body relation
  exact line1

/-- Audited catalogue reading of the metalinguistic rule ✱21·62. -/
def star_21_62_reading
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "When fR is true, whatever possible argument of the form ẑxẑyφ!(x,y) R may be, (R). fR is true."
  parsed := .assertion (.always universal body)

/-- ✱21·62, following PM's reference to the proof of ✱20·62 via ✱10·11.
The premise is legitimate because PM states ✱21·62 as a rule, not with `⊢`.
`demonstration_provenance: follows-printed`. -/
theorem star_21_62
    (universal : signature.Universal (relationSort resultOrder 0) scopeOrder)
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder)
    (line1 : Derivation (.assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (relationSort resultOrder 0 :: real)
          (relationSort resultOrder 0)))))) :
    Derivation (star_21_62_reading universal body).parsed := by
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/-- Audited catalogue reading of ✱21·63. -/
def star_21_63_reading
    (universal : signature.Universal (relationSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (relationSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [relationSort resultOrder 0] 0) :
    ClaimReading signature real where
  printed := "⊢ : (R). p ∨ fR .⊃ : p .∨ . (R). fR"
  parsed := .assertion (implication negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body))
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) body)))

/-- ✱21·63, following the proof of ✱20·63 via ✱10·12.
`demonstration_provenance: follows-printed`. -/
theorem star_21_63
    (universal : signature.Universal (relationSort resultOrder 0) 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation
      (bindOrder 0 (relationSort resultOrder 0)))
    (disjunction : signature.Disjunction
      (bindOrder 0 (relationSort resultOrder 0)))
    (p : Formula signature real [] 0)
    (body : Formula signature real [relationSort resultOrder 0] 0) :
    Derivation (star_21_63_reading universal matrixDisjunction negation
      disjunction p body).parsed := by
  have line1 := star_10_12 universal matrixDisjunction negation disjunction p body
  exact line1

/-- Audited catalogue reading of ✱21·631. -/
def star_21_631_reading
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "If \"fR\" is significant, then if S is of the same type as R, \"fS\" is significant, and vice versa."
  parsed := .significance body

/-- ✱21·631, following PM's reference to the proof of ✱20·631.
`demonstration_provenance: follows-printed`. -/
theorem star_21_631
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    Derivation (star_21_631_reading body).parsed := by
  have line1 := Derivation.star_10_121 body
  exact line1

/-- Audited catalogue reading of ✱21·632. -/
def star_21_632_reading
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    ClaimReading signature real where
  printed := "If, for some R, there is a proposition fR, then there is a function fR̂, and vice versa."
  parsed := .functionExistence body

/-- ✱21·632, following PM's reference to the proof of ✱20·632.
`demonstration_provenance: follows-printed`. -/
theorem star_21_632
    (body : Formula signature real [relationSort resultOrder 0] scopeOrder) :
    Derivation (star_21_632_reading body).parsed := by
  have line1 := Derivation.star_10_122 body
  exact line1

/-- Audited catalogue reading of ✱21·633. -/
def star_21_633_reading
    (leftInner : signature.Universal (relationSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (relationSort rightOrder 0)
      (bindOrder matrixOrder (relationSort leftOrder 0)))
    (rightInner : signature.Universal (relationSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (relationSort leftOrder 0)
      (bindOrder matrixOrder (relationSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
        (relationSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
          (relationSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (relationSort rightOrder 0))
          (relationSort leftOrder 0))))
    (body : Formula signature real
      [relationSort leftOrder 0, relationSort rightOrder 0] matrixOrder) :
    ClaimReading signature real where
  printed := "\"Whatever possible relation R may be, f(R,S) is true whatever possible relation S may be\" implies \"whatever possible relation S may be, f(R,S) is true whatever possible relation R may be.\""
  parsed := .assertion (star_11_07_formula leftInner rightOuter rightInner
    leftOuter negation disjunction body)

/-- ✱21·633, following PM's reference to the proof of ✱20·633.
`demonstration_provenance: follows-printed`. -/
theorem star_21_633
    (leftInner : signature.Universal (relationSort leftOrder 0) matrixOrder)
    (rightOuter : signature.Universal (relationSort rightOrder 0)
      (bindOrder matrixOrder (relationSort leftOrder 0)))
    (rightInner : signature.Universal (relationSort rightOrder 0) matrixOrder)
    (leftOuter : signature.Universal (relationSort leftOrder 0)
      (bindOrder matrixOrder (relationSort rightOrder 0)))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
        (relationSort rightOrder 0)))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder (relationSort leftOrder 0))
          (relationSort rightOrder 0))
        (bindOrder (bindOrder matrixOrder (relationSort rightOrder 0))
          (relationSort leftOrder 0))))
    (body : Formula signature real
      [relationSort leftOrder 0, relationSort rightOrder 0] matrixOrder) :
    Derivation (star_21_633_reading leftInner rightOuter rightInner leftOuter
      negation disjunction body).parsed := by
  have line1 := Derivation.star_11_07 leftInner rightOuter rightInner leftOuter
    negation disjunction body
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_21_61
#print axioms PM.RamifiedSyntax.star_21_62
#print axioms PM.RamifiedSyntax.star_21_63
#print axioms PM.RamifiedSyntax.star_21_631
#print axioms PM.RamifiedSyntax.star_21_632
#print axioms PM.RamifiedSyntax.star_21_633
#print axioms PM.RamifiedSyntax.star_21_1
#print axioms PM.RamifiedSyntax.star_21_6
#print axioms PM.RamifiedSyntax.star_21_07_unfold
#print axioms PM.RamifiedSyntax.star_21_071_unfold
