import Principia.FirstEdition.Volume1.Star21Source
import Principia.Deduction.Star10Derived
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱21 -/

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
