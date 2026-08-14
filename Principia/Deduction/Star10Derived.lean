import Principia.Deduction.Star3Ramified
import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star9Derived

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱10 -/

private theorem detach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (line1 : ⊢ᵣ p)
    (line2 : ⊢ᵣ implication negation disjunction p q) :
    ⊢ᵣ q := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction line1 line2
  | cons head tail => exact Derivation.star_1_11_same negation disjunction line1 line2

/-- ✱10·1, restated as a theorem of the ramified deduction calculus. -/
theorem star_10_1
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Derivation
      (star_10_1_reading universal negation disjunction body value).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction body value
  exact line1

/-- Audited catalogue reading of ✱10·11. -/
def star_10_11_reading
    (universal : signature.Universal argument matrixOrder)
    (body : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "If φy is true whatever possible argument y may be, then (x).φx is true."
  parsed := .assertion (.always universal body)

/-- ✱10·11, with its printed metalinguistic premise represented explicitly. -/
theorem star_10_11
    (universal : signature.Universal argument matrixOrder)
    (body : Formula signature real [argument] matrixOrder)
    (line1 : Derivation (.assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument))))) :
    Derivation (star_10_11_reading universal body).parsed := by
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

/-- Audited catalogue reading of ✱10·121. -/
def star_10_121_reading
    (body : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "If “φx” is significant, then if a is of the same type as x, “φa” is\nsignificant, and vice versa.  [✱9·14]"
  parsed := .significance body

/-- ✱10·121, the primitive significance claim cited from ✱9·14. -/
theorem star_10_121
    (body : Formula signature real [argument] matrixOrder) :
    Derivation (star_10_121_reading body).parsed := by
  have line1 := Derivation.star_10_121 body
  exact line1

/-- Audited catalogue reading of ✱10·122. -/
def star_10_122_reading
    (body : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "If, for some a, there is a proposition φa, then there is a function\nφx̂, and vice versa.  [✱9·15]"
  parsed := .functionExistence body

/-- ✱10·122, the primitive function-existence claim cited from ✱9·15. -/
theorem star_10_122
    (body : Formula signature real [argument] matrixOrder) :
    Derivation (star_10_122_reading body).parsed := by
  have line1 := Derivation.star_10_122 body
  exact line1

/-- Audited catalogue reading of ✱10·12. -/
def star_10_12_reading
    (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(x).p ∨ φx .⊃ : p .∨ .(x).φx  [✱9·25]"
  parsed := .assertion (implication negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) phi))
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) phi)))

/-- ✱10·12, exactly the instance of ✱9·25 cited in print.
`demonstration_provenance: follows-printed`. -/
theorem star_10_12
    (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation
      (star_10_12_reading universal matrixDisjunction negation disjunction p phi).parsed := by
  have line1 := star_9_25 universal matrixDisjunction negation disjunction p phi
  exact line1

/-- Audited catalogue reading of the metalinguistic rule ✱10·13. -/
def star_10_13_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "If φx̂ and ψx̂ take arguments of the same type, and we have “⊢.φx”\nand “⊢.ψx,” we shall have “⊢.φx.ψx.”"
  parsed := .assertion (conjunction negation disjunction phi psi)

/-- ✱10·13. The printed premises are legitimate because PM states this item as a rule.
`demonstration_provenance: follows-printed`. -/
theorem star_10_13
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order)
    (phiDerived : ⊢ᵣ phi)
    (psiDerived : ⊢ᵣ psi) :
    Derivation (star_10_13_reading negation disjunction phi psi).parsed := by
  have line1 := star_3_2 negation disjunction phi psi
  have line2 := detach negation disjunction phi
    (implication negation disjunction psi
      (conjunction negation disjunction phi psi)) phiDerived line1
  have line3 := detach negation disjunction psi
    (conjunction negation disjunction phi psi) psiDerived line2
  exact line3

/-- The common AST obtained from the two sides of ✱10·23 by the printed
definitions ✱9·03, ✱9·02 and ✱1·01. -/
def star_10_23_normalForm
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  star_9_03 universal disjunction (.neg negation phi) p

/-- Left member (x).φx⊃p, with PM's full-scope convention ✱9·03
eliminated to its object AST. -/
def star_10_23_left
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  star_10_23_normalForm universal disjunction negation phi p

/-- Right member (∃x).φx⊃p, after the eliminable definitions ✱9·02
and ✱1·01 used on PM's first printed line. -/
def star_10_23_right
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  star_10_23_normalForm universal disjunction negation phi p

/-- Audited catalogue reading of ✱10·23. -/
def star_10_23_reading
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (matrixDisjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (matrixNegation : signature.Negation matrixOrder)
    (outerNegation : signature.Negation
      (bindOrder (max matrixOrder fixedOrder) argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder (max matrixOrder fixedOrder) argument))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    ClaimReading signature real where
  printed := "✱10·23.  ⊢ : .(x).φx⊃p .≡ : (∃x).φx .⊃ .p"
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (star_10_23_left universal matrixDisjunction matrixNegation phi p)
    (star_10_23_right universal matrixDisjunction matrixNegation phi p))

/-- ✱10·23.  PM's first demonstration reduces both printed members, in
order, by ✱4·2, ✱9·03, ✱9·02 and ✱1·01 to one formula.
demonstration_provenance: follows-printed. -/
theorem star_10_23
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (matrixDisjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (matrixNegation : signature.Negation matrixOrder)
    (outerNegation : signature.Negation
      (bindOrder (max matrixOrder fixedOrder) argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder (max matrixOrder fixedOrder) argument))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Derivation (star_10_23_reading universal matrixDisjunction matrixNegation
      outerNegation outerDisjunction phi p).parsed := by
  have line1 := star_4_2 outerNegation outerDisjunction
    (star_10_23_normalForm universal matrixDisjunction matrixNegation phi p)
  exact line1

/-- Audited catalogue reading of ✱10·24. -/
def star_10_24_reading
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    ClaimReading signature real where
  printed := "✱10·24.  ⊢ : φy .⊃ .(∃x).φx"
  parsed := .assertion (mixedImplication negation disjunction
    (body.instantiate value) (.sometimes existential body))

/-- ✱10·24.  After the eliminable definition ✱10·01 is unfolded, PM's
printed ✱10·1/`Transp` proof is the existential primitive ✱9·1.
`demonstration_provenance: follows-printed`. -/
theorem star_10_24
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Derivation (star_10_24_reading existential negation disjunction body value).parsed := by
  have line1 := Derivation.star_9_1 existential negation disjunction body value
  exact line1

/-- Audited catalogue reading of ✱10·26. -/
def star_10_26_reading
    (universal : signature.Universal argument matrixOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi psi : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    ClaimReading signature real where
  printed := "✱10·26. ⊢:. (z).φ z⊃ψ z:φ x:⊃.ψ x [*10·1. Imp]"
  parsed := .assertion (mixedImplication outerNegation outerDisjunction
    (.always universal (implication matrixNegation matrixDisjunction phi psi))
    ((implication matrixNegation matrixDisjunction phi psi).instantiate value))

/-- ✱10·26.  The printed ✱10·1 specialization already has the displayed
`Imp` presentation after unfolding the instantiated matrix.
`demonstration_provenance: follows-printed`. -/
theorem star_10_26
    (universal : signature.Universal argument matrixOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi psi : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Derivation (star_10_26_reading universal matrixNegation matrixDisjunction
      outerNegation outerDisjunction phi psi value).parsed := by
  have line1 := Derivation.star_10_1 universal outerNegation outerDisjunction
    (implication matrixNegation matrixDisjunction phi psi) value
  exact line1

/-- Audited catalogue reading of ✱10·43. -/
def star_10_43_reading
    (universal : signature.Universal argument matrixOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi psi : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    ClaimReading signature real where
  printed := "⊢ :. (φ!x ≡ₓ ψx) . ⊃ : φ!y . ≡ . ψy"
  parsed := .assertion (mixedImplication outerNegation outerDisjunction
    (.always universal (equivalence matrixNegation matrixDisjunction phi psi))
    ((equivalence matrixNegation matrixDisjunction phi psi).instantiate value))

/-- ✱10·43.  PM's first printed line is precisely ✱10·1 applied to the
equivalence matrix; ✱5·32 only rewrites its propositional presentation.
`demonstration_provenance: follows-printed`. -/
theorem star_10_43
    (universal : signature.Universal argument matrixOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi psi : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Derivation (star_10_43_reading universal matrixNegation matrixDisjunction
      outerNegation outerDisjunction phi psi value).parsed := by
  have line1 := Derivation.star_10_1 universal outerNegation outerDisjunction
    (equivalence matrixNegation matrixDisjunction phi psi) value
  exact line1

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_10_1
#print axioms PM.RamifiedSyntax.star_10_11
#print axioms PM.RamifiedSyntax.star_10_121
#print axioms PM.RamifiedSyntax.star_10_122
#print axioms PM.RamifiedSyntax.star_10_12
#print axioms PM.RamifiedSyntax.star_10_13
#print axioms PM.RamifiedSyntax.star_10_23
#print axioms PM.RamifiedSyntax.star_10_24
#print axioms PM.RamifiedSyntax.star_10_26
#print axioms PM.RamifiedSyntax.star_10_43
