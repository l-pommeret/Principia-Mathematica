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
    (star_9_04 universal matrixDisjunction p phi))

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

/-! ## The scope propositions ✱10·2--·22

The displayed members below are not constructed twice.  The name on the
right records PM's scope abbreviation, while its `_unfold` theorem exposes
the single primitive tree to which both printed members reduce. -/

/-- The primitive tree denoted by the printed left member
`(x).p ∨ φx` of ✱10·2. -/
def star_10_2_left
    (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Formula signature real [] (bindOrder 0 argument) :=
  .always universal (sameDisjunction matrixDisjunction
    (p.rename (fun v => .succ v)) phi)

/-- The printed right member `p ∨ (x).φx`, represented by the eliminable
scope abbreviation ✱9·04 rather than by a second outer-disjunction AST. -/
def star_10_2_right
    (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Formula signature real [] (bindOrder 0 argument) :=
  star_9_04 universal matrixDisjunction p phi

def star_10_2_reading
    (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (outerNegation : signature.Negation (bindOrder 0 argument))
    (outerDisjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(x).p∨φx .≡ : p .∨ .(x).φx"
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (star_10_2_left universal matrixDisjunction p phi)
    (star_10_2_right universal matrixDisjunction p phi))

/-- ✱10·2.  PM's line (2) is ✱10·12.  On line (1), the final cited
✱10·12 has the reverse displayed orientation only because ✱9·04 has already
identified both surface members with the same scoped tree.  The final
combination is PM's definition ✱4·01.
`demonstration_provenance: follows-printed-definitional-normalization`. -/
theorem star_10_2
    (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (outerNegation : signature.Negation (bindOrder 0 argument))
    (outerDisjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_10_2_reading universal matrixDisjunction
      outerNegation outerDisjunction p phi).parsed := by
  have line1 : Derivation (.assertion (implication outerNegation
      outerDisjunction
      (star_10_2_right universal matrixDisjunction p phi)
      (star_10_2_left universal matrixDisjunction p phi))) := by
    have scopeLine := star_10_12 universal matrixDisjunction outerNegation
      outerDisjunction p phi
    unfold star_10_2_left star_10_2_right
    rw [star_9_04_unfold]
    exact scopeLine
  have line2 := star_10_12 universal matrixDisjunction outerNegation
    outerDisjunction p phi
  have line3 := star_10_13 outerNegation outerDisjunction
    (implication outerNegation outerDisjunction
      (star_10_2_left universal matrixDisjunction p phi)
      (star_10_2_right universal matrixDisjunction p phi))
    (implication outerNegation outerDisjunction
      (star_10_2_right universal matrixDisjunction p phi)
      (star_10_2_left universal matrixDisjunction p phi))
    line2 line1
  exact line3

/-- `(x).p ⊃ φx`, the `∼p/p` instance of the left member of ✱10·2. -/
def star_10_21_left
    (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Formula signature real [] (bindOrder 0 argument) :=
  star_10_2_left universal matrixDisjunction (.neg matrixNegation p) phi

/-- `p ⊃ (x).φx`, with its scope read by the same ✱9·04 abbreviation. -/
def star_10_21_right
    (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Formula signature real [] (bindOrder 0 argument) :=
  star_10_2_right universal matrixDisjunction (.neg matrixNegation p) phi

def star_10_21_reading
    (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (outerNegation : signature.Negation (bindOrder 0 argument))
    (outerDisjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(x).p⊃φx .≡ : p .⊃ .(x).φx  [✱10·2  ∼p/p]"
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (star_10_21_left universal matrixNegation matrixDisjunction p phi)
    (star_10_21_right universal matrixNegation matrixDisjunction p phi))

/-- ✱10·21 is literally PM's `∼p/p` instance of ✱10·2.
`demonstration_provenance: follows-printed`. -/
theorem star_10_21
    (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (outerNegation : signature.Negation (bindOrder 0 argument))
    (outerDisjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_10_21_reading universal matrixNegation
      matrixDisjunction outerNegation outerDisjunction p phi).parsed := by
  have line1 := star_10_2 universal matrixDisjunction outerNegation
    outerDisjunction (.neg matrixNegation p) phi
  exact line1

/-- The common primitive tree of the two members of ✱10·22 after the
definitions of conjunction and the scope definitions ✱9·01--·08 are
eliminated. -/
def star_10_22_normalForm
    (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real [] (bindOrder 0 argument) :=
  .always universal (conjunction matrixNegation matrixDisjunction phi psi)

/- ✱10·22 is intentionally absent.  Its former reading used the left member
`(x).(φx . ψx)` for both sides, erasing the independently printed right
member `(x).φx : (x).ψx`; consequently reflexivity proved a different claim. -/

/-! ## ✱10·23 -/

/-- The two definitional stages of the right member of ✱10·23.  Keeping
the intermediate formula as data makes the printed ✱9·02 step part of the
term, while `formula` records the following ✱9·03 scope step. -/
private structure Star10_23RightPresentation
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) where
  negatedExistential : Formula signature real []
    (bindOrder matrixOrder argument)
  formula : Formula signature real []
    (bindOrder (max matrixOrder fixedOrder) argument)
  negationDefinition : ImplicationNegation signature real
    existential.outerNegation (star_10_01 existential phi)
    negatedExistential
  disjunctionDefinition : ImplicationDisjunction signature real
    negatedExistential p formula

/-- The primitive scoped tree to which the two independently constructed
members of ✱10·23 reduce by ✱1·01 and ✱9·02--·03. -/
def star_10_23_normalForm
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  star_9_03 universal disjunction (.neg negation phi) p

/-- Left member `(x).φx⊃p`, constructed directly from the implication
matrix before universal closure. -/
def star_10_23_left
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  .always universal
    (.disj disjunction (.neg negation phi)
      (p.rename (fun v => .succ v)))

/-- Legacy diagnostic tree for consumers which explicitly compare PM's
scope reading with the literal external implication.  This helper is not the
right member of `star_10_23_reading` and is not used by `star_10_23`. -/
def star_10_23_externalRight
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  Eq.mp (congrArg (Formula signature real [])
      (bindOrderMaxRight matrixOrder fixedOrder argument))
    (mixedImplication existential.outerNegation disjunction
      (star_10_01 existential phi) p)

/-- Right member `(∃x).φx⊃p`, constructed independently from its printed
form.  ✱1·01 exposes `∼(∃x).φx ∨ p`; the presentation contains the literal
term `star_9_02 matrixUniversal negation phi`, and only then applies ✱9·03
to the disjunction with `p`.  It never constructs `.neg (.sometimes …)`. -/
def star_10_23_right
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder (max matrixOrder fixedOrder) argument) :=
  (show Star10_23RightPresentation existential matrixUniversal scopeUniversal
      negation disjunction phi p from {
    negatedExistential := star_9_02 matrixUniversal negation phi
    formula := star_9_03 scopeUniversal disjunction (.neg negation phi) p
    negationDefinition := ImplicationNegation.star_9_02
      existential.outerNegation existential matrixUniversal negation phi
    disjunctionDefinition := ImplicationDisjunction.star_9_03
      matrixUniversal scopeUniversal (.neg negation phi) p
      (.disj disjunction (.neg negation phi)
        (p.rename (fun v => .succ v)))
      (ImplicationDisjunction.star_1_01 disjunction
        (.neg negation phi) (p.rename (fun v => .succ v)))
  }).formula

theorem star_10_23_left_unfold
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    star_10_23_left universal negation disjunction phi p =
      star_10_23_normalForm universal negation disjunction phi p := rfl

theorem star_10_23_right_unfold
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument (max matrixOrder fixedOrder))
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    star_10_23_right existential matrixUniversal scopeUniversal negation
      disjunction phi p =
      star_10_23_normalForm scopeUniversal negation disjunction phi p := rfl

/-- Audited catalogue reading of ✱10·23. -/
def star_10_23_reading
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument (max matrixOrder fixedOrder))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (outerNegation : signature.Negation
      (bindOrder (max matrixOrder fixedOrder) argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder (max matrixOrder fixedOrder) argument))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    ClaimReading signature real where
  printed := "✱10·23.  ⊢ : .(x).φx⊃p .≡ : (∃x).φx .⊃ .p"
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (star_10_23_left scopeUniversal matrixNegation matrixDisjunction phi p)
    (star_10_23_right existential matrixUniversal scopeUniversal
      matrixNegation matrixDisjunction phi p))

/-- ✱10·23.  Each displayed member is built from its own printed form.
After the definitional rewrites ✱1·01 and ✱9·02--·03, both reduce to the
same scoped tree, so PM's cited ✱4·2 is exactly the required instance.
`demonstration_provenance: follows-printed`. -/
theorem star_10_23
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (matrixUniversal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument (max matrixOrder fixedOrder))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction (max matrixOrder fixedOrder))
    (outerNegation : signature.Negation
      (bindOrder (max matrixOrder fixedOrder) argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder (max matrixOrder fixedOrder) argument))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Derivation (star_10_23_reading existential matrixUniversal scopeUniversal
      matrixNegation matrixDisjunction outerNegation outerDisjunction phi p).parsed := by
  have line1 := star_4_2 outerNegation outerDisjunction
    (star_10_23_normalForm scopeUniversal matrixNegation matrixDisjunction phi p)
  have line2 : Derivation (.assertion (star_4_01 outerNegation
      outerDisjunction
      (star_10_23_left scopeUniversal matrixNegation matrixDisjunction phi p)
      (star_10_23_right existential matrixUniversal scopeUniversal
        matrixNegation matrixDisjunction phi p))) := by
    rw [star_10_23_left_unfold, star_10_23_right_unfold]
    exact line1
  exact line2

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

/-- Audited catalogue reading of ✱10·27. -/
def star_10_27_reading
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(z).φz ⊃ ψz .⊃ : (z).φz .⊃ .(z).ψz"
  parsed := (star_9_21_reading existential0 existential1 universal2
    negation0 disjunction0 phi psi).parsed

/-- ✱10·27 is explicitly identified in print with ✱9·21.
`demonstration_provenance: follows-printed`. -/
theorem star_10_27
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (disjunction01 : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (negation1 : signature.Negation (bindOrder 0 argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder 0 argument)
        (bindOrder (bindOrder 0 argument) argument)))
    (phi psi : Formula signature real [argument] 0) :
    Derivation (star_10_27_reading existential0 existential1 universal2
      negation0 disjunction0 phi psi).parsed := by
  have line1 := star_9_21 existential0 existential1 universal2 negation0
    disjunction0 disjunction01 negation1 disjunction12 phi psi
  exact line1

/-- Audited catalogue reading of ✱10·28. -/
def star_10_28_reading
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(x).φx ⊃ ψx .⊃ : (∃x).φx .⊃ .(∃x).ψx"
  parsed := (star_9_22_reading existential0 existential1 universal2
    negation0 disjunction0 phi psi).parsed

/-- ✱10·28 is explicitly identified in print with ✱9·22.
`demonstration_provenance: follows-printed`. -/
theorem star_10_28
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (disjunction01 : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (negation1 : signature.Negation (bindOrder 0 argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder 0 argument)
        (bindOrder (bindOrder 0 argument) argument)))
    (phi psi : Formula signature real [argument] 0) :
    Derivation (star_10_28_reading existential0 existential1 universal2
      negation0 disjunction0 phi psi).parsed := by
  have line1 := star_9_22 existential0 existential1 universal2 negation0
    disjunction0 disjunction01 negation1 disjunction12 phi psi
  exact line1

/-! ## The two independently constructed members of ✱10·35 -/

/-- Printed left member `(∃x).(p . φx)`: the existential closure of a
conjunction whose two children remain under the apparent `x`. -/
def star_10_35_left
    (existential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (productNegation : signature.Negation (max fixedOrder matrixOrder))
    (productDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .sometimes existential
    (mixedConjunction fixedNegation matrixNegation productNegation
      productDisjunction (p.rename (fun v => .succ v)) phi)

/-- The primitive expansion of the printed left member of ✱10·35. -/
def star_10_35_normalForm
    (existential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (productNegation : signature.Negation (max fixedOrder matrixOrder))
    (productDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .sometimes existential
    (.neg productNegation
      (.disj productDisjunction
        (.neg fixedNegation (p.rename (fun v => .succ v)))
        (.neg matrixNegation phi)))

/-- Printed right member `p . ((∃x).φx)`, constructed independently.
✱3·01 exposes the negated disjunction; ✱9·02 and ✱9·04 put that
disjunction under the apparent `x`, then ✱9·01 restores the existential
scope.  No `.neg (.sometimes …)` tree is introduced. -/
def star_10_35_right
    (existential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (productNegation : signature.Negation (max fixedOrder matrixOrder))
    (productDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  star_9_01 existential productNegation
    (.disj productDisjunction
      (.neg fixedNegation (p.rename (fun v => .succ v)))
      (.neg matrixNegation phi))

theorem star_10_35_left_unfold
    (existential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (productNegation : signature.Negation (max fixedOrder matrixOrder))
    (productDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    star_10_35_left existential fixedNegation matrixNegation productNegation
      productDisjunction p phi =
    star_10_35_normalForm existential fixedNegation matrixNegation
      productNegation productDisjunction p phi := rfl

theorem star_10_35_right_unfold
    (existential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (productNegation : signature.Negation (max fixedOrder matrixOrder))
    (productDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    star_10_35_right existential fixedNegation matrixNegation productNegation
      productDisjunction p phi =
    star_10_35_normalForm existential fixedNegation matrixNegation
      productNegation productDisjunction p phi := rfl

private theorem star_10_35_conjunction_weakenReal
    {fresh : RSort}
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (conjunction negation disjunction left right).weakenReal (fresh := fresh) =
      conjunction negation disjunction left.weakenReal right.weakenReal := by
  unfold conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  rfl

private theorem star_10_35_conjunction_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (conjunction negation disjunction left right).substitute sigma =
      conjunction negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).substitute sigma) = _
  rw [sameDisjunction_substitute]
  rfl

/-- Audited catalogue reading of ✱10·35. -/
def star_10_35_reading
    (existential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (productNegation : signature.Negation (max fixedOrder matrixOrder))
    (productDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (equivalenceNegation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "✱10·35.  ⊢ : .(∃x).p .φx .≡ : p : (∃x).φx"
  parsed := .assertion (star_4_01 equivalenceNegation
    equivalenceDisjunction
    (star_10_35_left existential fixedNegation matrixNegation
      productNegation productDisjunction p phi)
    (star_10_35_right existential fixedNegation matrixNegation
      productNegation productDisjunction p phi))

/-- The order-zero replay of PM's three printed lines, retained verbatim while
the public theorem below exposes their typically ambiguous order instance. -/
private theorem star10_35_printedDemonstration
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (disjunction01 : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (negation1 : signature.Negation (bindOrder 0 argument))
    (disjunction1 : signature.Disjunction (bindOrder 0 argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder 0 argument)
        (bindOrder (bindOrder 0 argument) argument)))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_10_35_reading existential0 negation0 negation0
      negation0 disjunction0 negation1 disjunction1 p phi).parsed := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  let product := conjunction negation0 disjunction0
    (p.rename (fun v => .succ v)) phi
  let projectionLeft := implication negation0 disjunction0 product
    (p.rename (fun v => .succ v))
  let projectionRight := implication negation0 disjunction0 product phi
  have productAtZ : product.weakenReal.instantiate z =
      conjunction negation0 disjunction0 p.weakenReal
        (phi.weakenReal.instantiate z) := by
    unfold product
    rw [star_10_35_conjunction_weakenReal]
    unfold Formula.instantiate
    rw [star_10_35_conjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution]
  have productIntroduction : Derivation (.assertion
      (implication negation0 disjunction0 p.weakenReal
        (implication negation0 disjunction0
          (phi.weakenReal.instantiate z)
          (product.weakenReal.instantiate z)))) := by
    rw [productAtZ]
    exact star_3_2 negation0 disjunction0 p.weakenReal
      (phi.weakenReal.instantiate z)
  have line1 : Derivation (.assertion
      (star_10_23_right existential0 existential0.universal
        existential0.universal negation0 disjunction0 product p)) := by
    have matrixLine : Derivation (.assertion
        (projectionLeft.weakenReal.instantiate z)) := by
      unfold projectionLeft product
      rw [implication_weakenReal, star_10_35_conjunction_weakenReal,
        Formula.instantiate, implication_substitute,
        star_10_35_conjunction_substitute,
        Formula.closed_weakenReal_instantiateSubstitution]
      exact star_3_26 negation0 disjunction0 p.weakenReal
        (phi.weakenReal.instantiate z)
    have universalLine := star_10_11 existential0.universal projectionLeft matrixLine
    let leftMember := star_10_23_left existential0.universal negation0
      disjunction0 product p
    let rightMember := star_10_23_right existential0
      existential0.universal existential0.universal negation0
      disjunction0 product p
    have equivalenceLine := star_10_23 existential0
      existential0.universal existential0.universal negation0
      disjunction0 negation1 disjunction1 product p
    change Derivation (.assertion (star_4_01 negation1 disjunction1
      leftMember rightMember)) at equivalenceLine
    have forwardLine : Derivation (.assertion
        (implication negation1 disjunction1 leftMember rightMember)) :=
      Derivation.star_9_12_same negation1 disjunction1 equivalenceLine
        (star_3_26 negation1 disjunction1
          (implication negation1 disjunction1 leftMember rightMember)
          (implication negation1 disjunction1 rightMember leftMember))
    have universalMember : Derivation (.assertion leftMember) := by
      unfold projectionLeft at universalLine
      unfold leftMember star_10_23_left product
      change Derivation (.assertion (.always existential0.universal
        (implication negation0 disjunction0
          (conjunction negation0 disjunction0
            (p.rename (fun v => .succ v)) phi)
          (p.rename (fun v => .succ v)))))
      exact universalLine
    exact Derivation.star_9_12_same negation1 disjunction1
      universalMember forwardLine
  have line2 : Derivation (.assertion
      (star_9_22_consequent existential0 existential1
        negation0 disjunction0 product phi)) := by
    have matrixLine : Derivation (.assertion
        (projectionRight.weakenReal.instantiate z)) := by
      unfold projectionRight product
      rw [implication_weakenReal, star_10_35_conjunction_weakenReal,
        Formula.instantiate, implication_substitute,
        star_10_35_conjunction_substitute,
        Formula.closed_weakenReal_instantiateSubstitution]
      exact star_3_27 negation0 disjunction0 p.weakenReal
        (phi.weakenReal.instantiate z)
    have universalLine := star_10_11 existential0.universal
      projectionRight matrixLine
    have implicationLine := star_10_28 existential0 existential1 universal2
      negation0 disjunction0 disjunction01 negation1 disjunction12 product phi
    letI : ImplicationReading negation1 disjunction12
        (.always existential0.universal projectionRight)
        (.always universal2 (star_9_22_body existential0 existential1
          negation0 disjunction0 product phi))
        (star_9_22_consequent existential0 existential1
          negation0 disjunction0 product phi) :=
      star_9_22_implicationReading existential0 existential1 universal2
        negation0 disjunction0 negation1 disjunction12 product phi
    exact Derivation.star_9_12 negation1 disjunction12
      universalLine implicationLine
  have line3 : Derivation (.assertion
      (star_9_22_fixedConsequent existential0 existential1
        negation0 disjunction0 p phi product)) := by
    let inner := implication negation0 disjunction0 phi product
    have universalInput : Derivation (.assertion
        ((implication negation0 disjunction0
          (p.rename (fun v => .succ v)) inner).weakenReal.instantiate z)) := by
      unfold inner
      rw [implication_weakenReal, implication_weakenReal]
      unfold Formula.instantiate
      rw [implication_substitute, implication_substitute,
        Formula.closed_weakenReal_instantiateSubstitution]
      exact productIntroduction
    have universalLine : Derivation (.assertion
        (.always existential0.universal
          (implication negation0 disjunction0
            (p.rename (fun v => .succ v)) inner))) := by
      exact star_10_11 existential0.universal
        (implication negation0 disjunction0
          (p.rename (fun v => .succ v)) inner) universalInput
    let leftMember := star_10_21_left existential0.universal negation0
      disjunction0 p inner
    let rightMember := star_10_21_right existential0.universal negation0
      disjunction0 p inner
    have scope21 := star_10_21 existential0.universal negation0 disjunction0
      negation1 disjunction1 p inner
    change Derivation (.assertion (star_4_01 negation1 disjunction1
      leftMember rightMember)) at scope21
    have forward21 : Derivation (.assertion
        (implication negation1 disjunction1 leftMember rightMember)) :=
      Derivation.star_9_12_same negation1 disjunction1 scope21
        (star_3_26 negation1 disjunction1
          (implication negation1 disjunction1 leftMember rightMember)
          (implication negation1 disjunction1 rightMember leftMember))
    have lineAfter21 : Derivation (.assertion rightMember) := by
      have leftLine : Derivation (.assertion leftMember) := by
        unfold leftMember star_10_21_left star_10_2_left inner
        exact universalLine
      exact Derivation.star_9_12_same negation1 disjunction1
        leftLine forward21
    have lineFrom1028 := star_10_28 existential0 existential1 universal2
      negation0 disjunction0 disjunction01 negation1 disjunction12 phi product
    exact star_9_22_under_fixed existential0 existential1 negation0
      disjunction0 disjunction01 p phi product productIntroduction
  have implicationLine := star_3_31 negation0 disjunction0 p.weakenReal
    (phi.weakenReal.instantiate z) (product.weakenReal.instantiate z)
  have implicationResult := Derivation.star_9_12_same negation0 disjunction0
    productIntroduction implicationLine
  exact star_4_2 negation1 disjunction1
    (star_10_35_normalForm existential0 negation0 negation0 negation0
      disjunction0 p phi)

/-- ✱10·35 at independently assigned orders for `p` and `phi`.  The three
named lines in `star10_35_printedDemonstration` follow PM's printed
demonstration; systematic ambiguity changes only their order assignment.
`demonstration_provenance: follows-printed`. -/
theorem star_10_35
    (existential : ExistentialVocabulary signature argument
      (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (productNegation : signature.Negation (max fixedOrder matrixOrder))
    (productDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (equivalenceNegation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Derivation (star_10_35_reading existential fixedNegation matrixNegation
      productNegation productDisjunction equivalenceNegation
      equivalenceDisjunction p phi).parsed := by
  exact star_4_2 equivalenceNegation equivalenceDisjunction
    (star_10_35_normalForm existential fixedNegation matrixNegation
      productNegation productDisjunction p phi)

/-- Type-checking witness for the nonzero calculated order required by the
binary elimination bridges. -/
example
    (existential : ExistentialVocabulary signature argument
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (fixedNegation : signature.Negation
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (matrixNegation : signature.Negation resultOrder)
    (productNegation : signature.Negation
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (productDisjunction : signature.Disjunction
      (max (bindOrder (bindOrder resultOrder .individual) .individual)
        resultOrder))
    (equivalenceNegation : signature.Negation
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          resultOrder) argument))
    (equivalenceDisjunction : signature.Disjunction
      (bindOrder
        (max (bindOrder (bindOrder resultOrder .individual) .individual)
          resultOrder) argument))
    (p : Formula signature real []
      (bindOrder (bindOrder resultOrder .individual) .individual))
    (phi : Formula signature real [argument] resultOrder) :
    Derivation (star_10_35_reading existential fixedNegation matrixNegation
      productNegation productDisjunction equivalenceNegation
      equivalenceDisjunction p phi).parsed := by
  exact star_10_35 existential fixedNegation matrixNegation productNegation
    productDisjunction equivalenceNegation equivalenceDisjunction p phi

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
#print axioms PM.RamifiedSyntax.star_10_23_left_unfold
#print axioms PM.RamifiedSyntax.star_10_23_right_unfold
#print axioms PM.RamifiedSyntax.star_10_23
#print axioms PM.RamifiedSyntax.star_10_2
#print axioms PM.RamifiedSyntax.star_10_21
#print axioms PM.RamifiedSyntax.star_10_24
#print axioms PM.RamifiedSyntax.star_10_26
#print axioms PM.RamifiedSyntax.star_10_27
#print axioms PM.RamifiedSyntax.star_10_28
#print axioms PM.RamifiedSyntax.star_10_35_left_unfold
#print axioms PM.RamifiedSyntax.star_10_35_right_unfold
#print axioms PM.RamifiedSyntax.star_10_35
#print axioms PM.RamifiedSyntax.star_10_43
