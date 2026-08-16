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
    {fixedOrder matrixOrder : Nat}
    (universal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (negation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (disjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "⊢ : .(x).p ∨ φx .⊃ : p .∨ .(x).φx  [✱9·25]"
  parsed := .assertion (implication negation disjunction
    (.always universal (.disj matrixDisjunction
      (p.rename (fun v => .succ v)) phi))
    (star_9_04 universal matrixDisjunction p phi))

/-- ✱10·12, exactly the instance of ✱9·25 cited in print.
`demonstration_provenance: follows-printed`. -/
theorem star_10_12
    {fixedOrder matrixOrder : Nat}
    (universal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (negation : signature.Negation
      (bindOrder (max fixedOrder matrixOrder) argument))
    (disjunction : signature.Disjunction
      (bindOrder (max fixedOrder matrixOrder) argument))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
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

/-! ## ✱10·14 -/

/-- At any order already raised by binding `sort`, binding the same sort
again preserves the assigned order. -/
private theorem star10_bindOrderHeight (baseOrder : Nat) (sort : RSort) :
    bindOrder (bindOrder baseOrder sort) sort = bindOrder baseOrder sort := by
  unfold bindOrder
  exact MixedOrder.maxRightAbsorb baseOrder (Nat.succ sort.height)

/-- A universal formula normalized only along the computed equality of its
assigned orders. -/
private def star10_stableUniversal
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  Eq.mp (congrArg (Formula signature real [])
      (star10_bindOrderHeight baseOrder sort))
    (.always universal body)

private theorem star10_castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

/-- ✱10·1 normalized at the least stable assigned order. -/
private theorem star10_stableSpecialize
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort))
    (value : Term signature real [] sort) :
    Derivation (.assertion (implication negation disjunction
      (star10_stableUniversal universal body) (body.instantiate value))) := by
  let bindEq := star10_bindOrderHeight baseOrder sort
  let resultEq := natMaxCongr bindEq rfl
  let rawNegation :=
    Eq.mp (congrArg signature.Negation bindEq.symm) negation
  let rawDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let rawFormula := mixedImplication rawNegation rawDisjunction
    (.always universal body) (body.instantiate value)
  have rawLine : Derivation (.assertion rawFormula) :=
    star_10_1 universal rawNegation rawDisjunction body value
  have castLine : Derivation (.assertion (Eq.mp
      (congrArg (Formula signature real []) resultEq) rawFormula)) :=
    star10_castAssertionOrder resultEq rawFormula rawLine
  have normalized :
      Eq.mp (congrArg (Formula signature real []) resultEq) rawFormula =
        implication negation disjunction
          (star10_stableUniversal universal body) (body.instantiate value) := by
    exact mixedImplication_normalizeSameOrder bindEq rfl
      negation disjunction (.always universal body) (body.instantiate value)
  exact Derivation.castAssertion normalized.symm castLine

private theorem star10_stableUniversal_weakenReal
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort)) :
    (star10_stableUniversal universal body).weakenReal (fresh := fresh) =
      star10_stableUniversal universal body.weakenReal := by
  unfold star10_stableUniversal
  exact Formula.weakenReal_cast (star10_bindOrderHeight baseOrder sort)
    (.always universal body)

/-- ✱10·11 normalized at the same stable assigned order. -/
private theorem star10_stableGeneralize
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort))
    (line : Derivation (.assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (sort :: real) sort))))) :
    Derivation (.assertion (star10_stableUniversal universal body)) := by
  have rawLine := star_10_11 universal body line
  exact star10_castAssertionOrder (star10_bindOrderHeight baseOrder sort)
    (.always universal body) rawLine

/-- Generalize a same-order implication whose antecedent is closed with
respect to the apparent variable. -/
private theorem star10_stableGeneralizeImplication
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort))
    (line : Derivation (.assertion (implication negation disjunction
      p.weakenReal
      (body.weakenReal.instantiate
        (.real (.zero : Var (sort :: real) sort)))))) :
    Derivation (.assertion (star10_stableUniversal universal
      (implication negation disjunction
        (p.rename (fun v => .succ v)) body))) := by
  let value : Term signature (sort :: real) [] sort := .real .zero
  have matrixLine : Derivation (.assertion
      ((implication negation disjunction
        (p.rename (fun v => .succ v)) body).weakenReal.instantiate value)) := by
    rw [implication_weakenReal, Formula.instantiate,
      implication_substitute,
      Formula.closed_weakenReal_instantiateSubstitution]
    exact line
  exact star10_stableGeneralize universal
    (implication negation disjunction
      (p.rename (fun v => .succ v)) body) matrixLine

/-- The independently constructed left member `(x).φx : (x).ψx` of ✱10·14. -/
def star_10_14_left
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  conjunction negation disjunction
    (star10_stableUniversal universal phi)
    (star10_stableUniversal universal psi)

/-- The independently constructed right member `φy . ψy` of ✱10·14. -/
def star_10_14_right
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument))
    (value : Term signature real [] argument) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  conjunction negation disjunction
    (phi.instantiate value) (psi.instantiate value)

/-- Audited catalogue reading of ✱10·14. -/
def star_10_14_reading
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument))
    (value : Term signature real [] argument) :
    ClaimReading signature real where
  printed := "⊢ : .(x).φx : (x).ψx : ⊃ .φy .ψy"
  parsed := .assertion (implication negation disjunction
    (star_10_14_left universal negation disjunction phi psi)
    (star_10_14_right negation disjunction phi psi value))

/-- ✱10·14.  Lines (1) and (2) are the two printed ✱10·1 instances;
`line3` is their ✱10·13 product and `line4` is the cited ✱3·47 instance.
`demonstration_provenance: follows-printed`. -/
theorem star_10_14
    {baseOrder : Nat}
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument))
    (value : Term signature real [] argument) :
    Derivation (star_10_14_reading universal negation disjunction
      phi psi value).parsed := by
  have line1 := star10_stableSpecialize universal negation disjunction phi value
  have line2 := star10_stableSpecialize universal negation disjunction psi value
  have line3 := star_10_13 negation disjunction
    (implication negation disjunction
      (star10_stableUniversal universal phi) (phi.instantiate value))
    (implication negation disjunction
      (star10_stableUniversal universal psi) (psi.instantiate value))
    line1 line2
  have line4 := detach negation disjunction
    (conjunction negation disjunction
      (implication negation disjunction
        (star10_stableUniversal universal phi) (phi.instantiate value))
      (implication negation disjunction
        (star10_stableUniversal universal psi) (psi.instantiate value)))
    (implication negation disjunction
      (conjunction negation disjunction
        (star10_stableUniversal universal phi)
        (star10_stableUniversal universal psi))
      (conjunction negation disjunction
        (phi.instantiate value) (psi.instantiate value)))
    line3 (star_3_47 negation disjunction
      (star10_stableUniversal universal phi)
      (star10_stableUniversal universal psi)
      (phi.instantiate value) (psi.instantiate value))
  exact line4

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
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "⊢ : .(z).φz ⊃ ψz .⊃ : (z).φz .⊃ .(z).ψz"
  parsed := (star_9_21_reading existential0 existential1 universal2
    negation0 disjunction0 phi psi).parsed

/-- ✱10·27 is explicitly identified in print with ✱9·21.
`demonstration_provenance: follows-printed`. -/
theorem star_10_27
    {matrixOrder : Nat}
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (disjunction01 : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (negation1 : signature.Negation (bindOrder matrixOrder argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder (bindOrder matrixOrder argument) argument)))
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (star_10_27_reading existential0 existential1 universal2
      negation0 disjunction0 phi psi).parsed := by
  have line1 := star_9_21 existential0 existential1 universal2 negation0
    disjunction0 disjunction01 negation1 disjunction12 phi psi
  exact line1

/-- Audited catalogue reading of ✱10·28. -/
def star_10_28_reading
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "⊢ : .(x).φx ⊃ ψx .⊃ : (∃x).φx .⊃ .(∃x).ψx"
  parsed := (star_9_22_reading existential0 existential1 universal2
    negation0 disjunction0 phi psi).parsed

/-- ✱10·28 is explicitly identified in print with ✱9·22.
`demonstration_provenance: follows-printed`. -/
theorem star_10_28
    {matrixOrder : Nat}
    (existential0 : ExistentialVocabulary signature argument matrixOrder)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder matrixOrder argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder matrixOrder argument) argument))
    (negation0 : signature.Negation matrixOrder)
    (disjunction0 : signature.Disjunction matrixOrder)
    (disjunction01 : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (negation1 : signature.Negation (bindOrder matrixOrder argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder matrixOrder argument)
        (bindOrder (bindOrder matrixOrder argument) argument)))
    (phi psi : Formula signature real [argument] matrixOrder) :
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

private theorem star10_matrixEquivalence_weakenReal
    {fresh : RSort}
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (equivalence negation disjunction left right).weakenReal (fresh := fresh) =
      equivalence negation disjunction left.weakenReal right.weakenReal := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).weakenReal))
      (.neg negation
        ((implication negation disjunction right left).weakenReal))) = _
  rw [implication_weakenReal, implication_weakenReal]

private theorem star10_matrixEquivalence_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (equivalence negation disjunction left right).substitute sigma =
      equivalence negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).substitute
        sigma) = _
  rw [sameDisjunction_substitute]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).substitute sigma))
      (.neg negation
        ((implication negation disjunction right left).substitute sigma))) = _
  rw [implication_substitute, implication_substitute]

/-! ## ✱10·22 and its stable-order ✱10·21 scope instance -/

/-- The independently constructed left member `(x).p⊃φx` of the stable-order
instance of ✱10·21. -/
def star_10_21_stable_left
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (p : Formula signature real [] (bindOrder baseOrder argument))
    (phi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  star10_stableUniversal (baseOrder := baseOrder) universal
    (implication negation disjunction (p.rename (fun v => .succ v)) phi)

/-- The independently constructed scoped reading of `p⊃(x).φx` in the same
instance of ✱10·21.  Its root remains the `.always` introduced by ✱9·04. -/
def star_10_21_stable_right
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (p : Formula signature real [] (bindOrder baseOrder argument))
    (phi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  star10_stableUniversal (baseOrder := baseOrder) universal
    (sameDisjunction disjunction
      ((Formula.neg negation p).rename (fun v => .succ v)) phi)

theorem star_10_21_stable_left_unfold
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (p : Formula signature real [] (bindOrder baseOrder argument))
    (phi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    star_10_21_stable_left (baseOrder := baseOrder) universal negation
        disjunction p phi =
      star_10_21_stable_right (baseOrder := baseOrder) universal negation
        disjunction p phi := rfl

/-- Audited stable-order reading of the acquired scope proposition ✱10·21. -/
def star_10_21_stable_reading
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (p : Formula signature real [] (bindOrder baseOrder argument))
    (phi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    ClaimReading signature real where
  printed := "⊢ : .(x).p⊃φx .≡ : p .⊃ .(x).φx  [✱10·2  ∼p/p]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_10_21_stable_left (baseOrder := baseOrder) universal negation
      disjunction p phi)
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction p phi))

/-- The least stable-order instance of ✱10·21, retaining the independently
printed members until the cited scope definition is unfolded.
`demonstration_provenance: follows-printed-definitional-normalization`. -/
theorem star_10_21_stable
    {baseOrder : Nat}
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (p : Formula signature real [] (bindOrder baseOrder argument))
    (phi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Derivation (star_10_21_stable_reading universal negation disjunction
      p phi).parsed := by
  have line1 := star_4_2 negation disjunction
    (star_10_21_stable_right universal negation disjunction p phi)
  unfold star_10_21_stable_reading
  rw [star_10_21_stable_left_unfold]
  exact line1

/-- The ✱9·04 certificate carried by the right member of the stable-order
✱10·21 instance. -/
private def star10_castImplicationDisjunctionOrder
    (equality : sourceOrder = targetOrder)
    (left : Formula signature real [] leftOrder)
    (right result : Formula signature real [] sourceOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real left
      (Eq.mp (congrArg (Formula signature real []) equality) right)
      (Eq.mp (congrArg (Formula signature real []) equality) result) := by
  cases equality
  exact reading

private def star10_stableScopeDisjunction
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (p : Formula signature real [] (bindOrder baseOrder argument))
    (phi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    ImplicationDisjunction signature real (.neg negation p)
      (star10_stableUniversal universal phi)
      (star_10_21_stable_right universal negation disjunction p phi) := by
  let result := sameDisjunction disjunction
    ((Formula.neg negation p).rename (fun v => .succ v)) phi
  have rawReading : ImplicationDisjunction signature real (.neg negation p)
      (.always universal phi) (.always universal result) := by
    apply ImplicationDisjunction.star_9_04 universal universal
    exact ImplicationDisjunction.star_1_01_same disjunction
      ((Formula.neg negation p).rename (fun v => .succ v)) phi
  exact star10_castImplicationDisjunctionOrder
    (star10_bindOrderHeight baseOrder argument) (.neg negation p)
    (.always universal phi) (.always universal result) rawReading

/-- Apply the forward half of the cited stable-order ✱10·21 instance. -/
private theorem star10_applyStableScope
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (p : Formula signature real [] (bindOrder baseOrder argument))
    (phi : Formula signature real [argument]
      (bindOrder baseOrder argument))
    (line : Derivation (.assertion
      (star_10_21_stable_left universal negation disjunction p phi))) :
    Derivation (.assertion
      (star_10_21_stable_right universal negation disjunction p phi)) := by
  let left := star_10_21_stable_left universal negation disjunction p phi
  let right := star_10_21_stable_right universal negation disjunction p phi
  have equivalenceLine := star_10_21_stable universal negation disjunction p phi
  change Derivation (.assertion (star_4_01 negation disjunction
    left right)) at equivalenceLine
  have forwardLine := Derivation.star_9_12_same negation disjunction
    equivalenceLine
    (star_3_26 negation disjunction
      (implication negation disjunction left right)
      (implication negation disjunction right left))
  exact Derivation.star_9_12_same negation disjunction line forwardLine

/-- `Syll` with independently certified, same-order implication trees. -/
private theorem star10_composeCertified
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r pNegated qNegated pqFormula qrFormula prFormula :
      Formula signature real [] order)
    (pNegationDefinition :
      ImplicationNegation signature real negation p pNegated)
    (qNegationDefinition :
      ImplicationNegation signature real negation q qNegated)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula)
    (line1 : Derivation (.assertion pqFormula))
    (line2 : Derivation (.assertion qrFormula)) :
    Derivation (.assertion prFormula) := by
  let syllReading := star2_05ReadingOfSameOrderComponents
    negation disjunction p q r pNegated qNegated pqFormula qrFormula prFormula
    pNegationDefinition qNegationDefinition pqDisjunctionDefinition
    qrDisjunctionDefinition prDisjunctionDefinition
  have syll := star_2_05 negation disjunction p q r
    (reading := syllReading)
  have step := Derivation.star_9_12_same negation disjunction line2 syll
  exact Derivation.star_9_12_same negation disjunction line1 step

private theorem star10_composeSame
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : Derivation (.assertion
      (implication negation disjunction p q)))
    (line2 : Derivation (.assertion
      (implication negation disjunction q r))) :
    Derivation (.assertion (implication negation disjunction p r)) := by
  exact star10_composeCertified negation disjunction p q r
    (.neg negation p) (.neg negation q)
    (implication negation disjunction p q)
    (implication negation disjunction q r)
    (implication negation disjunction p r)
    (ImplicationNegation.star_1_01 negation p)
    (ImplicationNegation.star_1_01 negation q)
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation p) q)
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation q) r)
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation p) r)
    line1 line2

/-- `Exp` with an independently certified implication as its premiss. -/
private theorem star10_exportCertified
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r formula : Formula signature real [] order)
    (formulaReading : ImplicationDisjunction signature real
      (.neg negation (conjunction negation disjunction p q)) r formula)
    (line : Derivation (.assertion formula)) :
    Derivation (.assertion (implication negation disjunction p
      (implication negation disjunction q r))) := by
  let product := conjunction negation disjunction p q
  let qToProduct := implication negation disjunction q product
  let qToR := implication negation disjunction q r
  have introduction := star_3_2 negation disjunction p q
  let syllReading := star2_05ReadingOfSameOrderComponents
    negation disjunction q product r
    (.neg negation q) (.neg negation product)
    qToProduct formula qToR
    (ImplicationNegation.star_1_01 negation q)
    (ImplicationNegation.star_1_01 negation product)
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation q) product)
    formulaReading
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation q) r)
  have syll := star_2_05 negation disjunction q product r
    (reading := syllReading)
  have transfer := Derivation.star_9_12_same negation disjunction line syll
  exact star10_composeSame negation disjunction p qToProduct qToR
    introduction transfer

/-- The printed `Comp` used at line (4), generalized only by the certified
✱9·04 readings of its two premisses. -/
private theorem star10_joinCertified
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r pqFormula prFormula : Formula signature real [] order)
    (pqDisjunctionDefinition : ImplicationDisjunction signature real
      (.neg negation p) q pqFormula)
    (prDisjunctionDefinition : ImplicationDisjunction signature real
      (.neg negation p) r prFormula)
    (line1 : Derivation (.assertion pqFormula))
    (line2 : Derivation (.assertion prFormula)) :
    Derivation (.assertion (implication negation disjunction p
      (conjunction negation disjunction q r))) := by
  let product := conjunction negation disjunction q r
  let qrFormula := implication negation disjunction q
    (implication negation disjunction r product)
  let pToRToProduct := implication negation disjunction p
    (implication negation disjunction r product)
  have productIntroduction := star_3_2 negation disjunction q r
  have firstComposition := star10_composeCertified negation disjunction
    p q (implication negation disjunction r product)
    (.neg negation p) (.neg negation q) pqFormula qrFormula pToRToProduct
    (ImplicationNegation.star_1_01 negation p)
    (ImplicationNegation.star_1_01 negation q)
    pqDisjunctionDefinition
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation q) (implication negation disjunction r product))
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation p) (implication negation disjunction r product))
    line1 productIntroduction
  have commuted := Derivation.star_9_12_same negation disjunction
    firstComposition (star_2_04 negation disjunction p r product)
  let rToPToProduct := implication negation disjunction r
    (implication negation disjunction p product)
  let duplicated := implication negation disjunction p
    (implication negation disjunction p product)
  have secondComposition := star10_composeCertified negation disjunction
    p r (implication negation disjunction p product)
    (.neg negation p) (.neg negation r) prFormula rToPToProduct duplicated
    (ImplicationNegation.star_1_01 negation p)
    (ImplicationNegation.star_1_01 negation r)
    prDisjunctionDefinition
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation r) (implication negation disjunction p product))
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation p) (implication negation disjunction p product))
    line2 commuted
  exact Derivation.star_9_12_same negation disjunction secondComposition
    (star_2_43 negation disjunction p product)

/-- The independently constructed left member `(x).φx .ψx` of ✱10·22. -/
def star_10_22_left
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  star10_stableUniversal (baseOrder := baseOrder) universal
    (conjunction negation disjunction phi psi)

/-- The independently constructed right member `(x).φx : (x).ψx` of ✱10·22. -/
def star_10_22_right
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  conjunction negation disjunction
    (star10_stableUniversal (baseOrder := baseOrder) universal phi)
    (star10_stableUniversal (baseOrder := baseOrder) universal psi)

/-- Audited catalogue reading of ✱10·22.  Expanding ✱4·01 leaves the reverse
implication in its literal ✱9·04 scope tree. -/
def star_10_22_reading
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    ClaimReading signature real where
  printed := "⊢ : .(x).φx .ψx .≡ : (x).φx : (x).ψx"
  parsed := .assertion (conjunction negation disjunction
    (implication negation disjunction
      (star_10_22_left (baseOrder := baseOrder) universal negation disjunction
        phi psi)
      (star_10_22_right (baseOrder := baseOrder) universal negation disjunction
        phi psi))
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction
      (star_10_22_right (baseOrder := baseOrder) universal negation disjunction
        phi psi)
      (conjunction negation disjunction phi psi)))

/-- ✱10·22.  `line1`--`line5` follow the five numbered printed lines;
the final product is the defining expansion of `Prop`/✱4·01.
`demonstration_provenance: follows-printed`. -/
theorem star_10_22
    {baseOrder : Nat}
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Derivation (star_10_22_reading universal negation disjunction
      phi psi).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let product := conjunction negation disjunction phi psi
  let left := star_10_22_left (baseOrder := baseOrder) universal negation
    disjunction phi psi
  let right := star_10_22_right (baseOrder := baseOrder) universal negation
    disjunction phi psi
  have leftWeaken : left.weakenReal (fresh := argument) =
      star10_stableUniversal (baseOrder := baseOrder) universal
        (conjunction negation disjunction
          (phi.weakenReal (fresh := argument))
          (psi.weakenReal (fresh := argument))) := by
    unfold left star_10_22_left
    rw [star10_stableUniversal_weakenReal (baseOrder := baseOrder),
      star_10_35_conjunction_weakenReal]
  have rightWeaken : right.weakenReal (fresh := argument) =
      conjunction negation disjunction
        (star10_stableUniversal (baseOrder := baseOrder) universal
          (phi.weakenReal (fresh := argument)))
        (star10_stableUniversal (baseOrder := baseOrder) universal
          (psi.weakenReal (fresh := argument))) := by
    unfold right star_10_22_right
    rw [star_10_35_conjunction_weakenReal,
      star10_stableUniversal_weakenReal (baseOrder := baseOrder),
      star10_stableUniversal_weakenReal (baseOrder := baseOrder)]
  have productAtValue :
      (conjunction negation disjunction
        phi.weakenReal psi.weakenReal).instantiate value =
      conjunction negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value) := by
    unfold Formula.instantiate
    rw [star_10_35_conjunction_substitute]
  have line1 : Derivation (.assertion (implication negation disjunction
      left.weakenReal
      (conjunction negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value)))) := by
    have specialization := star10_stableSpecialize universal negation
      disjunction (conjunction negation disjunction
        phi.weakenReal psi.weakenReal) value
    rw [← leftWeaken, productAtValue] at specialization
    exact specialization
  have line2 : Derivation (.assertion
      (star_10_21_stable_right universal negation disjunction left phi)) := by
    have pointwise := star10_composeCertified negation disjunction
      left.weakenReal
      (conjunction negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value))
      (phi.weakenReal.instantiate value)
      (.neg negation left.weakenReal)
      (.neg negation (conjunction negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value)))
      (implication negation disjunction left.weakenReal
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
      (implication negation disjunction
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value))
      (implication negation disjunction left.weakenReal
        (phi.weakenReal.instantiate value))
      (ImplicationNegation.star_1_01 negation left.weakenReal)
      (ImplicationNegation.star_1_01 negation
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation left.weakenReal)
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
        (phi.weakenReal.instantiate value))
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation left.weakenReal)
        (phi.weakenReal.instantiate value))
      line1 (star_3_26 negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value))
    have generalized := star10_stableGeneralizeImplication
      (baseOrder := baseOrder) universal
      negation disjunction left phi pointwise
    exact star10_applyStableScope (baseOrder := baseOrder) universal negation
      disjunction left phi
      generalized
  have line3 : Derivation (.assertion
      (star_10_21_stable_right universal negation disjunction left psi)) := by
    have pointwise := star10_composeCertified negation disjunction
      left.weakenReal
      (conjunction negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value))
      (psi.weakenReal.instantiate value)
      (.neg negation left.weakenReal)
      (.neg negation (conjunction negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value)))
      (implication negation disjunction left.weakenReal
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
      (implication negation disjunction
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value))
        (psi.weakenReal.instantiate value))
      (implication negation disjunction left.weakenReal
        (psi.weakenReal.instantiate value))
      (ImplicationNegation.star_1_01 negation left.weakenReal)
      (ImplicationNegation.star_1_01 negation
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation left.weakenReal)
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation (conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value)))
        (psi.weakenReal.instantiate value))
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation left.weakenReal)
        (psi.weakenReal.instantiate value))
      line1 (star_3_27 negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value))
    have generalized := star10_stableGeneralizeImplication
      (baseOrder := baseOrder) universal
      negation disjunction left psi pointwise
    exact star10_applyStableScope (baseOrder := baseOrder) universal negation
      disjunction left psi
      generalized
  have line4 : Derivation (.assertion (implication negation disjunction
      left right)) := by
    unfold right star_10_22_right
    exact star10_joinCertified negation disjunction left
      (star10_stableUniversal universal phi)
      (star10_stableUniversal universal psi)
      (star_10_21_stable_right universal negation disjunction left phi)
      (star_10_21_stable_right universal negation disjunction left psi)
      (star10_stableScopeDisjunction universal negation disjunction left phi)
      (star10_stableScopeDisjunction universal negation disjunction left psi)
      line2 line3
  have line5 : Derivation (.assertion
      (star_10_21_stable_right universal negation disjunction right product)) := by
    have pointwiseRaw := star_10_14 universal negation disjunction
      phi.weakenReal psi.weakenReal value
    change Derivation (.assertion (implication negation disjunction
      (conjunction negation disjunction
        (star10_stableUniversal universal phi.weakenReal)
        (star10_stableUniversal universal psi.weakenReal))
      (conjunction negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value)))) at pointwiseRaw
    rw [← rightWeaken] at pointwiseRaw
    have productWeakenAtValue : product.weakenReal.instantiate value =
        conjunction negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value) := by
      unfold product
      rw [star_10_35_conjunction_weakenReal]
      exact productAtValue
    have pointwise : Derivation (.assertion
        (implication negation disjunction right.weakenReal
          (product.weakenReal.instantiate value))) :=
      Derivation.castAssertion
        (congrArg (fun consequent => implication negation disjunction
          right.weakenReal consequent) productWeakenAtValue)
        pointwiseRaw
    have generalized := star10_stableGeneralizeImplication
      (baseOrder := baseOrder) universal
      negation disjunction right product pointwise
    exact star10_applyStableScope (baseOrder := baseOrder) universal negation
      disjunction right product
      generalized
  unfold star_10_22_reading
  exact star_10_13 negation disjunction
    (implication negation disjunction left right)
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction right product)
    line4 line5

/-! ## ✱10·27 at stable order and ✱10·271 -/

def star_10_27_saturated_left
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  star10_stableUniversal (baseOrder := baseOrder) universal
    (implication negation disjunction phi psi)

def star_10_27_saturated_right
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  implication negation disjunction
    (star10_stableUniversal (baseOrder := baseOrder) universal phi)
    (star10_stableUniversal (baseOrder := baseOrder) universal psi)

def star_10_27_saturated_reading
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    ClaimReading signature real where
  printed := "⊢ : .(z).φz ⊃ ψz .⊃ : (z).φz .⊃ .(z).ψz"
  parsed := .assertion (implication negation disjunction
    (star_10_27_saturated_left (baseOrder := baseOrder) universal negation
      disjunction phi psi)
    (star_10_27_saturated_right (baseOrder := baseOrder) universal negation
      disjunction phi psi))

/-- The stable-order instance of ✱10·27, following its printed
✱10·14/`Ass`/✱10·11·21/`Exp` route.
`demonstration_provenance: follows-printed`. -/
theorem star_10_27_saturated
    {baseOrder : Nat}
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Derivation (star_10_27_saturated_reading universal negation disjunction
      phi psi).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let forward := implication negation disjunction phi psi
  let universalForward := star10_stableUniversal (baseOrder := baseOrder)
    universal forward
  let universalPhi := star10_stableUniversal (baseOrder := baseOrder)
    universal phi
  let universalPsi := star10_stableUniversal (baseOrder := baseOrder)
    universal psi
  let product := conjunction negation disjunction universalForward universalPhi
  have productWeaken : product.weakenReal (fresh := argument) =
      conjunction negation disjunction
        (star10_stableUniversal (baseOrder := baseOrder) universal
          (implication negation disjunction
            (phi.weakenReal (fresh := argument))
            (psi.weakenReal (fresh := argument))))
        (star10_stableUniversal (baseOrder := baseOrder) universal
          (phi.weakenReal (fresh := argument))) := by
    unfold product universalForward universalPhi forward
    rw [star_10_35_conjunction_weakenReal,
      star10_stableUniversal_weakenReal (baseOrder := baseOrder),
      implication_weakenReal,
      star10_stableUniversal_weakenReal (baseOrder := baseOrder)]
  have forwardAtValue :
      (implication negation disjunction
        phi.weakenReal psi.weakenReal).instantiate value =
      implication negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value) := by
    unfold Formula.instantiate
    rw [implication_substitute]
  have line1 : Derivation (.assertion (implication negation disjunction
      product.weakenReal
      (conjunction negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value)))) := by
    have printedLine := star_10_14 (baseOrder := baseOrder) universal negation
      disjunction
      (implication negation disjunction phi.weakenReal psi.weakenReal)
      phi.weakenReal value
    change Derivation (.assertion (implication negation disjunction
      (conjunction negation disjunction
        (star10_stableUniversal (baseOrder := baseOrder) universal
          (implication negation disjunction phi.weakenReal psi.weakenReal))
        (star10_stableUniversal (baseOrder := baseOrder) universal
          phi.weakenReal))
      (conjunction negation disjunction
        ((implication negation disjunction
          phi.weakenReal psi.weakenReal).instantiate value)
        (phi.weakenReal.instantiate value)))) at printedLine
    rw [← productWeaken, forwardAtValue] at printedLine
    exact printedLine
  have line2 : Derivation (.assertion (implication negation disjunction
      (conjunction negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value)
          (psi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value))
      (psi.weakenReal.instantiate value))) := by
    have permutation := star_3_22 negation disjunction
      (implication negation disjunction
        (phi.weakenReal.instantiate value)
        (psi.weakenReal.instantiate value))
      (phi.weakenReal.instantiate value)
    have assertion := star_3_35 negation disjunction
      (phi.weakenReal.instantiate value)
      (psi.weakenReal.instantiate value)
    exact star10_composeSame negation disjunction _ _ _ permutation assertion
  have line3 := star10_composeSame negation disjunction _ _ _ line1 line2
  have line4Left := star10_stableGeneralizeImplication
    (baseOrder := baseOrder) universal negation
    disjunction product psi line3
  have line4 := star10_applyStableScope (baseOrder := baseOrder) universal
    negation disjunction
    product psi line4Left
  have line5 := star10_exportCertified negation disjunction
    universalForward universalPhi universalPsi
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction product psi)
    (star10_stableScopeDisjunction (baseOrder := baseOrder) universal negation
      disjunction product psi)
    line4
  unfold star_10_27_saturated_reading star_10_27_saturated_left
    star_10_27_saturated_right
  exact line5

/-- The least stable-order presentation retained for existing ✱11 callers. -/
def star_10_27_stable_left
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi : Formula signature real [argument] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  star_10_27_saturated_left (baseOrder := 0) universal negation disjunction
    phi psi

def star_10_27_stable_right
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi : Formula signature real [argument] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  star_10_27_saturated_right (baseOrder := 0) universal negation disjunction
    phi psi

def star_10_27_stable_reading
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi : Formula signature real [argument] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "⊢ : .(z).φz ⊃ ψz .⊃ : (z).φz .⊃ .(z).ψz"
  parsed := .assertion (implication negation disjunction
    (star_10_27_stable_left universal negation disjunction phi psi)
    (star_10_27_stable_right universal negation disjunction phi psi))

/-- The least stable-order specialization of the saturated ✱10·27 family.
`demonstration_provenance: follows-printed`. -/
theorem star_10_27_stable
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi : Formula signature real [argument] (Nat.succ argument.height)) :
    Derivation (star_10_27_stable_reading universal negation disjunction
      phi psi).parsed := by
  have line1 := star_10_27_saturated (baseOrder := 0) universal negation
    disjunction phi psi
  exact line1

/-- The independently constructed antecedent `(z).φz≡ψz` of ✱10·271. -/
def star_10_271_left
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  star10_stableUniversal (baseOrder := baseOrder) universal
    (conjunction negation disjunction
      (implication negation disjunction phi psi)
      (implication negation disjunction psi phi))

/-- The independently constructed consequent `(z).φz≡(z).ψz` of ✱10·271. -/
def star_10_271_right
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Formula signature real [] (bindOrder baseOrder argument) :=
  star_4_01 negation disjunction
    (star10_stableUniversal (baseOrder := baseOrder) universal phi)
    (star10_stableUniversal (baseOrder := baseOrder) universal psi)

def star_10_271_reading
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    ClaimReading signature real where
  printed := "⊢ : .(z).φz ≡ ψz .⊃ : (z).φz .≡.(z).ψz"
  parsed := .assertion (implication negation disjunction
    (star_10_271_left universal negation disjunction phi psi)
    (star_10_271_right universal negation disjunction phi psi))

/-- ✱10·271.  Lines (1) and (2) use ✱10·22 followed by the two orientations
of ✱10·27; `line3` is the printed `Comp`.
`demonstration_provenance: follows-printed`. -/
theorem star_10_271
    {baseOrder : Nat}
    (universal : signature.Universal argument (bindOrder baseOrder argument))
    (negation : signature.Negation (bindOrder baseOrder argument))
    (disjunction : signature.Disjunction (bindOrder baseOrder argument))
    (phi psi : Formula signature real [argument]
      (bindOrder baseOrder argument)) :
    Derivation (star_10_271_reading universal negation disjunction
      phi psi).parsed := by
  let forward := implication negation disjunction phi psi
  let reverse := implication negation disjunction psi phi
  let hypothesis := star_10_271_left universal negation disjunction phi psi
  let universalForward := star10_stableUniversal (baseOrder := baseOrder)
    universal forward
  let universalReverse := star10_stableUniversal (baseOrder := baseOrder)
    universal reverse
  let universalPhi := star10_stableUniversal (baseOrder := baseOrder)
    universal phi
  let universalPsi := star10_stableUniversal (baseOrder := baseOrder)
    universal psi
  let pair := conjunction negation disjunction universalForward universalReverse
  have distribution := star_10_22 (baseOrder := baseOrder) universal negation
    disjunction forward reverse
  unfold star_10_22_reading at distribution
  change Derivation (.assertion (conjunction negation disjunction
    (implication negation disjunction hypothesis pair)
    (star_10_21_stable_right (baseOrder := baseOrder) universal negation
      disjunction pair
      (conjunction negation disjunction forward reverse)))) at distribution
  have distributionForward := Derivation.star_9_12_same negation disjunction
    distribution
    (star_3_26 negation disjunction
      (implication negation disjunction hypothesis pair)
      (star_10_21_stable_right (baseOrder := baseOrder) universal negation
        disjunction pair
        (conjunction negation disjunction forward reverse)))
  have line1a := star10_composeSame negation disjunction hypothesis pair
    universalForward distributionForward
    (star_3_26 negation disjunction universalForward universalReverse)
  have line1 := star10_composeSame negation disjunction hypothesis
    universalForward (implication negation disjunction universalPhi universalPsi)
    line1a (star_10_27_saturated (baseOrder := baseOrder) universal negation
      disjunction phi psi)
  have line2a := star10_composeSame negation disjunction hypothesis pair
    universalReverse distributionForward
    (star_3_27 negation disjunction universalForward universalReverse)
  have line2 := star10_composeSame negation disjunction hypothesis
    universalReverse (implication negation disjunction universalPsi universalPhi)
    line2a (star_10_27_saturated (baseOrder := baseOrder) universal negation
      disjunction psi phi)
  have line3 := star10_joinCertified negation disjunction hypothesis
    (implication negation disjunction universalPhi universalPsi)
    (implication negation disjunction universalPsi universalPhi)
    (implication negation disjunction hypothesis
      (implication negation disjunction universalPhi universalPsi))
    (implication negation disjunction hypothesis
      (implication negation disjunction universalPsi universalPhi))
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation hypothesis)
      (implication negation disjunction universalPhi universalPsi))
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation hypothesis)
      (implication negation disjunction universalPsi universalPhi))
    line1 line2
  unfold star_10_271_reading star_10_271_right star_4_01
  exact line3

/-! ## ✱10·301--·32 -/

/-- Audited catalogue reading of ✱10·301.  The final implication retains
the ✱10·21 scope tree used in PM's printed ✱10·22 step. -/
def star_10_301_reading
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi chi :
      Formula signature real [argument] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "✱10·301.  ⊢ : .(x).φx≡ψx : (x).ψx≡χx : ⊃ .(x).φx≡χx"
  parsed := .assertion
    (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
      (conjunction negation disjunction
        (star10_stableUniversal (baseOrder := 0) universal
          (equivalence negation disjunction phi psi))
        (star10_stableUniversal (baseOrder := 0) universal
          (equivalence negation disjunction psi chi)))
      (equivalence negation disjunction phi chi))

/-- ✱10·301.  `line1` and `line2` are the cited ✱10·22 consequence;
`line3`--`line5` are ✱4·22 followed by ✱10·11 and ✱10·27, and `line6`
is the printed propositional composition.
`demonstration_provenance: follows-printed`. -/
theorem star_10_301
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi chi :
      Formula signature real [argument] (Nat.succ argument.height)) :
    Derivation (star_10_301_reading universal negation disjunction
      phi psi chi).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let phiPsi := equivalence negation disjunction phi psi
  let psiChi := equivalence negation disjunction psi chi
  let phiChi := equivalence negation disjunction phi chi
  let pair := conjunction negation disjunction phiPsi psiChi
  let hypothesis := conjunction negation disjunction
    (star10_stableUniversal (baseOrder := 0) universal phiPsi)
    (star10_stableUniversal (baseOrder := 0) universal psiChi)
  have line1 := star_10_22 (baseOrder := 0) universal negation disjunction
    phiPsi psiChi
  unfold star_10_22_reading at line1
  change Derivation (.assertion (conjunction negation disjunction
    (implication negation disjunction
      (star10_stableUniversal (baseOrder := 0) universal pair) hypothesis)
    (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
      hypothesis pair))) at line1
  have line2 := Derivation.star_9_12_same negation disjunction line1
    (star_3_27 negation disjunction
      (implication negation disjunction
        (star10_stableUniversal (baseOrder := 0) universal pair) hypothesis)
      (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
        hypothesis pair))
  have line3 : Derivation (.assertion
      (star10_stableUniversal (baseOrder := 0) universal
        (implication negation disjunction pair phiChi))) := by
    apply star10_stableGeneralize (baseOrder := 0)
    apply Derivation.castAssertion
      (congrArg (fun formula => formula.instantiate value)
        (implication_weakenReal (fresh := argument) negation disjunction
          pair phiChi))
    change Derivation (.assertion ((implication negation disjunction
      pair.weakenReal phiChi.weakenReal).instantiate value))
    unfold pair
    rw [star_10_35_conjunction_weakenReal negation disjunction phiPsi psiChi]
    unfold phiPsi psiChi phiChi
    rw [star10_matrixEquivalence_weakenReal negation disjunction phi psi,
      star10_matrixEquivalence_weakenReal negation disjunction psi chi,
      star10_matrixEquivalence_weakenReal negation disjunction phi chi,
      Formula.instantiate, implication_substitute,
      star_10_35_conjunction_substitute,
      star10_matrixEquivalence_substitute,
      star10_matrixEquivalence_substitute,
      star10_matrixEquivalence_substitute]
    exact star_4_22 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line4 := star_10_27_stable universal negation
    disjunction pair phiChi
  unfold star_10_27_stable_reading star_10_27_stable_left
    star_10_27_stable_right at line4
  have line5 := detach negation disjunction _ _ line3 line4
  have line6 := star10_composeCertified negation disjunction
    hypothesis (star10_stableUniversal (baseOrder := 0) universal pair)
    (star10_stableUniversal (baseOrder := 0) universal phiChi)
    (.neg negation hypothesis)
    (.neg negation (star10_stableUniversal (baseOrder := 0) universal pair))
    (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
      hypothesis pair)
    (implication negation disjunction
      (star10_stableUniversal (baseOrder := 0) universal pair)
      (star10_stableUniversal (baseOrder := 0) universal phiChi))
    (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
      hypothesis phiChi)
    (ImplicationNegation.star_1_01 negation hypothesis)
    (ImplicationNegation.star_1_01 negation
      (star10_stableUniversal (baseOrder := 0) universal pair))
    (star10_stableScopeDisjunction (baseOrder := 0) universal negation disjunction
      hypothesis pair)
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation (star10_stableUniversal (baseOrder := 0) universal pair))
      (star10_stableUniversal (baseOrder := 0) universal phiChi))
    (star10_stableScopeDisjunction (baseOrder := 0) universal negation disjunction
      hypothesis phiChi)
    line2 line5
  unfold star_10_301_reading
  exact line6

/-- Audited catalogue reading of ✱10·31. -/
def star_10_31_reading
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi chi :
      Formula signature real [argument] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "✱10·31.  ⊢ : .(x).φx⊃ψx .⊃ : (x) : φx .χx .⊃ .ψx .χx"
  parsed := .assertion (implication negation disjunction
    (star10_stableUniversal (baseOrder := 0) universal
      (implication negation disjunction phi psi))
    (star10_stableUniversal (baseOrder := 0) universal
      (implication negation disjunction
        (conjunction negation disjunction phi chi)
        (conjunction negation disjunction psi chi))))

/-- ✱10·31, by the printed `Fact`, ✱10·11 and ✱10·27 chain.
`demonstration_provenance: follows-printed`. -/
theorem star_10_31
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi chi :
      Formula signature real [argument] (Nat.succ argument.height)) :
    Derivation (star_10_31_reading universal negation disjunction
      phi psi chi).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let forward := implication negation disjunction phi psi
  let consequence := implication negation disjunction
    (conjunction negation disjunction phi chi)
    (conjunction negation disjunction psi chi)
  have line1 : Derivation (.assertion
      (star10_stableUniversal (baseOrder := 0) universal
        (implication negation disjunction forward consequence))) := by
    apply star10_stableGeneralize (baseOrder := 0)
    apply Derivation.castAssertion
      (congrArg (fun formula => formula.instantiate value)
        (implication_weakenReal (fresh := argument) negation disjunction
          forward consequence))
    change Derivation (.assertion ((implication negation disjunction
      forward.weakenReal consequence.weakenReal).instantiate value))
    unfold forward consequence
    rw [implication_weakenReal negation disjunction phi psi,
      implication_weakenReal negation disjunction
        (conjunction negation disjunction phi chi)
        (conjunction negation disjunction psi chi),
      star_10_35_conjunction_weakenReal negation disjunction phi chi,
      star_10_35_conjunction_weakenReal negation disjunction psi chi,
      Formula.instantiate, implication_substitute,
      implication_substitute, implication_substitute,
      star_10_35_conjunction_substitute,
      star_10_35_conjunction_substitute]
    exact star_3_45 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := star_10_27_stable universal negation disjunction
    forward consequence
  unfold star_10_27_stable_reading star_10_27_stable_left
    star_10_27_stable_right at line2
  have line3 := detach negation disjunction _ _ line1 line2
  unfold star_10_31_reading
  exact line3

/-- Audited catalogue reading of ✱10·311. -/
def star_10_311_reading
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi chi :
      Formula signature real [argument] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "✱10·311.  ⊢ : .(x).φx≡ψx .⊃ : (x) : φx .χx .≡ .ψx .χx"
  parsed := .assertion (implication negation disjunction
    (star10_stableUniversal (baseOrder := 0) universal
      (equivalence negation disjunction phi psi))
    (star10_stableUniversal (baseOrder := 0) universal
      (equivalence negation disjunction
        (conjunction negation disjunction phi chi)
        (conjunction negation disjunction psi chi))))

/-- ✱10·311, by the printed ✱4·36, ✱10·11 and ✱10·27 chain.
`demonstration_provenance: follows-printed`. -/
theorem star_10_311
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi chi :
      Formula signature real [argument] (Nat.succ argument.height)) :
    Derivation (star_10_311_reading universal negation disjunction
      phi psi chi).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let antecedent := equivalence negation disjunction phi psi
  let consequence := equivalence negation disjunction
    (conjunction negation disjunction phi chi)
    (conjunction negation disjunction psi chi)
  have line1 : Derivation (.assertion
      (star10_stableUniversal (baseOrder := 0) universal
        (implication negation disjunction antecedent consequence))) := by
    apply star10_stableGeneralize (baseOrder := 0)
    apply Derivation.castAssertion
      (congrArg (fun formula => formula.instantiate value)
        (implication_weakenReal (fresh := argument) negation disjunction
          antecedent consequence))
    change Derivation (.assertion ((implication negation disjunction
      antecedent.weakenReal consequence.weakenReal).instantiate value))
    unfold antecedent consequence
    rw [star10_matrixEquivalence_weakenReal negation disjunction phi psi,
      star10_matrixEquivalence_weakenReal negation disjunction
        (conjunction negation disjunction phi chi)
        (conjunction negation disjunction psi chi),
      star_10_35_conjunction_weakenReal negation disjunction phi chi,
      star_10_35_conjunction_weakenReal negation disjunction psi chi,
      Formula.instantiate, implication_substitute,
      star10_matrixEquivalence_substitute,
      star10_matrixEquivalence_substitute,
      star_10_35_conjunction_substitute,
      star_10_35_conjunction_substitute]
    exact star_4_36 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := star_10_27_stable universal negation disjunction
    antecedent consequence
  unfold star_10_27_stable_reading star_10_27_stable_left
    star_10_27_stable_right at line2
  have line3 := detach negation disjunction _ _ line1 line2
  unfold star_10_311_reading
  exact line3

private theorem star10_bindOrderAbsorbMatrix
    (matrixOrder : Nat) (argument : RSort) :
    max (bindOrder matrixOrder argument) matrixOrder =
      bindOrder matrixOrder argument := by
  rw [bindOrderMaxRight, natMaxSelf]

private theorem star10_bindOrderIdempotent
    (matrixOrder : Nat) (argument : RSort) :
    bindOrder (bindOrder matrixOrder argument) argument =
      bindOrder matrixOrder argument := by
  unfold bindOrder
  exact MixedOrder.maxRightAbsorb matrixOrder (Nat.succ argument.height)

private def star10_boundImplication
    (orderEquality : max leftOrder rightOrder = resultOrder)
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    Formula signature real apparent resultOrder :=
  Eq.mp (congrArg (Formula signature real apparent) orderEquality)
    (mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction orderEquality.symm) disjunction)
      left right)

private theorem star10_boundImplication_weakenReal
    (orderEquality : max leftOrder rightOrder = resultOrder)
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    (star10_boundImplication orderEquality negation disjunction
      left right).weakenReal (fresh := fresh) =
      star10_boundImplication orderEquality negation disjunction
        left.weakenReal right.weakenReal := by
  cases orderEquality
  rfl

private theorem star10_boundImplication_substitute
    (orderEquality : max leftOrder rightOrder = resultOrder)
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real source leftOrder)
    (right : Formula signature real source rightOrder)
    (sigma : Substitution signature real source target) :
    (star10_boundImplication orderEquality negation disjunction
      left right).substitute sigma =
      star10_boundImplication orderEquality negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  cases orderEquality
  rfl

private theorem star10_uncastAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) equality) formula)) →
      Derivation (.assertion formula) := by
  cases equality
  exact fun derivation => derivation

private def star10_castImplicationDisjunctionResult
    (equality : sourceOrder = targetOrder)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder)
    (result : Formula signature real apparent sourceOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real left right
      (Eq.mp (congrArg (Formula signature real apparent) equality) result) := by
  cases equality
  exact reading

private theorem star10_ternarySyll
    (negation : MixedOrder.TernaryNegations signature)
    (disjunction : MixedOrder.TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (line1 : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))))
    (line2 : Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR)))) :
    Derivation (.assertion
      (MixedOrder.ternaryInterpret negation disjunction p q r
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR))) := by
  have line3 := MixedOrder.ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star2.star_2_05 MixedOrder.ternaryP
      MixedOrder.ternaryQ MixedOrder.ternaryR)
  have line4 := MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .qr .pqr)
    negation.qr disjunction.pqr
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR))
    (MixedOrder.ternaryInterpret negation disjunction p q r
      ((MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ) ⊃ₚ
        (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR))) line2 line3
  exact MixedOrder.detach
    (MixedOrder.ternaryOrderCombine negation .pq .pr)
    negation.pq disjunction.pqr
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))
    (MixedOrder.ternaryInterpret negation disjunction p q r
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryR)) line1 line4

private theorem star10_generalFormalDirection
    (universal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (bindOrder matrixOrder argument))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder matrixOrder argument))
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (.assertion (implication outerNegation outerDisjunction
      (.always universal (equivalence matrixNegation matrixDisjunction phi psi))
      (.always universal (equivalence matrixNegation matrixDisjunction psi phi)))) := by
  let boundOrder := bindOrder matrixOrder argument
  let boundMatrixEquality := star10_bindOrderAbsorbMatrix matrixOrder argument
  let boundEquality := star10_bindOrderIdempotent matrixOrder argument
  let matrixSelfEquality := natMaxSelf matrixOrder
  let fullEquality : max boundOrder (max matrixOrder matrixOrder) = boundOrder :=
    Eq.trans (congrArg (max boundOrder) matrixSelfEquality) boundMatrixEquality
  let mixedDisjunction := Eq.mp
    (congrArg signature.Disjunction boundMatrixEquality.symm) outerDisjunction
  let phiPsi := equivalence matrixNegation matrixDisjunction phi psi
  let psiPhi := equivalence matrixNegation matrixDisjunction psi phi
  let left := Formula.always universal phiPsi
  let right := Formula.always universal psiPhi
  let value : Term signature (argument :: real) [] argument := .real .zero
  let phiInstance := phi.weakenReal.substitute (instantiateSubstitution value)
  let psiInstance := psi.weakenReal.substitute (instantiateSubstitution value)
  let phiPsiInstance := equivalence matrixNegation matrixDisjunction
    phiInstance psiInstance
  let psiPhiInstance := equivalence matrixNegation matrixDisjunction
    psiInstance phiInstance
  let orderVocabulary : MixedOrder.TernaryNegations signature := {
    pOrder := boundOrder
    qOrder := matrixOrder
    rOrder := matrixOrder
    p := outerNegation
    q := matrixNegation
    r := matrixNegation
    pq := Eq.mp (congrArg signature.Negation boundMatrixEquality.symm)
      outerNegation
    pr := Eq.mp (congrArg signature.Negation boundMatrixEquality.symm)
      outerNegation
    qr := Eq.mp (congrArg signature.Negation matrixSelfEquality.symm)
      matrixNegation
    pqr := Eq.mp (congrArg signature.Negation fullEquality.symm)
      outerNegation
  }
  let connectiveVocabulary : MixedOrder.TernaryDisjunctions signature
      orderVocabulary := {
    p := outerDisjunction
    q := matrixDisjunction
    r := matrixDisjunction
    pq := mixedDisjunction
    pr := mixedDisjunction
    qr := Eq.mp (congrArg signature.Disjunction matrixSelfEquality.symm)
      matrixDisjunction
    pqr := Eq.mp (congrArg signature.Disjunction fullEquality.symm)
      outerDisjunction
  }
  have line1 := Derivation.star_10_1 universal outerNegation mixedDisjunction
    phiPsi.weakenReal value
  have line2 :
      (phiPsi.weakenReal.instantiate value) = phiPsiInstance := by
    unfold phiPsi phiPsiInstance
    rw [star10_matrixEquivalence_weakenReal, Formula.instantiate,
      star10_matrixEquivalence_substitute]
  have line3 : Derivation (.assertion
      (mixedImplication outerNegation mixedDisjunction left.weakenReal
        phiPsiInstance)) :=
    Derivation.castAssertion
      (congrArg (mixedImplication outerNegation mixedDisjunction
        left.weakenReal) line2.symm) line1
  change Derivation (.assertion
    (MixedOrder.ternaryInterpret orderVocabulary connectiveVocabulary
      left.weakenReal phiPsiInstance psiPhiInstance
      (MixedOrder.ternaryP ⊃ₚ MixedOrder.ternaryQ))) at line3
  have line4 := star_4_21 matrixNegation matrixDisjunction
    phiInstance psiInstance
  have line5 := Derivation.star_9_12_same matrixNegation matrixDisjunction
    line4 (star_3_26 matrixNegation matrixDisjunction
      (implication matrixNegation matrixDisjunction
        phiPsiInstance psiPhiInstance)
      (implication matrixNegation matrixDisjunction
        psiPhiInstance phiPsiInstance))
  have line6 := Derivation.castAssertion
    (mixedImplication_normalizeSameOrder rfl rfl matrixNegation
      matrixDisjunction phiPsiInstance psiPhiInstance) line5
  have line7 := star10_uncastAssertionOrder matrixSelfEquality
    (mixedImplication matrixNegation
      (Eq.mp (congrArg signature.Disjunction matrixSelfEquality.symm)
        matrixDisjunction) phiPsiInstance psiPhiInstance) line6
  change Derivation (.assertion
    (MixedOrder.ternaryInterpret orderVocabulary connectiveVocabulary
      left.weakenReal phiPsiInstance psiPhiInstance
      (MixedOrder.ternaryQ ⊃ₚ MixedOrder.ternaryR))) at line7
  have line8 := star10_ternarySyll orderVocabulary connectiveVocabulary
    left.weakenReal phiPsiInstance psiPhiInstance line3 line7
  change Derivation (.assertion
    (mixedImplication outerNegation mixedDisjunction
      left.weakenReal psiPhiInstance)) at line8
  have line9 := star10_castAssertionOrder boundMatrixEquality
    (mixedImplication outerNegation mixedDisjunction
      left.weakenReal psiPhiInstance) line8
  let scopeBody := star10_boundImplication boundMatrixEquality
    outerNegation outerDisjunction (left.rename (fun v => .succ v)) psiPhi
  have line10 : Derivation (.assertion
      (scopeBody.weakenReal.instantiate value)) := by
    unfold scopeBody
    rw [star10_boundImplication_weakenReal,
      Formula.instantiate, star10_boundImplication_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      star10_matrixEquivalence_weakenReal,
      star10_matrixEquivalence_substitute]
    exact line9
  have line11 := star_10_11 scopeUniversal scopeBody line10
  let scopedFormula := Eq.mp
    (congrArg (Formula signature real []) boundEquality)
    (.always scopeUniversal scopeBody)
  have line12 : Derivation (.assertion scopedFormula) :=
    star10_castAssertionOrder boundEquality
      (.always scopeUniversal scopeBody) line11
  let line13 : ImplicationDisjunction signature real
      (Formula.neg outerNegation left) right scopedFormula := by
    let line11a : ImplicationDisjunction signature real
        ((Formula.neg outerNegation left).rename (fun v => .succ v)) psiPhi
        scopeBody := by
      unfold scopeBody star10_boundImplication
      exact star10_castImplicationDisjunctionResult boundMatrixEquality
        ((Formula.neg outerNegation left).rename (fun v => .succ v)) psiPhi
        (.disj mixedDisjunction
          ((Formula.neg outerNegation left).rename (fun v => .succ v)) psiPhi)
        (ImplicationDisjunction.star_1_01 mixedDisjunction
          ((Formula.neg outerNegation left).rename (fun v => .succ v)) psiPhi)
    let line11b : ImplicationDisjunction signature real
        (Formula.neg outerNegation left) right
          (.always scopeUniversal scopeBody) :=
      ImplicationDisjunction.star_9_04 universal scopeUniversal
        (Formula.neg outerNegation left) psiPhi scopeBody line11a
    exact star10_castImplicationDisjunctionResult boundEquality
      (Formula.neg outerNegation left) right
      (.always scopeUniversal scopeBody) line11b
  have line14 := star10_composeCertified outerNegation outerDisjunction
    left left right
    (.neg outerNegation left) (.neg outerNegation left)
    (implication outerNegation outerDisjunction left left)
    scopedFormula
    (implication outerNegation outerDisjunction left right)
    (ImplicationNegation.star_1_01 outerNegation left)
    (ImplicationNegation.star_1_01 outerNegation left)
    (ImplicationDisjunction.star_1_01_same outerDisjunction
      (.neg outerNegation left) left)
    line13
    (ImplicationDisjunction.star_1_01_same outerDisjunction
      (.neg outerNegation left) right)
    (star_2_08 outerNegation outerDisjunction left) line12
  exact line14

/-- Audited catalogue reading of ✱10·32, generalized over the matrix order.
The second universal is the scope meaning required by the printed ✱10·271
transport once the first quantifier has raised the assigned order. -/
def star_10_32_reading
    (universal : signature.Universal argument matrixOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder matrixOrder argument))
    (phi psi : Formula signature real [argument] matrixOrder) :
    ClaimReading signature real where
  printed := "✱10·32. ⊢:φ x≡ₓψ x.≡.ψ x≡ₓφ x"
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (.always universal (equivalence matrixNegation matrixDisjunction phi psi))
    (.always universal (equivalence matrixNegation matrixDisjunction psi phi)))

/-- ✱10·32.  Each direction generalizes ✱4·21 by ✱10·11 and the
general-order form of the ✱10·271 transport; ✱10·13 joins both directions.
`demonstration_provenance: follows-printed`. -/
theorem star_10_32
    (universal : signature.Universal argument matrixOrder)
    (scopeUniversal : signature.Universal argument
      (bindOrder matrixOrder argument))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder matrixOrder argument))
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (star_10_32_reading universal matrixNegation
      matrixDisjunction outerNegation outerDisjunction phi psi).parsed := by
  have line1 := star10_generalFormalDirection universal scopeUniversal
    matrixNegation matrixDisjunction outerNegation outerDisjunction phi psi
  have line2 := star10_generalFormalDirection universal scopeUniversal
    matrixNegation matrixDisjunction outerNegation outerDisjunction psi phi
  have line3 := star_10_13 outerNegation outerDisjunction
    (implication outerNegation outerDisjunction
      (.always universal (equivalence matrixNegation matrixDisjunction phi psi))
      (.always universal (equivalence matrixNegation matrixDisjunction psi phi)))
    (implication outerNegation outerDisjunction
      (.always universal (equivalence matrixNegation matrixDisjunction psi phi))
      (.always universal (equivalence matrixNegation matrixDisjunction phi psi)))
    line1 line2
  unfold star_10_32_reading star_4_01
  exact line3

/-! ## ✱10·33 -/

/-- Instantiating a closed formula after it has been moved below one
apparent binder returns the original formula. -/
private theorem star10_closed_instantiate
    (p : Formula signature real [] order)
    (value : Term signature real [] argument) :
    (p.rename (fun v => .succ v) :
      Formula signature real [argument] order).instantiate value = p := by
  unfold Formula.instantiate
  rw [Formula.rename_substitute]
  exact Formula.substitute_eq_self p (fun v => nomatch v)

/-- Instantiation distributes over a conjunction whose right member is
independent of the bound variable. -/
private theorem star10_conjunction_instantiate_closedRight
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [argument] order)
    (p : Formula signature real [] order)
    (value : Term signature real [] argument) :
    (conjunction negation disjunction phi
      (p.rename (fun v => .succ v))).instantiate value =
      conjunction negation disjunction (phi.instantiate value) p := by
  unfold Formula.instantiate
  rw [star_10_35_conjunction_substitute]
  exact congrArg (conjunction negation disjunction (phi.instantiate value))
    (star10_closed_instantiate p value)

/-- The independently constructed left member `(x):(phi x . p)` of
✱10·33. -/
def star_10_33_left
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  star10_stableUniversal (baseOrder := 0) universal
    (conjunction negation disjunction phi
      (p.rename (fun v => .succ v)))

/-- The independently constructed right member `(x).phi x : p` of
✱10·33. -/
def star_10_33_right
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  conjunction negation disjunction
    (star10_stableUniversal (baseOrder := 0) universal phi) p

/-- Audited catalogue reading of ✱10·33. -/
def star_10_33_reading
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "✱10·33.  ⊢ : .(x) : φx .p .≡ : (x).φx : p"
  parsed := .assertion (conjunction negation disjunction
    (implication negation disjunction
      (star_10_33_left universal negation disjunction phi p)
      (star_10_33_right universal negation disjunction phi p))
    (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
      (star_10_33_right universal negation disjunction phi p)
      (conjunction negation disjunction phi
        (p.rename (fun v => .succ v)))))

/-- ✱10·33.  `line1`--`line5` are the five numbered lines of the
printed demonstration.
`demonstration_provenance: follows-printed`. -/
theorem star_10_33
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height))
    (witness : Term signature real [] argument) :
    Derivation (star_10_33_reading universal negation disjunction phi p).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let product := conjunction negation disjunction phi
    (p.rename (fun v => .succ v))
  let left := star_10_33_left universal negation disjunction phi p
  let right := star_10_33_right universal negation disjunction phi p
  let leftWeaken : left.weakenReal (fresh := argument) =
      star10_stableUniversal (baseOrder := 0) universal
        (conjunction negation disjunction phi.weakenReal
          ((p.rename (fun v => .succ v)).weakenReal)) := by
    unfold left star_10_33_left
    exact Eq.trans
      (star10_stableUniversal_weakenReal (baseOrder := 0)
        (fresh := argument) universal
        (conjunction negation disjunction phi
          (p.rename (fun v => .succ v))))
      (congrArg (star10_stableUniversal (baseOrder := 0) universal)
        (star_10_35_conjunction_weakenReal (fresh := argument)
          negation disjunction phi (p.rename (fun v => .succ v))))
  let rightWeaken : right.weakenReal (fresh := argument) =
      conjunction negation disjunction
        (star10_stableUniversal (baseOrder := 0) universal phi.weakenReal)
        p.weakenReal := by
    unfold right star_10_33_right
    exact Eq.trans
      (star_10_35_conjunction_weakenReal (fresh := argument) negation
        disjunction (star10_stableUniversal (baseOrder := 0) universal phi) p)
      (congrArg (fun left => conjunction negation disjunction left p.weakenReal)
        (star10_stableUniversal_weakenReal (baseOrder := 0)
          (fresh := argument) universal phi))
  let productAtValue :
      (conjunction negation disjunction phi.weakenReal
        ((p.rename (fun v => .succ v)).weakenReal)).instantiate value =
      conjunction negation disjunction
        (phi.weakenReal.instantiate value) p.weakenReal := by
    unfold Formula.instantiate
    rw [star_10_35_conjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution]
  have line1 : Derivation (.assertion (implication negation disjunction
      left (conjunction negation disjunction
        (phi.instantiate witness) p))) := by
    unfold left star_10_33_left
    rw [← star10_conjunction_instantiate_closedRight negation disjunction
      phi p witness]
    exact star10_stableSpecialize (baseOrder := 0) universal negation
      disjunction product witness
  have line2 : Derivation (.assertion (implication negation disjunction
      left p)) := by
    exact star10_composeSame negation disjunction _ _ _ line1
      (star_3_27 negation disjunction
        (phi.instantiate witness) p)
  have line3 : Derivation (.assertion
      (star_10_21_stable_right (baseOrder := 0) universal negation
        disjunction left phi)) := by
    let specializationRaw := star10_stableSpecialize (baseOrder := 0)
      universal negation
      disjunction
      (conjunction negation disjunction phi.weakenReal
        ((p.rename (fun v => .succ v)).weakenReal)) value
    let specialization := Derivation.castAssertion
      (congrArg (fun consequent => implication negation disjunction
        (star10_stableUniversal (baseOrder := 0) universal
          (conjunction negation disjunction phi.weakenReal
            ((p.rename (fun v => .succ v)).weakenReal))) consequent)
        productAtValue).symm
      specializationRaw
    let pointwiseRaw := star10_composeSame negation disjunction _ _ _
      specialization
      (star_3_26 negation disjunction
        (phi.weakenReal.instantiate value) p.weakenReal)
    let pointwise : Derivation (.assertion (implication negation disjunction
        left.weakenReal (phi.weakenReal.instantiate value))) := by
      rw [leftWeaken]
      exact pointwiseRaw
    let generalized := star10_stableGeneralizeImplication (baseOrder := 0)
      universal
      negation disjunction left phi pointwise
    exact star10_applyStableScope (baseOrder := 0) universal negation
      disjunction left phi
      generalized
  have line4 : Derivation (.assertion (implication negation disjunction
      left right)) := by
    unfold right star_10_33_right
    exact star10_joinCertified negation disjunction left
      (star10_stableUniversal (baseOrder := 0) universal phi) p
      (star_10_21_stable_right (baseOrder := 0) universal negation
        disjunction left phi)
      (implication negation disjunction left p)
      (star10_stableScopeDisjunction (baseOrder := 0) universal negation
        disjunction left phi)
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation left) p)
      line3 line2
  have line5 : Derivation (.assertion
      (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
        right product)) := by
    let specialization : Derivation (.assertion
        (implication negation disjunction
          (star10_stableUniversal (baseOrder := 0) universal phi.weakenReal)
          (phi.weakenReal.instantiate value))) :=
      star10_stableSpecialize (baseOrder := 0) universal negation disjunction
        phi.weakenReal value
    let pointwiseRaw := detach negation disjunction _ _ specialization
      (star_3_45 negation disjunction
        (star10_stableUniversal (baseOrder := 0) universal phi.weakenReal)
        (phi.weakenReal.instantiate value) p.weakenReal)
    let pointwise : Derivation (.assertion (implication negation disjunction
        right.weakenReal (product.weakenReal.instantiate value))) := by
      unfold product
      rw [rightWeaken, star_10_35_conjunction_weakenReal,
        Formula.instantiate, star_10_35_conjunction_substitute,
        Formula.closed_weakenReal_instantiateSubstitution]
      exact pointwiseRaw
    let generalized := star10_stableGeneralizeImplication (baseOrder := 0)
      universal
      negation disjunction right product pointwise
    exact star10_applyStableScope (baseOrder := 0) universal negation
      disjunction right product
      generalized
  unfold star_10_33_reading
  exact star_10_13 negation disjunction
    (implication negation disjunction left right)
    (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
      right product)
    line4 line5

/-! ## ✱10·34 -/

/-- `Transp` applied to an implication whose constructor tree is certified
independently of its printed antecedent and consequent. -/
private theorem star10_transposeCertified
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q pqFormula : Formula signature real [] order)
    (pqDisjunctionDefinition : ImplicationDisjunction signature real
      (.neg negation p) q pqFormula)
    (line : Derivation (.assertion pqFormula)) :
    Derivation (.assertion (implication negation disjunction
      (.neg negation q) (.neg negation p))) := by
  let doubleQ : Formula signature real [] order :=
    .neg negation (.neg negation q)
  let line1 := star10_composeCertified negation disjunction p q doubleQ
    (.neg negation p) (.neg negation q)
    pqFormula (implication negation disjunction q doubleQ)
    (implication negation disjunction p doubleQ)
    (ImplicationNegation.star_1_01 negation p)
    (ImplicationNegation.star_1_01 negation q)
    pqDisjunctionDefinition
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation q) doubleQ)
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation p) doubleQ)
    line (star_2_12 negation disjunction q)
  exact detach negation disjunction _ _ line1
    (star_2_03 negation disjunction p (.neg negation q))

/-- Negation congruence for an equivalence whose two implication members
carry independent scope certificates. -/
private theorem star10_negateCertifiedEquivalence
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q pqFormula qpFormula : Formula signature real [] order)
    (pqDisjunctionDefinition : ImplicationDisjunction signature real
      (.neg negation p) q pqFormula)
    (qpDisjunctionDefinition : ImplicationDisjunction signature real
      (.neg negation q) p qpFormula)
    (line : Derivation (.assertion
      (conjunction negation disjunction pqFormula qpFormula))) :
    Derivation (.assertion (star_4_01 negation disjunction
      (.neg negation p) (.neg negation q))) := by
  let line1 := detach negation disjunction _ _ line
    (star_3_26 negation disjunction pqFormula qpFormula)
  let line2 := detach negation disjunction _ _ line
    (star_3_27 negation disjunction pqFormula qpFormula)
  let line3 := star10_transposeCertified negation disjunction p q pqFormula
    pqDisjunctionDefinition line1
  let line4 := star10_transposeCertified negation disjunction q p qpFormula
    qpDisjunctionDefinition line2
  unfold star_4_01
  exact star_10_13 negation disjunction
    (implication negation disjunction (.neg negation p) (.neg negation q))
    (implication negation disjunction (.neg negation q) (.neg negation p))
    line4 line3

/-- The cited ✱4·22 transitivity step for two already derived
equivalences. -/
private theorem star10_chainEquivalence
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : Derivation (.assertion
      (star_4_01 negation disjunction p q)))
    (line2 : Derivation (.assertion
      (star_4_01 negation disjunction q r))) :
    Derivation (.assertion (star_4_01 negation disjunction p r)) := by
  let line3 := star_10_13 negation disjunction
    (star_4_01 negation disjunction p q)
    (star_4_01 negation disjunction q r) line1 line2
  exact detach negation disjunction _ _ line3
    (star_4_22 negation disjunction p q r)

private theorem star10_equivalence_weakenReal
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (equivalence negation disjunction left right).weakenReal
      (fresh := fresh) =
      equivalence negation disjunction left.weakenReal right.weakenReal := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).weakenReal))
      (.neg negation
        ((implication negation disjunction right left).weakenReal))) = _
  rw [implication_weakenReal, implication_weakenReal]

private theorem star10_equivalence_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (equivalence negation disjunction left right).substitute sigma =
      equivalence negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold equivalence conjunction
  change Formula.neg negation
    ((sameDisjunction disjunction
      (.neg negation (implication negation disjunction left right))
      (.neg negation (implication negation disjunction right left))).substitute
        sigma) = _
  rw [sameDisjunction_substitute]
  change Formula.neg negation
    (sameDisjunction disjunction
      (.neg negation
        ((implication negation disjunction left right).substitute sigma))
      (.neg negation
        ((implication negation disjunction right left).substitute sigma))) = _
  rw [implication_substitute, implication_substitute]

/-- The vocabulary of ✱10·01 at the least stable assigned order. -/
private def star10_stableExistentialVocabulary
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height)) :
    ExistentialVocabulary signature argument (Nat.succ argument.height) where
  printed := existential
  matrixNegation := negation
  universal := universal
  outerNegation := Eq.mp
    (congrArg signature.Negation (star10_bindOrderHeight 0 argument).symm)
    negation

/-- ✱10·01 normalized only along the computed stable-order equality. -/
private def star10_stableExistential
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (body : Formula signature real [argument] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  Eq.mp (congrArg (Formula signature real [])
      (star10_bindOrderHeight 0 argument))
    (.sometimes
      (star10_stableExistentialVocabulary existential universal negation) body)

private theorem star10_negation_normalizeOrder
    (equality : sourceOrder = targetOrder)
    (negation : signature.Negation targetOrder)
    (body : Formula signature real [] sourceOrder) :
    Eq.mp (congrArg (Formula signature real []) equality)
      (.neg (Eq.mp (congrArg signature.Negation equality.symm) negation)
        body) =
      .neg negation
        (Eq.mp (congrArg (Formula signature real []) equality) body) := by
  cases equality
  rfl

private theorem star10_stableExistential_unfold
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (body : Formula signature real [argument] (Nat.succ argument.height)) :
    star10_stableExistential existential universal negation body =
      .neg negation
        (star10_stableUniversal (baseOrder := 0) universal
          (.neg negation body)) := by
  unfold star10_stableExistential star10_stableExistentialVocabulary
    Formula.sometimes star10_stableUniversal
  exact star10_negation_normalizeOrder
    (star10_bindOrderHeight 0 argument) negation
    (.always universal (.neg negation body))

/-- The independently constructed left member `(exists x).phi x implies p`
of ✱10·34. -/
def star_10_34_left
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  star10_stableExistential existential universal negation
    (implication negation disjunction phi
      (p.rename (fun v => .succ v)))

/-- The independently constructed right member `(x).phi x implies p` of
✱10·34. -/
def star_10_34_right
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  implication negation disjunction
    (star10_stableUniversal (baseOrder := 0) universal phi) p

/-- Audited catalogue reading of ✱10·34. -/
def star_10_34_reading
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "✱10·34.  ⊢ : .(∃x).φx⊃p .≡ : (x).φx .⊃ .p"
  parsed := .assertion (star_4_01 negation disjunction
    (star_10_34_left existential universal negation disjunction phi p)
    (star_10_34_right universal negation disjunction phi p))

/-- ✱10·34.  `line1`--`line5` follow the printed chain
✱4·2/10·01, ✱4·61/10·271, ✱10·33, ✱4·53, and ✱4·6.
`demonstration_provenance: follows-printed`. -/
theorem star_10_34
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height))
    (witness : Term signature real [] argument) :
    Derivation (star_10_34_reading existential universal negation disjunction
      phi p).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let implicationMatrix := implication negation disjunction phi
    (p.rename (fun v => .succ v))
  let negatedImplication :
      Formula signature real [argument] (Nat.succ argument.height) :=
    .neg negation implicationMatrix
  let product : Formula signature real [argument]
      (Nat.succ argument.height) := conjunction negation disjunction phi
    ((Formula.neg negation p).rename (fun v => .succ v))
  let universalNegatedImplication : Formula signature real []
      (Nat.succ argument.height) :=
    star10_stableUniversal (baseOrder := 0) universal negatedImplication
  let universalProduct : Formula signature real []
      (Nat.succ argument.height) :=
    star10_stableUniversal (baseOrder := 0) universal product
  let universalPhi : Formula signature real []
      (Nat.succ argument.height) :=
    star10_stableUniversal (baseOrder := 0) universal phi
  let productRight : Formula signature real []
      (Nat.succ argument.height) := conjunction negation disjunction universalPhi
    (Formula.neg negation p)
  let stage0 : Formula signature real [] (Nat.succ argument.height) :=
    .neg negation universalNegatedImplication
  let stage1 : Formula signature real [] (Nat.succ argument.height) :=
    .neg negation universalProduct
  let stage2 : Formula signature real [] (Nat.succ argument.height) :=
    .neg negation productRight
  let stage3 : Formula signature real [] (Nat.succ argument.height) :=
    sameDisjunction disjunction (.neg negation universalPhi) p
  let left := star_10_34_left existential universal negation disjunction phi p
  let right := star_10_34_right universal negation disjunction phi p
  have line1 : Derivation (.assertion
      (star_4_01 negation disjunction left stage0)) := by
    unfold left star_10_34_left stage0 universalNegatedImplication
      negatedImplication implicationMatrix
    rw [star10_stableExistential_unfold]
    exact star_4_2 negation disjunction
      (.neg negation
        (star10_stableUniversal (baseOrder := 0) universal
          (.neg negation
            (implication negation disjunction phi
              (p.rename (fun v => .succ v))))))
  have line2 : Derivation (.assertion
      (star_4_01 negation disjunction stage0 stage1)) := by
    let matrixEquivalence := equivalence negation disjunction
      negatedImplication product
    let matrixLine : Derivation (.assertion
        (matrixEquivalence.weakenReal.instantiate value)) := by
      unfold matrixEquivalence negatedImplication implicationMatrix product
      rw [star10_equivalence_weakenReal, Formula.instantiate,
        star10_equivalence_substitute]
      change Derivation (.assertion (equivalence negation disjunction
        (.neg negation
          ((implication negation disjunction phi
            (p.rename (fun v => .succ v))).weakenReal.substitute
              (instantiateSubstitution value)))
        ((conjunction negation disjunction phi
          ((Formula.neg negation p).rename
            (fun v => .succ v))).weakenReal.substitute
              (instantiateSubstitution value))))
      rw [implication_weakenReal,
        implication_substitute, star_10_35_conjunction_weakenReal,
        star_10_35_conjunction_substitute,
        Formula.closed_weakenReal_instantiateSubstitution p argument value,
        Formula.closed_weakenReal_instantiateSubstitution
          (Formula.neg negation p) argument value]
      change Derivation (.assertion (star_4_01 negation disjunction
        (.neg negation (implication negation disjunction
          (phi.weakenReal.instantiate value) p.weakenReal))
        (conjunction negation disjunction
          (phi.weakenReal.instantiate value) (.neg negation p.weakenReal))))
      exact star_4_61 negation disjunction
        (phi.weakenReal.instantiate value) p.weakenReal
    let generalized := star10_stableGeneralize (baseOrder := 0) universal
      matrixEquivalence matrixLine
    let lifting := star_10_271 (baseOrder := 0) universal negation disjunction
      negatedImplication product
    let lifted : Derivation (.assertion (star_4_01 negation disjunction
        universalNegatedImplication universalProduct)) := by
      unfold star_10_271_reading star_10_271_left star_10_271_right at lifting
      exact detach negation disjunction _ _ generalized lifting
    let congruence := star_4_11 negation disjunction
      universalNegatedImplication universalProduct
    let forward := detach negation disjunction _ _ congruence
      (star_3_26 negation disjunction
        (implication negation disjunction
          (star_4_01 negation disjunction universalNegatedImplication
            universalProduct)
          (star_4_01 negation disjunction
            (.neg negation universalNegatedImplication)
            (.neg negation universalProduct)))
        (implication negation disjunction
          (star_4_01 negation disjunction
            (.neg negation universalNegatedImplication)
            (.neg negation universalProduct))
          (star_4_01 negation disjunction universalNegatedImplication
            universalProduct)))
    exact detach negation disjunction _ _ lifted forward
  have line3 : Derivation (.assertion
      (star_4_01 negation disjunction stage1 stage2)) := by
    let distribution := star_10_33 universal negation disjunction phi
      (.neg negation p) witness
    unfold star_10_33_reading star_10_33_left star_10_33_right at distribution
    change Derivation (.assertion (conjunction negation disjunction
      (implication negation disjunction universalProduct productRight)
      (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
        productRight product))) at distribution
    exact star10_negateCertifiedEquivalence negation disjunction
      universalProduct productRight
      (implication negation disjunction universalProduct productRight)
      (star_10_21_stable_right (baseOrder := 0) universal negation disjunction
        productRight product)
      (ImplicationDisjunction.star_1_01_same disjunction
        (.neg negation universalProduct) productRight)
      (star10_stableScopeDisjunction (baseOrder := 0) universal negation
        disjunction
        productRight product)
      distribution
  have line4 : Derivation (.assertion
      (star_4_01 negation disjunction stage2 stage3)) := by
    exact star_4_53 negation disjunction universalPhi p
  have line5 : Derivation (.assertion
      (star_4_01 negation disjunction stage3 right)) := by
    let printedLine := star_4_6 negation disjunction universalPhi p
    unfold right star_10_34_right stage3
    exact detach negation disjunction _ _ printedLine
      (star_3_22 negation disjunction
        (implication negation disjunction
          (implication negation disjunction universalPhi p)
          (sameDisjunction disjunction (.neg negation universalPhi) p))
        (implication negation disjunction
          (sameDisjunction disjunction (.neg negation universalPhi) p)
          (implication negation disjunction universalPhi p)))
  exact star10_chainEquivalence negation disjunction left stage0 right line1
    (star10_chainEquivalence negation disjunction stage0 stage1 right line2
      (star10_chainEquivalence negation disjunction stage1 stage2 right line3
        (star10_chainEquivalence negation disjunction stage2 stage3 right
          line4 line5)))

/-! ## ✱10·36 -/

private theorem star10_disjunction_weakenReal_instantiate_closedRight
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [argument] order)
    (p : Formula signature real [] order)
    (value : Term signature (argument :: real) [] argument) :
    (sameDisjunction disjunction phi
      (p.rename (fun v => .succ v))).weakenReal.instantiate value =
      sameDisjunction disjunction
        (phi.weakenReal.instantiate value) p.weakenReal := by
  rw [sameDisjunction_weakenReal]
  unfold Formula.instantiate
  rw [sameDisjunction_substitute,
    Formula.closed_weakenReal_instantiateSubstitution]

private theorem star10_implication_weakenReal_instantiate_closedRight
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [argument] order)
    (p : Formula signature real [] order)
    (value : Term signature (argument :: real) [] argument) :
    (implication negation disjunction phi
      (p.rename (fun v => .succ v))).weakenReal.instantiate value =
      implication negation disjunction
        (phi.weakenReal.instantiate value) p.weakenReal := by
  rw [implication_weakenReal]
  unfold Formula.instantiate
  rw [implication_substitute,
    Formula.closed_weakenReal_instantiateSubstitution]

/-- The stable-order instance of the acquired ✱10·28: a pointwise
implication lifts through the two ✱10·01 existential definitions. -/
private theorem star10_liftStableExistential
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi psi : Formula signature real [argument] (Nat.succ argument.height))
    (line1 : Derivation (.assertion (implication negation disjunction
      (phi.weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument)))
      (psi.weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument)))))) :
    Derivation (.assertion (implication negation disjunction
      (star10_stableExistential existential universal negation phi)
      (star10_stableExistential existential universal negation psi))) := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let line2Raw := star10_transposeCertified negation disjunction
    (phi.weakenReal.instantiate value) (psi.weakenReal.instantiate value)
    (implication negation disjunction
      (phi.weakenReal.instantiate value) (psi.weakenReal.instantiate value))
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation (phi.weakenReal.instantiate value))
      (psi.weakenReal.instantiate value)) line1
  let line2 : Derivation (.assertion
      ((implication negation disjunction
        (.neg negation psi) (.neg negation phi)).weakenReal.instantiate
          value)) := by
    rw [implication_weakenReal, Formula.instantiate,
      implication_substitute]
    exact line2Raw
  let line3 := star10_stableGeneralize (baseOrder := 0) universal
    (implication negation disjunction
      (.neg negation psi) (.neg negation phi)) line2
  let line4 := detach negation disjunction _ _ line3
    (star_10_27_stable universal negation disjunction
      (.neg negation psi) (.neg negation phi))
  let line5 := star10_transposeCertified negation disjunction
    (star10_stableUniversal (baseOrder := 0) universal (.neg negation psi))
    (star10_stableUniversal (baseOrder := 0) universal (.neg negation phi))
    (implication negation disjunction
      (star10_stableUniversal (baseOrder := 0) universal (.neg negation psi))
      (star10_stableUniversal (baseOrder := 0) universal (.neg negation phi)))
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation
        (star10_stableUniversal (baseOrder := 0) universal
          (.neg negation psi)))
      (star10_stableUniversal (baseOrder := 0) universal
        (.neg negation phi))) line4
  rw [star10_stableExistential_unfold,
    star10_stableExistential_unfold]
  exact line5

/-- The independently constructed left member `(exists x).phi x or p` of
✱10·36. -/
def star_10_36_left
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  star10_stableExistential existential universal negation
    (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))

/-- The independently constructed right member `(exists x).phi x .or. p`
of ✱10·36. -/
def star_10_36_right
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  sameDisjunction disjunction
    (star10_stableExistential existential universal negation phi) p

/-- Audited catalogue reading of ✱10·36. -/
def star_10_36_reading
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "✱10·36.  ⊢ : .(∃x).φx∨p .≡ : (∃x).φx .∨ .p"
  parsed := .assertion (star_4_01 negation disjunction
    (star_10_36_left existential universal negation disjunction phi p)
    (star_10_36_right existential universal negation disjunction phi p))

/-- ✱10·36.  `line1` is ✱4·64 lifted by ✱10·11/28 in both
orientations; `line2` is the cited ✱10·34 instance; `line3` is
✱4·6 after ✱10·01.
`demonstration_provenance: follows-printed`. -/
theorem star_10_36
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height))
    (witness : Term signature real [] argument) :
    Derivation (star_10_36_reading existential universal negation disjunction
      phi p).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let disjunctionMatrix := sameDisjunction disjunction phi
    (p.rename (fun v => .succ v))
  let implicationMatrix := implication negation disjunction
    (.neg negation phi) (p.rename (fun v => .succ v))
  let left := star_10_36_left existential universal negation disjunction phi p
  let stage1 := star10_stableExistential existential universal negation
    implicationMatrix
  let stage2 := implication negation disjunction
    (star10_stableUniversal (baseOrder := 0) universal (.neg negation phi)) p
  let right := star_10_36_right existential universal negation disjunction phi p
  have line1 : Derivation (.assertion
      (star_4_01 negation disjunction left stage1)) := by
    let pointEquivalence := star_4_64 negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal
    let pointForward := detach negation disjunction _ _ pointEquivalence
      (star_3_27 negation disjunction
        (implication negation disjunction
          (implication negation disjunction
            (.neg negation (phi.weakenReal.instantiate value)) p.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) p.weakenReal))
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) p.weakenReal)
          (implication negation disjunction
            (.neg negation (phi.weakenReal.instantiate value)) p.weakenReal)))
    let pointReverse := detach negation disjunction _ _ pointEquivalence
      (star_3_26 negation disjunction
        (implication negation disjunction
          (implication negation disjunction
            (.neg negation (phi.weakenReal.instantiate value)) p.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) p.weakenReal))
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) p.weakenReal)
          (implication negation disjunction
            (.neg negation (phi.weakenReal.instantiate value)) p.weakenReal)))
    let forwardInput : Derivation (.assertion (implication negation disjunction
        (disjunctionMatrix.weakenReal.instantiate value)
        (implicationMatrix.weakenReal.instantiate value))) := by
      rw [star10_disjunction_weakenReal_instantiate_closedRight,
        star10_implication_weakenReal_instantiate_closedRight]
      exact pointForward
    let reverseInput : Derivation (.assertion (implication negation disjunction
        (implicationMatrix.weakenReal.instantiate value)
        (disjunctionMatrix.weakenReal.instantiate value))) := by
      rw [star10_implication_weakenReal_instantiate_closedRight,
        star10_disjunction_weakenReal_instantiate_closedRight]
      exact pointReverse
    let forward := star10_liftStableExistential existential universal
      negation disjunction disjunctionMatrix implicationMatrix forwardInput
    let reverse := star10_liftStableExistential existential universal
      negation disjunction implicationMatrix disjunctionMatrix reverseInput
    unfold left star_10_36_left stage1
    unfold star_4_01
    exact star_10_13 negation disjunction
      (implication negation disjunction
        (star10_stableExistential existential universal negation
          disjunctionMatrix)
        (star10_stableExistential existential universal negation
          implicationMatrix))
      (implication negation disjunction
        (star10_stableExistential existential universal negation
          implicationMatrix)
        (star10_stableExistential existential universal negation
          disjunctionMatrix))
      forward reverse
  have line2 : Derivation (.assertion
      (star_4_01 negation disjunction stage1 stage2)) := by
    exact star_10_34 existential universal negation disjunction
      (.neg negation phi) p witness
  have line3 : Derivation (.assertion
      (star_4_01 negation disjunction stage2 right)) := by
    unfold stage2 right star_10_36_right
    rw [star10_stableExistential_unfold]
    exact star_4_6 negation disjunction
      (star10_stableUniversal (baseOrder := 0) universal
        (.neg negation phi)) p
  exact star10_chainEquivalence negation disjunction left stage1 right line1
    (star10_chainEquivalence negation disjunction stage1 stage2 right
      line2 line3)

/-! ## ✱10·37 -/

private theorem star10_implication_weakenReal_instantiate_closedLeft
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order)
    (phi : Formula signature real [argument] order)
    (value : Term signature (argument :: real) [] argument) :
    (implication negation disjunction
      (p.rename (fun v => .succ v)) phi).weakenReal.instantiate value =
      implication negation disjunction p.weakenReal
        (phi.weakenReal.instantiate value) := by
  rw [implication_weakenReal]
  unfold Formula.instantiate
  rw [implication_substitute,
    Formula.closed_weakenReal_instantiateSubstitution]

/-- The independently constructed left member `(exists x).p implies phi x`
of ✱10·37. -/
def star_10_37_left
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  star10_stableExistential existential universal negation
    (implication negation disjunction
      (p.rename (fun v => .succ v)) phi)

/-- The independently constructed right member `p implies (exists x).phi x`
of ✱10·37. -/
def star_10_37_right
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height)) :
    Formula signature real [] (Nat.succ argument.height) :=
  implication negation disjunction p
    (star10_stableExistential existential universal negation phi)

/-- Audited catalogue reading of ✱10·37. -/
def star_10_37_reading
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height)) :
    ClaimReading signature real where
  printed := "✱10·37.  ⊢ : .(∃x).p⊃φx .≡ : p .⊃ .(∃x).φx  [✱10·36  ∼p/p]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_10_37_left existential universal negation disjunction p phi)
    (star_10_37_right existential universal negation disjunction p phi))

/-- ✱10·37.  `line2` is exactly the printed substitution
`[✱10·36  ∼p/p]`; `line1` and `line3` expose the two implication
abbreviations by Perm.
`demonstration_provenance: follows-printed`. -/
theorem star_10_37
    (existential : signature.Existential argument (Nat.succ argument.height))
    (universal : signature.Universal argument (Nat.succ argument.height))
    (negation : signature.Negation (Nat.succ argument.height))
    (disjunction : signature.Disjunction (Nat.succ argument.height))
    (p : Formula signature real [] (Nat.succ argument.height))
    (phi : Formula signature real [argument] (Nat.succ argument.height))
    (witness : Term signature real [] argument) :
    Derivation (star_10_37_reading existential universal negation disjunction
      p phi).parsed := by
  let value : Term signature (argument :: real) [] argument := .real .zero
  let implicationMatrix := implication negation disjunction
    (p.rename (fun v => .succ v)) phi
  let commutedMatrix := sameDisjunction disjunction phi
    ((Formula.neg negation p).rename (fun v => .succ v))
  let left := star_10_37_left existential universal negation disjunction p phi
  let stage1 := star_10_36_left existential universal negation disjunction
    phi (.neg negation p)
  let stage2 := star_10_36_right existential universal negation disjunction
    phi (.neg negation p)
  let right := star_10_37_right existential universal negation disjunction p phi
  have line1 : Derivation (.assertion
      (star_4_01 negation disjunction left stage1)) := by
    let pointEquivalence := star_4_31 negation disjunction
      (.neg negation p.weakenReal) (phi.weakenReal.instantiate value)
    let pointForward := detach negation disjunction _ _ pointEquivalence
      (star_3_26 negation disjunction
        (implication negation disjunction
          (sameDisjunction disjunction (.neg negation p.weakenReal)
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction (phi.weakenReal.instantiate value)
            (.neg negation p.weakenReal)))
        (implication negation disjunction
          (sameDisjunction disjunction (phi.weakenReal.instantiate value)
            (.neg negation p.weakenReal))
          (sameDisjunction disjunction (.neg negation p.weakenReal)
            (phi.weakenReal.instantiate value))))
    let pointReverse := detach negation disjunction _ _ pointEquivalence
      (star_3_27 negation disjunction
        (implication negation disjunction
          (sameDisjunction disjunction (.neg negation p.weakenReal)
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction (phi.weakenReal.instantiate value)
            (.neg negation p.weakenReal)))
        (implication negation disjunction
          (sameDisjunction disjunction (phi.weakenReal.instantiate value)
            (.neg negation p.weakenReal))
          (sameDisjunction disjunction (.neg negation p.weakenReal)
            (phi.weakenReal.instantiate value))))
    let forwardInput : Derivation (.assertion (implication negation disjunction
        (implicationMatrix.weakenReal.instantiate value)
        (commutedMatrix.weakenReal.instantiate value))) := by
      unfold implicationMatrix commutedMatrix
      rw [star10_implication_weakenReal_instantiate_closedLeft,
        star10_disjunction_weakenReal_instantiate_closedRight]
      exact pointForward
    let reverseInput : Derivation (.assertion (implication negation disjunction
        (commutedMatrix.weakenReal.instantiate value)
        (implicationMatrix.weakenReal.instantiate value))) := by
      unfold commutedMatrix implicationMatrix
      rw [star10_disjunction_weakenReal_instantiate_closedRight,
        star10_implication_weakenReal_instantiate_closedLeft]
      exact pointReverse
    let forward := star10_liftStableExistential existential universal
      negation disjunction implicationMatrix commutedMatrix forwardInput
    let reverse := star10_liftStableExistential existential universal
      negation disjunction commutedMatrix implicationMatrix reverseInput
    unfold left star_10_37_left stage1 star_10_36_left
    unfold star_4_01
    exact star_10_13 negation disjunction
      (implication negation disjunction
        (star10_stableExistential existential universal negation
          implicationMatrix)
        (star10_stableExistential existential universal negation
          commutedMatrix))
      (implication negation disjunction
        (star10_stableExistential existential universal negation
          commutedMatrix)
        (star10_stableExistential existential universal negation
          implicationMatrix))
      forward reverse
  have line2 : Derivation (.assertion
      (star_4_01 negation disjunction stage1 stage2)) := by
    exact star_10_36 existential universal negation disjunction
      phi (.neg negation p) witness
  have line3 : Derivation (.assertion
      (star_4_01 negation disjunction stage2 right)) := by
    unfold stage2 star_10_36_right right star_10_37_right
    exact star_4_31 negation disjunction
      (star10_stableExistential existential universal negation phi)
      (.neg negation p)
  exact star10_chainEquivalence negation disjunction left stage1 right line1
    (star10_chainEquivalence negation disjunction stage1 stage2 right
      line2 line3)

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

/-! ## ✱10·5 -/

/-- The constructor-level normal form of ✱10·5.  Each conjunct is the
independently scoped ✱10·28 consequence obtained from one of the two printed
projections.  This is the form reached after the printed existential
definitions and transpositions are eliminated. -/
def star_10_5_formula
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (resultNegation : signature.Negation
      (bindOrder (bindOrder 0 argument) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (bindOrder 0 argument) argument))
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real []
      (bindOrder (bindOrder 0 argument) argument) :=
  let product := conjunction negation0 disjunction0 phi psi
  conjunction resultNegation resultDisjunction
    (star_9_22_consequent existential0 existential1
      negation0 disjunction0 product phi)
    (star_9_22_consequent existential0 existential1
      negation0 disjunction0 product psi)

/-- Audited catalogue reading of ✱10·5. -/
def star_10_5_reading
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (resultNegation : signature.Negation
      (bindOrder (bindOrder 0 argument) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (bindOrder 0 argument) argument))
    (phi psi : Formula signature real [argument] 0) :
    ClaimReading signature real where
  printed := "⊢ : .(∃x).φx .ψx .⊃ : (∃x).φx : (∃x).ψx"
  parsed := .assertion (star_10_5_formula existential0 existential1
    negation0 disjunction0 resultNegation resultDisjunction phi psi)

/-- ✱10·5.  `line1` and `line2` are exactly PM's two projected instances of
✱10·28, obtained respectively from ✱3·26 and ✱3·27 through ✱10·11.  `line3`
performs the printed `Comp`; the target is already in the constructor-level
normal form exposed by the existential definitions.
`demonstration_provenance: follows-printed`. -/
theorem star_10_5
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
    (resultNegation : signature.Negation
      (bindOrder (bindOrder 0 argument) argument))
    (resultDisjunction : signature.Disjunction
      (bindOrder (bindOrder 0 argument) argument))
    (phi psi : Formula signature real [argument] 0) :
    Derivation (star_10_5_reading existential0 existential1 negation0
      disjunction0 resultNegation resultDisjunction phi psi).parsed := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  let product := conjunction negation0 disjunction0 phi psi
  let projectionLeft := implication negation0 disjunction0 product phi
  let projectionRight := implication negation0 disjunction0 product psi
  let leftConsequence := star_9_22_consequent existential0 existential1
    negation0 disjunction0 product phi
  let rightConsequence := star_9_22_consequent existential0 existential1
    negation0 disjunction0 product psi
  have line1 : Derivation (.assertion leftConsequence) := by
    have matrixLine : Derivation (.assertion
        (projectionLeft.weakenReal.instantiate z)) := by
      unfold projectionLeft product
      rw [implication_weakenReal, star_10_35_conjunction_weakenReal,
        Formula.instantiate, implication_substitute,
        star_10_35_conjunction_substitute]
      exact star_3_26 negation0 disjunction0
        (phi.weakenReal.instantiate z) (psi.weakenReal.instantiate z)
    have universalLine := star_10_11 existential0.universal
      projectionLeft matrixLine
    have liftingLine := star_10_28 existential0 existential1 universal2
      negation0 disjunction0 disjunction01 negation1 disjunction12 product phi
    letI : ImplicationReading negation1 disjunction12
        (.always existential0.universal projectionLeft)
        (.always universal2 (star_9_22_body existential0 existential1
          negation0 disjunction0 product phi))
        leftConsequence :=
      star_9_22_implicationReading existential0 existential1 universal2
        negation0 disjunction0 negation1 disjunction12 product phi
    exact Derivation.star_9_12 negation1 disjunction12
      universalLine liftingLine
  have line2 : Derivation (.assertion rightConsequence) := by
    have matrixLine : Derivation (.assertion
        (projectionRight.weakenReal.instantiate z)) := by
      unfold projectionRight product
      rw [implication_weakenReal, star_10_35_conjunction_weakenReal,
        Formula.instantiate, implication_substitute,
        star_10_35_conjunction_substitute]
      exact star_3_27 negation0 disjunction0
        (phi.weakenReal.instantiate z) (psi.weakenReal.instantiate z)
    have universalLine := star_10_11 existential0.universal
      projectionRight matrixLine
    have liftingLine := star_10_28 existential0 existential1 universal2
      negation0 disjunction0 disjunction01 negation1 disjunction12 product psi
    letI : ImplicationReading negation1 disjunction12
        (.always existential0.universal projectionRight)
        (.always universal2 (star_9_22_body existential0 existential1
          negation0 disjunction0 product psi))
        rightConsequence :=
      star_9_22_implicationReading existential0 existential1 universal2
        negation0 disjunction0 negation1 disjunction12 product psi
    exact Derivation.star_9_12 negation1 disjunction12
      universalLine liftingLine
  have line3 : Derivation (.assertion
      (conjunction resultNegation resultDisjunction
        leftConsequence rightConsequence)) := by
    have identityLine := star_2_08 resultNegation resultDisjunction
      leftConsequence
    have factLine := detach resultNegation resultDisjunction
      rightConsequence
      (implication resultNegation resultDisjunction
        leftConsequence rightConsequence)
      line2 (star_2_02 resultNegation resultDisjunction
        leftConsequence rightConsequence)
    have premissLine := star_10_13 resultNegation resultDisjunction
      (implication resultNegation resultDisjunction
        leftConsequence leftConsequence)
      (implication resultNegation resultDisjunction
        leftConsequence rightConsequence)
      identityLine factLine
    have compLine := star_3_43 resultNegation resultDisjunction
      leftConsequence leftConsequence rightConsequence
    have implicationLine := detach resultNegation resultDisjunction
      (conjunction resultNegation resultDisjunction
        (implication resultNegation resultDisjunction
          leftConsequence leftConsequence)
        (implication resultNegation resultDisjunction
          leftConsequence rightConsequence))
      (implication resultNegation resultDisjunction leftConsequence
        (conjunction resultNegation resultDisjunction
          leftConsequence rightConsequence))
      premissLine compLine
    exact detach resultNegation resultDisjunction leftConsequence
      (conjunction resultNegation resultDisjunction
        leftConsequence rightConsequence) line1 implicationLine
  unfold star_10_5_reading star_10_5_formula
  exact line3

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_10_1
#print axioms PM.RamifiedSyntax.star_10_11
#print axioms PM.RamifiedSyntax.star_10_121
#print axioms PM.RamifiedSyntax.star_10_122
#print axioms PM.RamifiedSyntax.star_10_12
#print axioms PM.RamifiedSyntax.star_10_13
#print axioms PM.RamifiedSyntax.star_10_14
#print axioms PM.RamifiedSyntax.star_10_23_left_unfold
#print axioms PM.RamifiedSyntax.star_10_23_right_unfold
#print axioms PM.RamifiedSyntax.star_10_23
#print axioms PM.RamifiedSyntax.star_10_2
#print axioms PM.RamifiedSyntax.star_10_21
#print axioms PM.RamifiedSyntax.star_10_21_stable_left_unfold
#print axioms PM.RamifiedSyntax.star_10_21_stable
#print axioms PM.RamifiedSyntax.star_10_22
#print axioms PM.RamifiedSyntax.star_10_24
#print axioms PM.RamifiedSyntax.star_10_26
#print axioms PM.RamifiedSyntax.star_10_27
#print axioms PM.RamifiedSyntax.star_10_27_saturated
#print axioms PM.RamifiedSyntax.star_10_27_stable
#print axioms PM.RamifiedSyntax.star_10_271
#print axioms PM.RamifiedSyntax.star_10_28
#print axioms PM.RamifiedSyntax.star_10_301
#print axioms PM.RamifiedSyntax.star_10_31
#print axioms PM.RamifiedSyntax.star_10_311
#print axioms PM.RamifiedSyntax.star_10_32
#print axioms PM.RamifiedSyntax.star_10_33
#print axioms PM.RamifiedSyntax.star_10_34
#print axioms PM.RamifiedSyntax.star_10_36
#print axioms PM.RamifiedSyntax.star_10_37
#print axioms PM.RamifiedSyntax.star_10_35_left_unfold
#print axioms PM.RamifiedSyntax.star_10_35_right_unfold
#print axioms PM.RamifiedSyntax.star_10_35
#print axioms PM.RamifiedSyntax.star_10_43
#print axioms PM.RamifiedSyntax.star_10_5
