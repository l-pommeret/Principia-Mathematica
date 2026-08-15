import Principia.Syntax.Ramified
import Principia.Syntax.Printed
import Principia.Deduction.Star2Ramified

namespace PM.RamifiedSyntax

/- A T4 reading for the heterogeneous ramified claims of ✱9. -/
structure Star9Reading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String := "The parsed field is the eliminable ramified AST of the diplomatic formula."

/- A transparent spelling used only to keep T4 focused on the conclusion of
the two metalinguistic rules whose premisses are themselves derivations. -/
abbrev Star9Assertion
    (formula : Formula signature real [] order) :=
  Derivation (.assertion formula)

/-! # Derived propositions of PM I, ✱9

The formulae below use the eliminable scope conventions ✱9·03--·08: their
expanded AST is the universal closure of the elementary matrix displayed in
the proof. Each proof consequently has exactly PM's two essential lines: the
appropriate primitive of ✱1 on the matrix, followed by ✱9·13.
-/

def star_9_1_reading
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:φx.⊃.(∃z).φz  Pp"
  parsed := .assertion (mixedImplication negation disjunction
    (body.instantiate value) (.sometimes existential body))

/-- ✱9·1, the first primitive existential-introduction proposition.
`demonstration_provenance: follows-printed`. -/
theorem star_9_1
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Derivation (.assertion (mixedImplication negation disjunction
      (body.instantiate value) (.sometimes existential body))) := by
  have line1 := Derivation.star_9_1 existential negation disjunction body value
  exact line1

def star_9_11_reading
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (x y : Term signature real [] argument) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:φx∨φy.⊃.(∃z).φz  Pp"
  parsed := .assertion (mixedImplication negation disjunction
    (sameDisjunction matrixDisjunction (body.instantiate x)
      (body.instantiate y))
    (.sometimes existential body))

/-- ✱9·11, the second primitive existential-introduction proposition.
`demonstration_provenance: follows-printed`. -/
theorem star_9_11
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (x y : Term signature real [] argument) :
    Derivation (.assertion (mixedImplication negation disjunction
      (sameDisjunction matrixDisjunction (body.instantiate x)
        (body.instantiate y))
      (.sometimes existential body))) := by
  have line1 := Derivation.star_9_11 existential negation matrixDisjunction
    disjunction body x y
  exact line1

def star_9_12_reading
    (q : Formula signature real [] rightOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "What is implied by a true premiss is true. Pp."
  parsed := .assertion q

/-- ✱9·12 is PM's primitive detachment rule at the new proposition orders.
Its two arguments are the premisses printed in the prose rule, not additional
hypotheses about the numbered proposition.
`demonstration_provenance: follows-printed`. -/
theorem star_9_12
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (p : Formula signature real [] leftOrder)
    (q : Formula signature real [] rightOrder)
    (line1 : Star9Assertion p)
    (line2 : Star9Assertion
      (mixedImplication negation disjunction p q)) :
    Derivation (.assertion q) := by
  have line3 := Derivation.star_9_12 negation disjunction line1 line2
  exact line3

def star_9_13_reading
    (universal : signature.Universal argument matrixOrder)
    (body : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "In any assertion containing a real variable, this real variable may\nbe turned into an apparent variable of which all possible values are asserted\nto satisfy the function in question. Pp."
  parsed := .assertion (.always universal body)

/-- ✱9·13, with PM's real-variable premiss represented explicitly.
`demonstration_provenance: follows-printed`. -/
theorem star_9_13
    (universal : signature.Universal argument matrixOrder)
    (body : Formula signature real [argument] matrixOrder)
    (line1 : Star9Assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument)))) :
    Derivation (.assertion (.always universal body)) := by
  have line2 := Derivation.star_9_13 universal body line1
  exact line2

def star_9_14_reading
    (body : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "✱9·14. If \" φ x \" is significant, then if x is of the same type as a , \" φ a \" is significant, and vice versa. Pp. (Cf. note on *10·121, p. 146.)"
  parsed := .significance body

/-- ✱9·14, restated at ✱10·121 with exactly the same primitive content.
`demonstration_provenance: follows-printed`. -/
theorem star_9_14
    (body : Formula signature real [argument] matrixOrder) :
    Derivation (.significance body) := by
  have line1 := Derivation.star_10_121 body
  exact line1

def star_9_15_reading
    (body : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "✱9·15. If, for some a , there is a proposition φ a , then there is a function φ x̂ , and vice versa. Pp."
  parsed := .functionExistence body

/-- ✱9·15, restated at ✱10·122 with exactly the same primitive content.
`demonstration_provenance: follows-printed`. -/
theorem star_9_15
    (body : Formula signature real [argument] matrixOrder) :
    Derivation (.functionExistence body) := by
  have line1 := Derivation.star_10_122 body
  exact line1

private theorem lift_star_1_3_left
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction q.weakenReal
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
          q.weakenReal) :=
    Derivation.star_1_3_same negation disjunction
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
      q.weakenReal
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))).weakenReal.instantiate value =
      implication negation disjunction q.weakenReal
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value) q.weakenReal) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      Formula.instantiate, implication_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (q.rename (fun v => .succ v))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_2
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction phi phi) phi) := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value)
          (phi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value) :=
    Derivation.star_1_2 negation disjunction
      (phi.weakenReal.instantiate value)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi phi) phi).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate value)
          (phi.weakenReal.instantiate value))
        (phi.weakenReal.instantiate value) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi phi) phi)
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_4
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument))))
        (sameDisjunction disjunction
          (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
          p.weakenReal) :=
    Derivation.star_1_4_same negation disjunction p.weakenReal
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      (sameDisjunction disjunction phi (p.rename (fun v => .succ v))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_5
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))) := by
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument))))) :=
    Derivation.star_1_5_same negation disjunction p.weakenReal q.weakenReal
      (phi.weakenReal.instantiate (.real (.zero : Var (argument :: real) argument)))
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction q.weakenReal (phi.weakenReal.instantiate value)))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value))) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private theorem lift_star_1_4_reverse
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ .always universal
      (implication negation disjunction
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)) := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal)
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value)) :=
    Derivation.star_1_4_same negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value) p.weakenReal)
        (sameDisjunction disjunction p.weakenReal (phi.weakenReal.instantiate value)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))
    (Derivation.castAssertion matrixEq line1)
  exact line2

private def star_9_3x_slotInner : Renaming [argument] [argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

private def star_9_3x_slotOuter : Renaming [argument] [argument, argument]
  | _, .zero => .succ .zero
  | _, .succ v => nomatch v

private def star_9_3x_slotThird : Renaming [argument]
    [argument, argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

def star_9_32_reading (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .q . ⊃ : (x).φx .∨. q"
  parsed := .assertion (star_9_04 universal matrixDisjunction
    (.neg matrixNegation q)
    (sameDisjunction matrixDisjunction phi (q.rename (fun v => .succ v))))
  scopeReading := "The outer implication and the member `(x).φx ∨ q` are both read through the scoped definitions ✱9·04 and ✱9·03; unfolding yields PM's generalized elementary matrix."

def star_9_34_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal : signature.Universal argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(x).φx .⊃ : p .∨. (x).φx"
  parsed := .assertion (star_9_08 existential universal disjunction
    (.neg negation (phi.rename star_9_3x_slotInner))
    (sameDisjunction disjunction
      (p.rename (fun v => .succ (.succ v)))
      (phi.rename star_9_3x_slotOuter)))
  scopeReading := "The antecedent negation is ✱9·01, the disjunction of its existential expansion with the universal consequent is ✱9·08, and `p ∨ (x).φx` is ✱9·04. The resulting AST is `(z)(∃x).∼φx ∨ (p ∨ φz)`."

def star_9_36_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal : signature.Universal argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .p .∨. (x).φx : ⊃ : (x).φx .∨. p"
  parsed := .assertion (star_9_08 existential universal disjunction
    (.neg negation (sameDisjunction disjunction
      (p.rename (fun v => .succ (.succ v)))
      (phi.rename star_9_3x_slotInner)))
    (sameDisjunction disjunction
      (phi.rename star_9_3x_slotOuter)
      (p.rename (fun v => .succ (.succ v)))))
  scopeReading := "The antecedent `p ∨ (x).φx` and consequent `(x).φx ∨ p` are read by ✱9·04 and ✱9·03; ✱9·01 and ✱9·08 give the two-binder scoped implication AST."

def star_9_361_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(x).φx .∨. p : ⊃ : p .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
    (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_361 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_361_reading universal negation disjunction p phi).parsed := by
  exact lift_star_1_4_reverse universal negation disjunction p phi

def star_9_4_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p : ∨ : q .∨. (x).φx : .⊃ : .q : ∨ : p .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_4 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_4_reading universal negation disjunction p q phi).parsed := by
  exact lift_star_1_5 universal negation disjunction p q phi

def star_9_2_reading
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (y : Term signature real [] argument) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:(x).φx.⊃.φy"
  parsed := .assertion (mixedImplication negation disjunction
    (.always universal phi) (phi.instantiate y))

/-- ✱9·2 is the general-to-particular inference later restated as ✱10·1.
The canonical block prints no demonstration, so the later primitive restatement
is used as the reconstruction.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_2
    (universal : signature.Universal argument matrixOrder)
    (negation : signature.Negation (bindOrder matrixOrder argument))
    (disjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (y : Term signature real [] argument) :
    Derivation (star_9_2_reading universal negation disjunction phi y).parsed := by
  have line1 := Derivation.star_10_1 universal negation disjunction phi y
  exact line1

def star_9_3_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(x).φx .∨. (x).φx : ⊃ . (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi phi) phi))

/-- The eliminable scope definitions reduce the printed proof to its
elementary `Taut` matrix and the final generalization.
`demonstration_provenance: follows-printed`. -/
theorem star_9_3 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_3_reading universal negation disjunction phi).parsed := by
  exact lift_star_1_2 universal negation disjunction phi

def star_9_23_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:(x).φx.⊃.(x).φx       [Id.✱9·13·21]"
  parsed := .assertion (implication negation disjunction
    (.always universal phi) (.always universal phi))

/-- ✱9·23.  The printed final `Id` is applied to the universally quantified
proposition; the preceding citations explain its formation.
`demonstration_provenance: follows-printed`. -/
theorem star_9_23 (universal : signature.Universal argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_23_reading universal negation disjunction phi).parsed := by
  have line1 := star_2_08 negation disjunction (.always universal phi)
  exact line1

def star_9_24_reading (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:(∃x).φx.⊃.(∃x).φx     [Id.✱9·13·22]"
  parsed := .assertion (implication negation disjunction
    (.sometimes existential phi) (.sometimes existential phi))

/-- ✱9·24.  The printed final `Id` is applied to the existentially quantified
proposition; the preceding citations explain its formation.
`demonstration_provenance: follows-printed`. -/
theorem star_9_24 (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_24_reading existential negation disjunction phi).parsed := by
  have line1 := star_2_08 negation disjunction (.sometimes existential phi)
  exact line1

def star_9_25_reading (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:.(x).p∨φx.⊃:p.∨.(x).φx   [Id.✱9·23.(✱9·04)]"
  parsed := .assertion (implication negation disjunction
    (.always universal (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) phi))
    (star_9_04 universal matrixDisjunction p phi))

/-- ✱9·25.  Both displayed sides unfold by ✱9·04 to the same scoped
formula, so PM's cited `Id` is literally the required instance.
`demonstration_provenance: follows-printed`. -/
theorem star_9_25 (universal : signature.Universal argument 0)
    (matrixDisjunction : signature.Disjunction 0)
    (negation : signature.Negation (bindOrder 0 argument))
    (disjunction : signature.Disjunction (bindOrder 0 argument))
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_25_reading universal matrixDisjunction negation disjunction p phi).parsed := by
  have line1 := star_9_23 universal negation disjunction
    (sameDisjunction matrixDisjunction
      (p.rename (fun v => .succ v)) phi)
  have line2 :
      Derivation (.assertion (implication negation disjunction
        (.always universal (sameDisjunction matrixDisjunction
          (p.rename (fun v => .succ v)) phi))
        (star_9_04 universal matrixDisjunction p phi))) := by
    rw [star_9_04_unfold]
    exact line1
  exact line2

/-- ✱9·32.  PM's line (1) is lifted by ✱9·13; ✱9·25 then moves
the closed member below the binder, and ✱9·03 supplies the final scoped
reading.  `demonstration_provenance: follows-printed`. -/
theorem star_9_32 (universal : signature.Universal argument 0)
    (matrixNegation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (scopeNegation : signature.Negation (bindOrder 0 argument))
    (scopeDisjunction : signature.Disjunction (bindOrder 0 argument))
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_32_reading universal matrixNegation matrixDisjunction
      q phi).parsed := by
  have line1 := lift_star_1_3_left universal matrixNegation
    matrixDisjunction q phi
  have line2 : Derivation (.assertion (.always universal
      (sameDisjunction matrixDisjunction
        ((Formula.neg matrixNegation q).rename (fun v => .succ v))
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v)))))) := by
    change Derivation (.assertion (.always universal
      (implication matrixNegation matrixDisjunction
        (q.rename (fun v => .succ v))
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v))))))
    exact line1
  have line3 : Derivation (.assertion (implication scopeNegation scopeDisjunction
      (.always universal (sameDisjunction matrixDisjunction
        ((Formula.neg matrixNegation q).rename (fun v => .succ v))
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v)))))
      (star_9_04 universal matrixDisjunction (.neg matrixNegation q)
        (sameDisjunction matrixDisjunction phi
          (q.rename (fun v => .succ v)))))) := by
    exact star_9_25 universal matrixDisjunction scopeNegation
      scopeDisjunction (.neg matrixNegation q)
      (sameDisjunction matrixDisjunction phi
        (q.rename (fun v => .succ v)))
  have line4 := Derivation.star_9_12_same scopeNegation scopeDisjunction
    line2 line3
  exact line4

def star_9_41_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p : ∨ : (x).φx .∨. r : .⊃ : .(x).φx : ∨ : p ∨ r"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_41 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_41_reading universal negation disjunction p r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction p.weakenReal r.weakenReal)) :=
    Derivation.star_1_5_same negation disjunction p.weakenReal
      (phi.weakenReal.instantiate value) r.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
        (sameDisjunction disjunction phi
          (sameDisjunction disjunction (p.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction p.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal))
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction p.weakenReal r.weakenReal)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
      (sameDisjunction disjunction phi
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  change ⊢ᵣ .always universal (implication negation disjunction
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v)))))
  exact line2

def star_9_42_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : (x).φx : ∨ : q ∨ r : .⊃ : .q : ∨ : (x).φx .∨. r"
  parsed := .assertion (.always universal (implication negation disjunction
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_9_42 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0) (phi : Formula signature real [argument] 0) :
    Derivation (star_9_42_reading universal negation disjunction q r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction q.weakenReal r.weakenReal))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal)) :=
    Derivation.star_1_5_same negation disjunction
      (phi.weakenReal.instantiate value) q.weakenReal r.weakenReal
  have matrixEq :
      (implication negation disjunction
        (sameDisjunction disjunction phi
          (sameDisjunction disjunction (q.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (sameDisjunction disjunction phi
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (sameDisjunction disjunction (phi.weakenReal.instantiate value)
          (sameDisjunction disjunction q.weakenReal r.weakenReal))
        (sameDisjunction disjunction q.weakenReal
          (sameDisjunction disjunction (phi.weakenReal.instantiate value) r.weakenReal)) := by
    rw [implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate, implication_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute, sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (sameDisjunction disjunction phi
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (r.rename (fun v => .succ v))))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  change ⊢ᵣ .always universal (implication negation disjunction
    (sameDisjunction disjunction phi
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))
    (sameDisjunction disjunction (q.rename (fun v => .succ v))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
  exact line2

def star_9_51_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p .⊃. (x).φx : ⊃ : .p ∨ r .⊃ .⊃ : (x).φx .∨. r"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction (p.rename (fun v => .succ v)) phi)
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v))
        (r.rename (fun v => .succ v)))
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v))))))

/-- `demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_51 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_51_reading universal negation disjunction p r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction p.weakenReal
          (phi.weakenReal.instantiate value))
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal r.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)) :=
    star_2_38 negation disjunction r.weakenReal p.weakenReal
      (phi.weakenReal.instantiate value)
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction (p.rename (fun v => .succ v)) phi)
        (implication negation disjunction
          (sameDisjunction disjunction (p.rename (fun v => .succ v))
            (r.rename (fun v => .succ v)))
          (sameDisjunction disjunction phi
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction p.weakenReal
          (phi.weakenReal.instantiate value))
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal r.weakenReal)
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution]
    rfl
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction (p.rename (fun v => .succ v)) phi)
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_31_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal1 : signature.Universal argument
      (max 0 (bindOrder 0 argument)))
    (universal2 : signature.Universal argument
      (bindOrder (max 0 (bindOrder 0 argument)) argument))
    (negation : signature.Negation 0)
    (matrixDisjunction : signature.Disjunction 0)
    (scopeDisjunction : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(∃x).φx .∨. (∃x).φx : ⊃ . (∃x).φx"
  parsed := .assertion (.always universal2 (.always universal1
    (mixedImplication negation scopeDisjunction
      (sameDisjunction matrixDisjunction
        (phi.rename star_9_3x_slotOuter)
        (phi.rename star_9_3x_slotInner))
      (.sometimes existential (phi.rename star_9_3x_slotThird)))))
  scopeReading := "This is printed line (3). Two applications of ✱9·03·02 read its universal binders as negated existential antecedents; recursive ✱9·05·06 then reads `(∃x).φx ∨ (∃y).φy` as the nested scoped matrix. The former raw `Taut` AST is not retained."

def star_9_33_reading
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .q .⊃ : (∃x).φx .∨. q   [Proof as above]"
  parsed := .assertion (star_9_06 existential disjunction (.neg negation q)
    (sameDisjunction disjunction phi (q.rename (fun v => .succ v))))
  scopeReading := "The outer implication is first read by ✱1·01; ✱9·06 moves its closed negated premiss below the existential, while the displayed member `(∃x).φx ∨ q` is read there by ✱9·05."

/-- ✱9·33, the existential analogue of the preceding printed proof.  A real
value supplies PM's free `x`; ✱9·1 introduces the scoped existential and
✱9·05/·06 are definitional readings only.
`demonstration_provenance: follows-printed`. -/
theorem star_9_33
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (scopeDisjunction : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0)
    (value : Term signature real [] argument) :
    Derivation (star_9_33_reading existential negation disjunction
      q phi).parsed := by
  let body := implication negation disjunction
    (q.rename (fun v => .succ v))
    (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))
  have closedQ :
      (q.rename (fun v => .succ v)).substitute
          (instantiateSubstitution value) = q := by
    rw [Formula.rename_substitute]
    apply Formula.substitute_eq_self
    intro sort v
    exact nomatch v
  have bodyAtValue : body.instantiate value =
      implication negation disjunction q
        (sameDisjunction disjunction (phi.instantiate value) q) := by
    unfold body Formula.instantiate
    rw [implication_substitute, sameDisjunction_substitute, closedQ]
  have line1 := Derivation.star_1_3_same negation disjunction
    (phi.instantiate value) q
  have line2 : Derivation (.assertion (body.instantiate value)) :=
    Derivation.castAssertion bodyAtValue line1
  have line3 := Derivation.star_9_1 existential negation scopeDisjunction
    body value
  have line4 := Derivation.star_9_12 negation scopeDisjunction line2 line3
  change Derivation (.assertion (star_9_06 existential disjunction
    (.neg negation q)
    (sameDisjunction disjunction phi (q.rename (fun v => .succ v)))))
  rw [star_9_06_unfold]
  change Derivation (.assertion (.sometimes existential body))
  exact line4

def star_9_35_reading
    (existential : ExistentialVocabulary signature argument 0)
    (universal : signature.Universal argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : .(∃x).φx .⊃ : p .∨. (∃x).φx   [Proof as above]"
  parsed := .assertion (star_9_07 existential universal disjunction
    (.neg negation (phi.rename star_9_3x_slotOuter))
    (sameDisjunction disjunction
      (p.rename (fun v => .succ (.succ v)))
      (phi.rename star_9_3x_slotInner)))
  scopeReading := "The antecedent negation is ✱9·02, `p ∨ (∃x).φx` is ✱9·06, and ✱9·07 combines the resulting universal and existential members. The raw higher-order `Add` tree is deliberately not used."

def star_9_5_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : p ⊃ q .⊃ : .p .∨. (x).φx : ⊃ : q .∨. (x).φx"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction (p.rename (fun v => .succ v))
      (q.rename (fun v => .succ v)))
    (implication negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi))))

/-- PM's first line is reconstructed by the derived right-summation form of
`Sum`, then lifted through ✱9·13.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_5 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (p q : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_5_reading universal negation disjunction p q phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction p.weakenReal q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate value))) :=
    star_2_38 negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal q.weakenReal
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction (p.rename (fun v => .succ v))
          (q.rename (fun v => .succ v)))
        (implication negation disjunction
          (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
          (sameDisjunction disjunction
            (q.rename (fun v => .succ v)) phi))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction p.weakenReal q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction p.weakenReal
            (phi.weakenReal.instantiate value))
          (sameDisjunction disjunction q.weakenReal
            (phi.weakenReal.instantiate value))) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution, Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction (p.rename (fun v => .succ v))
        (q.rename (fun v => .succ v)))
      (implication negation disjunction
        (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
        (sameDisjunction disjunction (q.rename (fun v => .succ v)) phi)))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_52_reading (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢ : : (x).φx .⊃. q : ⊃ : .(x).φx .∨. r .⊃ . q ∨ r"
  parsed := .assertion (.always universal (implication negation disjunction
    (implication negation disjunction phi (q.rename (fun v => .succ v)))
    (implication negation disjunction
      (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
      (sameDisjunction disjunction (q.rename (fun v => .succ v))
        (r.rename (fun v => .succ v))))))

/-- PM's first line is reconstructed by the derived right-summation form of
`Sum`, then lifted through ✱9·13.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_9_52 (universal : signature.Universal argument 0)
    (negation : signature.Negation 0) (disjunction : signature.Disjunction 0)
    (q r : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    Derivation (star_9_52_reading universal negation disjunction q r phi).parsed := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have line1 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value) q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)
          (sameDisjunction disjunction q.weakenReal r.weakenReal)) :=
    star_2_38 negation disjunction r.weakenReal
      (phi.weakenReal.instantiate value) q.weakenReal
  have matrixEq :
      (implication negation disjunction
        (implication negation disjunction phi
          (q.rename (fun v => .succ v)))
        (implication negation disjunction
          (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
          (sameDisjunction disjunction (q.rename (fun v => .succ v))
            (r.rename (fun v => .succ v))))).weakenReal.instantiate value =
      implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate value) q.weakenReal)
        (implication negation disjunction
          (sameDisjunction disjunction
            (phi.weakenReal.instantiate value) r.weakenReal)
          (sameDisjunction disjunction q.weakenReal r.weakenReal)) := by
    rw [implication_weakenReal, implication_weakenReal,
      implication_weakenReal, sameDisjunction_weakenReal,
      sameDisjunction_weakenReal, Formula.instantiate,
      implication_substitute, implication_substitute,
      implication_substitute, sameDisjunction_substitute,
      sameDisjunction_substitute,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.closed_weakenReal_instantiateSubstitution,
      Formula.instantiate]
  have line2 := Derivation.star_9_13 universal
    (implication negation disjunction
      (implication negation disjunction phi (q.rename (fun v => .succ v)))
      (implication negation disjunction
        (sameDisjunction disjunction phi (r.rename (fun v => .succ v)))
        (sameDisjunction disjunction (q.rename (fun v => .succ v))
          (r.rename (fun v => .succ v)))))
    (Derivation.castAssertion matrixEq line1)
  exact line2

def star_9_61_reading
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Star9Reading signature real where
  printed := PM.pmPrinted "If φx̂ and ψx̂ are elementary functions of the same type, there is a function φx̂ ∨ ψx̂."
  parsed := .functionExistence (sameDisjunction disjunction phi psi)

/-- ✱9·61. Intrinsic typing supplies PM's same-type hypothesis, and the
printed appeal to ✱9·15 is the primitive function-existence constructor.
`demonstration_provenance: follows-printed`. -/
theorem star_9_61
    (disjunction : signature.Disjunction matrixOrder)
    (phi psi : Formula signature real [argument] matrixOrder) :
    Derivation (star_9_61_reading disjunction phi psi).parsed := by
  have line1 := Derivation.star_10_121 psi
  have line2 := Derivation.star_10_121 phi
  have line3 := Derivation.star_10_121
    (sameDisjunction disjunction phi psi)
  have line4 := Derivation.star_10_122
    (sameDisjunction disjunction phi psi)
  exact line4

/-- The two function matrices printed at ✱9·62.  The index lets one theorem
assert both heterogeneous `Claim.functionExistence` conclusions without
adding a conjunction or a new constructor to the object calculus. -/
inductive Star9_62Branch where
  | universal
  | existential

def star_9_62_matrix
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Formula signature real [leftArgument] (bindOrder 0 rightArgument) :=
  Star9_62Branch.casesOn branch
    (.always universal (sameDisjunction disjunction phi
      (psi.rename (fun v => .succ v))))
    (.sometimes existential (sameDisjunction disjunction phi
      (psi.rename (fun v => .succ v))))

def star_9_62_reading
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Star9Reading signature real where
  printed := PM.pmPrinted "If φ(x̂, ŷ) and ψẑ are elementary functions, and the x-argument to φ is of the same type as the argument to ψ, there are functions (y).φ(x̂,y).∨.ψx̂, (∃y).φ(x̂,y).∨.ψx̂."
  parsed := .functionExistence
    (star_9_62_matrix universal existential disjunction phi psi branch)

/-- ✱9·62, for each of the two function matrices named in print.  Intrinsic
sorting supplies the same-type premise; ✱10·121/·122 are the ramified forms
of the cited ✱9·14/·15 formation steps.
`demonstration_provenance: follows-printed`. -/
theorem star_9_62
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction 0)
    (phi : Formula signature real [rightArgument, leftArgument] 0)
    (psi : Formula signature real [leftArgument] 0)
    (branch : Star9_62Branch) :
    Derivation (star_9_62_reading universal existential disjunction
      phi psi branch).parsed := by
  have line1 := Derivation.star_10_121
    (star_9_62_matrix universal existential disjunction phi psi branch)
  have line2 := Derivation.star_10_122
    (star_9_62_matrix universal existential disjunction phi psi branch)
  exact line2

/-- The four always/sometimes combinations covered by PM's “etc.” at ✱9·63. -/
inductive Star9_63Branch where
  | universalUniversal
  | universalExistential
  | existentialUniversal
  | existentialExistential

def star_9_63_matrix
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Formula signature real [leftArgument] (bindOrder 0 rightArgument) :=
  Star9_63Branch.casesOn branch
    (sameDisjunction disjunction (.always universal phi) (.always universal psi))
    (sameDisjunction disjunction (.always universal phi) (.sometimes existential psi))
    (sameDisjunction disjunction (.sometimes existential phi) (.always universal psi))
    (sameDisjunction disjunction (.sometimes existential phi) (.sometimes existential psi))

def star_9_63_reading
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Star9Reading signature real where
  printed := PM.pmPrinted "If φ(x̂, ŷ), ψ(x̂, ŷ) are elementary functions of the same type, there are functions (y).φ(x̂,y).∨.(z).ψ(x̂,z), etc.  [Proof as above]"
  parsed := .functionExistence
    (star_9_63_matrix universal existential disjunction phi psi branch)

/-- ✱9·63, uniformly for all four branches meant by “etc.”.  The formation
claim stays inside `Derivation` and introduces no extra primitive.
`demonstration_provenance: follows-printed`. -/
theorem star_9_63
    (universal : signature.Universal rightArgument 0)
    (existential : ExistentialVocabulary signature rightArgument 0)
    (disjunction : signature.Disjunction (bindOrder 0 rightArgument))
    (phi psi : Formula signature real [rightArgument, leftArgument] 0)
    (branch : Star9_63Branch) :
    Derivation (star_9_63_reading universal existential disjunction
      phi psi branch).parsed := by
  have line1 := Derivation.star_10_121
    (star_9_63_matrix universal existential disjunction phi psi branch)
  have line2 := Derivation.star_10_122
    (star_9_63_matrix universal existential disjunction phi psi branch)
  exact line2

section Star922

variable {signature : Signature} {real : Context} {argument : RSort}

private def s9ComposeSubstitution
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    Substitution signature real source target :=
  fun v => (sigma v).substitute tau

private theorem Term.s9_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (term : Term signature real source sort) :
    (term.substitute sigma).substitute tau =
      term.substitute (s9ComposeSubstitution sigma tau) := by
  cases term <;> rfl

private theorem Arguments.s9_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (arguments : Arguments signature real source sorts) :
    (arguments.substitute sigma).substitute tau =
      arguments.substitute (s9ComposeSubstitution sigma tau) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.s9_substitute_substitute, ih]

private theorem Term.s9_weaken_substitute_lift
    (tau : Substitution signature real middle target)
    (term : Term signature real middle sort) :
    term.weaken.substitute (liftSubstitution (sort := binder) tau) =
      (term.substitute tau).weaken := by
  cases term <;> rfl

private theorem s9_lift_comp_pointwise
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binder :: source) sort),
      (liftSubstitution sigma v).substitute (liftSubstitution tau) =
        liftSubstitution (s9ComposeSubstitution sigma tau) v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact Term.s9_weaken_substitute_lift tau (sigma v)

private theorem s9_liftN_comp_pointwise
    (binders : List RSort)
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      (liftSubstitutionN binders sigma v).substitute
          (liftSubstitutionN binders tau) =
        liftSubstitutionN binders (s9ComposeSubstitution sigma tau) v := by
  induction binders with
  | nil =>
      intro sort v
      rfl
  | cons binder binders ih =>
      intro sort v
      cases v with
      | zero => rfl
      | succ v =>
          exact Eq.trans
            (Term.s9_weaken_substitute_lift (liftSubstitutionN binders tau)
              (liftSubstitutionN binders sigma v))
            (congrArg Term.weaken (ih v))

private theorem s9_lift_congr
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binder :: source) sort),
      liftSubstitution sigma v = liftSubstitution tau v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Term.weaken (pointwise v)

private theorem s9_liftN_congr
    (binders : List RSort)
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftSubstitutionN binders sigma v = liftSubstitutionN binders tau v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih => exact s9_lift_congr _ _ ih

private theorem Term.s9_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (term : Term signature real source sort) :
    term.substitute sigma = term.substitute tau := by
  cases term with
  | real v => rfl
  | apparent v => exact pointwise v
  | symbol payload => rfl

private theorem Arguments.s9_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (arguments : Arguments signature real source sorts) :
    arguments.substitute sigma = arguments.substitute tau := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.s9_substitute_of_pointwise sigma tau pointwise, ih]

private theorem Formula.s9_substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (formula : Formula signature real source order) :
    formula.substitute sigma = formula.substitute tau := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.s9_substitute_of_pointwise sigma tau pointwise]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.s9_substitute_of_pointwise sigma tau pointwise,
        Arguments.s9_substitute_of_pointwise sigma tau pointwise]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      exact congrArg (Formula.neg meaning) (ih sigma tau pointwise)
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH sigma tau pointwise, rightIH sigma tau pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      exact congrArg (Formula.always meaning)
        (ih (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise))
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau)
          (s9_liftN_congr parameters sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (s9_lift_congr sigma tau pointwise)]

private theorem Formula.s9_substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (formula : Formula signature real source order) :
    (formula.substitute sigma).substitute tau =
      formula.substitute (s9ComposeSubstitution sigma tau) := by
  induction formula generalizing middle target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.s9_substitute_substitute]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.s9_substitute_substitute, Arguments.s9_substitute_substitute]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH, rightIH]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      have line1 := ih (liftSubstitution sigma) (liftSubstitution tau)
      have line2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) body
      exact congrArg (Formula.always meaning) (Eq.trans line1 line2)
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      have matrixLine1 := matrixIH (liftSubstitutionN parameters sigma)
        (liftSubstitutionN parameters tau)
      have matrixLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau))
        (liftSubstitutionN parameters (s9ComposeSubstitution sigma tau))
        (s9_liftN_comp_pointwise parameters sigma tau) matrix
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextMatrix => Formula.incompleteScope kind parameters
          resultOrder excess scopeOrder nextMatrix
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans matrixLine1 matrixLine2))
        (congrArg (Formula.incompleteScope kind parameters resultOrder excess
          scopeOrder
          (matrix.substitute
            (liftSubstitutionN parameters (s9ComposeSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      have conditionLine1 := conditionIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have conditionLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) condition
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := Formula.s9_substitute_of_pointwise
        (s9ComposeSubstitution (liftSubstitution sigma) (liftSubstitution tau))
        (liftSubstitution (s9ComposeSubstitution sigma tau))
        (s9_lift_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextCondition => Formula.descriptionScope sort
          conditionOrder scopeOrder nextCondition
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans conditionLine1 conditionLine2))
        (congrArg (Formula.descriptionScope sort conditionOrder scopeOrder
          (condition.substitute
            (liftSubstitution (s9ComposeSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))
private def star_9_22_slotY : Renaming [argument] [argument, argument, argument]
  | _, .zero => .succ (.succ .zero)
  | _, .succ v => nomatch v

private def star_9_22_slotX : Renaming [argument] [argument, argument, argument]
  | _, .zero => .succ .zero
  | _, .succ v => nomatch v

private def star_9_22_slotZ : Renaming [argument] [argument, argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

def star_9_22_matrix
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real [argument, argument, argument] 0 :=
  implication negation disjunction
    (implication negation disjunction
      (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX))
    (implication negation disjunction
      (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ))

private def star_9_22_matrixReal
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature (argument :: real) [argument, argument] 0 :=
  (star_9_22_matrix negation disjunction phi psi).weakenReal.substitute
    (liftSubstitution (liftSubstitution
      (instantiateSubstitution
        (.real (.zero : Var (argument :: real) argument)))))

private def star_9_22_bodyY
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature (argument :: real) [argument] 0 :=
  (star_9_22_matrixReal negation disjunction phi psi).substitute
    (liftSubstitution
      (instantiateSubstitution
        (.real (.zero : Var (argument :: real) argument))))

theorem star_9_22_matrix_all_real
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    (star_9_22_bodyY negation disjunction phi psi).instantiate
      (.real (.zero : Var (argument :: real) argument)) =
      implication negation disjunction
        (implication negation disjunction
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero)))
        (implication negation disjunction
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero))) := by
  unfold star_9_22_bodyY star_9_22_matrixReal Formula.instantiate
  rw [Formula.s9_substitute_substitute, Formula.s9_substitute_substitute]
  unfold star_9_22_matrix
  rw [implication_weakenReal, implication_weakenReal,
    implication_weakenReal, Formula.weakenReal_rename,
    Formula.weakenReal_rename, Formula.weakenReal_rename,
    Formula.weakenReal_rename, implication_substitute,
    implication_substitute, implication_substitute,
    Formula.rename_substitute, Formula.rename_substitute,
    Formula.rename_substitute, Formula.rename_substitute]
  let z : Term signature (argument :: real) [] argument := .real .zero
  let sigmaZ : Substitution signature (argument :: real)
      [argument, argument, argument] [argument, argument] :=
    liftSubstitution (liftSubstitution (instantiateSubstitution z))
  let sigmaX : Substitution signature (argument :: real)
      [argument, argument] [argument] :=
    liftSubstitution (instantiateSubstitution z)
  let sigmaY : Substitution signature (argument :: real) [argument] [] :=
    instantiateSubstitution z
  let sigmaAll : Substitution signature (argument :: real)
      [argument, argument, argument] [] :=
    fun v => s9ComposeSubstitution sigmaZ
      (s9ComposeSubstitution sigmaX sigmaY) v
  have slotXPhi :
      phi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotX sigmaAll) =
        phi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have slotXPsi :
      psi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotX sigmaAll) =
        psi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have slotYPhi :
      phi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotY sigmaAll) =
        phi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have slotZPsi :
      psi.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_slotZ sigmaAll) =
        psi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  rw [slotXPhi, slotXPsi, slotYPhi, slotZPsi]

private def star_9_22_bodyX
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature (argument :: real) [argument] (bindOrder 0 argument) :=
  .sometimes existential (star_9_22_matrixReal negation disjunction phi psi)

def star_9_22_body
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real [argument]
      (bindOrder (bindOrder 0 argument) argument) :=
  .sometimes existential1
    (.sometimes existential0 (star_9_22_matrix negation disjunction phi psi))

/-- The independently scoped consequent printed inside ✱9·22:
`(exists x).phi x implies (exists x).psi x`.  Its universal binder is ✱9·02,
its existential binder is ✱9·07, and the two bound variables remain
distinct in the matrix. -/
def star_9_22_consequent
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real []
      (bindOrder (bindOrder 0 argument) argument) :=
  .always existential1.universal
    (.sometimes existential0
      (implication negation disjunction
        (phi.rename star_9_3x_slotOuter)
        (psi.rename star_9_3x_slotInner)))

theorem star_9_22_bodyX_at_z
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    (star_9_22_bodyX existential negation disjunction phi psi).instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      .sometimes existential (star_9_22_bodyY negation disjunction phi psi) := by
  rfl

theorem star_9_22_body_at_z
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    (star_9_22_body existential0 existential1 negation disjunction phi psi).weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      .sometimes existential1
        (star_9_22_bodyX existential0 negation disjunction phi psi) := by
  rfl


def star_9_22_reading
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:.(x).φx⊃ψx.⊃:.(∃x).φx.⊃.(∃x).ψx"
  parsed := .assertion (.always universal2
    (star_9_22_body existential0 existential1
      negation0 disjunction0 phi psi))
  scopeReading := "The parsed AST is printed line (4), which PM identifies with the displayed proposition by the eliminable scope definitions ✱9·06, ✱9·08, ✱9·07, ✱9·01, and ✱9·02."

/-! ### The fixed-premiss instance used on line (3) of ✱10·35

The two quantified variables below remain distinct in the displayed formula:
the outer universal variable occurs in `phi`, and the inner existential
variable occurs in `psi`.  Only the real witness used in the proof identifies
them, exactly as in PM's proof of ✱9·22. -/

private def star_9_22_fixedClosed : Renaming [] [argument, argument] :=
  fun v => nomatch v

/-- Matrix of `p ⊃ (phi y ⊃ psi x)`, with `x` and `y` independently
bound. -/
def star_9_22_fixedMatrix
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real [argument, argument] 0 :=
  implication negation disjunction
    (p.rename star_9_22_fixedClosed)
    (implication negation disjunction
      (phi.rename star_9_3x_slotOuter)
      (psi.rename star_9_3x_slotInner))

private def star_9_22_fixedMatrixReal
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature (argument :: real) [argument] 0 :=
  (star_9_22_fixedMatrix negation disjunction p phi psi).weakenReal.substitute
    (liftSubstitution
      (instantiateSubstitution
        (.real (.zero : Var (argument :: real) argument))))

private def star_9_22_fixedBody
    (existential : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature (argument :: real) [] (bindOrder 0 argument) :=
  .sometimes existential
    (star_9_22_fixedMatrixReal negation disjunction p phi psi)

/-- Full-scope tree of the printed proposition
`p ⊃ ((∃x).phi x ⊃ (∃x).psi x)`. -/
def star_9_22_fixedConsequent
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real []
      (bindOrder (bindOrder 0 argument) argument) :=
  .always existential1.universal
    (.sometimes existential0
      (star_9_22_fixedMatrix negation disjunction p phi psi))

theorem star_9_22_fixedMatrix_all_real
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    (star_9_22_fixedMatrixReal negation disjunction p phi psi).instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      implication negation disjunction p.weakenReal
        (implication negation disjunction
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero))) := by
  unfold star_9_22_fixedMatrixReal Formula.instantiate
  rw [Formula.s9_substitute_substitute]
  unfold star_9_22_fixedMatrix
  rw [implication_weakenReal, implication_weakenReal,
    Formula.weakenReal_rename, Formula.weakenReal_rename,
    Formula.weakenReal_rename, implication_substitute,
    implication_substitute, Formula.rename_substitute,
    Formula.rename_substitute, Formula.rename_substitute]
  let z : Term signature (argument :: real) [] argument := .real .zero
  let sigmaOuter : Substitution signature (argument :: real)
      [argument, argument] [argument] :=
    liftSubstitution (instantiateSubstitution z)
  let sigmaInner : Substitution signature (argument :: real) [argument] [] :=
    instantiateSubstitution z
  let sigmaAll : Substitution signature (argument :: real)
      [argument, argument] [] :=
    fun v => s9ComposeSubstitution sigmaOuter sigmaInner v
  have fixedP :
      p.weakenReal.substitute
          (substitutionAfterRenaming star_9_22_fixedClosed sigmaAll) =
        p.weakenReal := by
    apply Formula.substitute_eq_self
    intro sort v
    exact nomatch v
  have outerPhi :
      phi.weakenReal.substitute
          (substitutionAfterRenaming star_9_3x_slotOuter sigmaAll) =
        phi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  have innerPsi :
      psi.weakenReal.substitute
          (substitutionAfterRenaming star_9_3x_slotInner sigmaAll) =
        psi.weakenReal.substitute (instantiateSubstitution z) := by
    apply Formula.s9_substitute_of_pointwise
    intro sort v
    cases v with
    | zero => rfl
    | succ v => exact nomatch v
  rw [fixedP, outerPhi, innerPsi]

private theorem star_9_22_fixedBody_at_z
    (existential0 : ExistentialVocabulary signature argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0) :
    ((Formula.sometimes existential0
        (star_9_22_fixedMatrix negation disjunction p phi psi)).weakenReal).instantiate
        (.real (.zero : Var (argument :: real) argument)) =
      star_9_22_fixedBody existential0 negation disjunction p phi psi := by
  rfl

/-- The fixed-premiss consequence of ✱9·22 used by PM at ✱10·35(3).
The input proof is the diagonal matrix; ✱9·1 introduces the existential
output and ✱9·13 generalizes the independently retained input variable. -/
theorem star_9_22_under_fixed
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (disjunction01 : signature.Disjunction
      (max 0 (bindOrder 0 argument)))
    (p : Formula signature real [] 0)
    (phi psi : Formula signature real [argument] 0)
    (line1 : Derivation (.assertion
      (implication negation0 disjunction0 p.weakenReal
        (implication negation0 disjunction0
          (phi.weakenReal.instantiate (.real .zero))
          (psi.weakenReal.instantiate (.real .zero)))))) :
    Derivation (.assertion
      (star_9_22_fixedConsequent existential0 existential1 negation0
        disjunction0 p phi psi)) := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  have matrixLine : Derivation (.assertion
      ((star_9_22_fixedMatrixReal negation0 disjunction0 p phi psi).instantiate
        z)) :=
    Derivation.castAssertion
      (star_9_22_fixedMatrix_all_real negation0 disjunction0 p phi psi)
      line1
  have existentialLine : Derivation (.assertion
      (star_9_22_fixedBody existential0 negation0 disjunction0 p phi psi)) :=
    Derivation.star_9_12 negation0 disjunction01 matrixLine
      (Derivation.star_9_1 existential0 negation0 disjunction01
        (star_9_22_fixedMatrixReal negation0 disjunction0 p phi psi) z)
  exact Derivation.star_9_13 existential1.universal
    (.sometimes existential0
      (star_9_22_fixedMatrix negation0 disjunction0 p phi psi))
    (Derivation.castAssertion
      (star_9_22_fixedBody_at_z existential0 negation0
        disjunction0 p phi psi).symm existentialLine)

end Star922

private def star_9_21_renamingSubstitution
    {signature : Signature} {realCtx : Context}
    (rho : Renaming source target) :
    Substitution signature realCtx source target :=
  fun v => .apparent (rho v)

private theorem Term.star_9_21_rename_as_substitute
    (rho : Renaming source target)
    (term : Term signature realCtx source sort) :
    term.rename rho = term.substitute (star_9_21_renamingSubstitution rho) := by
  cases term <;> rfl

private theorem Arguments.star_9_21_rename_as_substitute
    (rho : Renaming source target)
    (arguments : Arguments signature realCtx source sorts) :
    arguments.rename rho =
      arguments.substitute (star_9_21_renamingSubstitution rho) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.star_9_21_rename_as_substitute, ih]

private theorem star_9_21_lift_renamingSubstitution
    {signature : Signature} {realCtx : Context}
    (rho : Renaming source target) :
    ∀ {sort} (v : Var (binder :: source) sort),
      star_9_21_renamingSubstitution (signature := signature)
          (realCtx := realCtx) (liftRenaming rho) v =
        liftSubstitution (star_9_21_renamingSubstitution
          (signature := signature) (realCtx := realCtx) rho) v := by
  intro sort v
  cases v <;> rfl

private theorem star_9_21_liftN_renamingSubstitution
    {signature : Signature} {realCtx : Context}
    (binders : List RSort) (rho : Renaming source target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      star_9_21_renamingSubstitution (signature := signature)
          (realCtx := realCtx) (liftRenamingN binders rho) v =
        liftSubstitutionN binders (star_9_21_renamingSubstitution
          (signature := signature) (realCtx := realCtx) rho) v := by
  induction binders with
  | nil =>
      intro sort v
      rfl
  | cons binder binders ih =>
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact congrArg Term.weaken (ih v)

private theorem Formula.star_9_21_rename_as_substitute
    (rho : Renaming source target)
    (formula : Formula signature realCtx source order) :
    formula.rename rho =
      formula.substitute (star_9_21_renamingSubstitution rho) := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.star_9_21_rename_as_substitute]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.star_9_21_rename_as_substitute,
        Arguments.star_9_21_rename_as_substitute]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      exact congrArg (Formula.neg meaning) (ih rho)
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH rho, rightIH rho]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      rw [ih (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho)]
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftRenamingN parameters rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenamingN parameters rho))
          (liftSubstitutionN parameters (star_9_21_renamingSubstitution rho))
          (star_9_21_liftN_renamingSubstitution parameters rho),
        continuationIH (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho),
        continuationIH (liftRenaming rho),
        Formula.s9_substitute_of_pointwise
          (star_9_21_renamingSubstitution (liftRenaming rho))
          (liftSubstitution (star_9_21_renamingSubstitution rho))
          (star_9_21_lift_renamingSubstitution rho)]

private theorem Formula.star_9_21_rename_rename
    (rho : Renaming source middle)
    (tau : Renaming middle target)
    (formula : Formula signature realCtx source order) :
    (formula.rename rho).rename tau =
      formula.rename (fun v => tau (rho v)) := by
  rw [Formula.star_9_21_rename_as_substitute,
    Formula.rename_substitute,
    Formula.star_9_21_rename_as_substitute]
  apply Formula.s9_substitute_of_pointwise
  intro sort v
  rfl

private theorem Formula.star_9_21_rename_of_pointwise
    (rho tau : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = tau v)
    (formula : Formula signature realCtx source order) :
    formula.rename rho = formula.rename tau := by
  rw [Formula.star_9_21_rename_as_substitute,
    Formula.star_9_21_rename_as_substitute]
  apply Formula.s9_substitute_of_pointwise
  intro sort v
  exact congrArg Term.apparent (pointwise v)

private def star_9_21_slotX : Renaming [argument] [argument, argument]
  | _, .zero => .zero
  | _, .succ v => nomatch v

private theorem Formula.star_9_21_slotX_rename
    (formula : Formula signature real [argument] order) :
    formula.rename (fun v => .succ (star_9_21_slotX v)) =
      formula.rename star_9_22_slotX := by
  apply Formula.star_9_21_rename_of_pointwise
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact nomatch v

private theorem star_9_21_fixed_rename
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    (Formula.neg negation (implication negation disjunction
      (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX))).rename
        (fun v => .succ v) =
      .neg negation (implication negation disjunction
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX)) := by
  rw [Formula.star_9_21_rename_as_substitute]
  change Formula.neg negation
    ((implication negation disjunction
      (phi.rename star_9_21_slotX)
      (psi.rename star_9_21_slotX)).substitute _) = _
  rw [implication_substitute]
  rw [← Formula.star_9_21_rename_as_substitute,
    ← Formula.star_9_21_rename_as_substitute]
  rw [Formula.star_9_21_rename_rename,
    Formula.star_9_21_rename_rename]
  rw [Formula.star_9_21_slotX_rename,
    Formula.star_9_21_slotX_rename]

private theorem Formula.star_9_22_implication_rename
    (rho : Renaming source target)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order) :
    (implication negation disjunction left right).rename rho =
      implication negation disjunction (left.rename rho) (right.rename rho) := by
  rw [Formula.star_9_21_rename_as_substitute]
  rw [implication_substitute]
  rw [← Formula.star_9_21_rename_as_substitute,
    ← Formula.star_9_21_rename_as_substitute]

private theorem star_9_22_premiss_scope_rename
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    ((Formula.neg negation (implication negation disjunction phi psi)).rename
        (liftRenaming (fun v => .succ v))).rename (fun v => .succ v) =
      Formula.neg negation (implication negation disjunction
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX)) := by
  rw [Formula.star_9_21_rename_rename]
  have renameEq :
      (Formula.neg negation (implication negation disjunction phi psi)).rename
          (fun v => (liftRenaming (fun v => .succ v) v).succ) =
        (Formula.neg negation (implication negation disjunction phi psi)).rename
          star_9_22_slotX :=
    Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) _
  rw [renameEq]
  change Formula.neg negation
    ((implication negation disjunction phi psi).rename star_9_22_slotX) = _
  rw [Formula.star_9_22_implication_rename]

private theorem star_9_22_consequent_scope_rename
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    (implication negation disjunction
      (phi.rename star_9_3x_slotOuter)
      (psi.rename star_9_3x_slotInner)).rename
        (liftRenaming (fun v => .succ v)) =
      implication negation disjunction
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ) := by
  rw [Formula.star_9_22_implication_rename]
  rw [Formula.star_9_21_rename_rename,
    Formula.star_9_21_rename_rename]
  have innerEq :
      phi.rename (fun v =>
        liftRenaming (fun v => .succ v) (star_9_3x_slotOuter v)) =
        phi.rename star_9_22_slotY :=
    Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) phi
  have outerEq :
      psi.rename (fun v =>
        liftRenaming (fun v => .succ v) (star_9_3x_slotInner v)) =
        psi.rename star_9_22_slotZ :=
    Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) psi
  rw [innerEq, outerEq]

private theorem star_9_22_consequent_eq_star_9_07
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi =
      star_9_07 existential0 existential1.universal disjunction0
        ((Formula.neg negation0 phi).rename (fun v => .succ v))
        (psi.rename implicationScopeHead) := by
  unfold star_9_22_consequent star_9_07 implication mixedImplication
  have phiRename :
      (Formula.neg negation0 phi).rename (fun v => .succ v) =
        Formula.neg negation0 (phi.rename star_9_3x_slotOuter) := by
    change Formula.neg negation0 (phi.rename (fun v => .succ v)) = _
    exact congrArg (Formula.neg negation0)
      (Formula.star_9_21_rename_of_pointwise _ _ (by
        intro sort v
        cases v with
        | zero => rfl
        | succ v => exact nomatch v) phi)
  have psiRename :
      psi.rename implicationScopeHead =
        psi.rename star_9_3x_slotInner := by
    exact Formula.star_9_21_rename_of_pointwise _ _ (by
      intro sort v
      cases v with
      | zero => rfl
      | succ v => exact nomatch v) psi
  rw [phiRename, psiRename]

/-- The full-scope reading which makes ✱9·22 detachable by the single
primitive rule ✱9·12.  Reading the negated universal premiss uses ✱9·01;
the quantified disjunction then follows ✱9·04, ✱9·05 and ✱9·06. -/
@[reducible] def star_9_22_implicationReading
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (negation1 : signature.Negation (bindOrder 0 argument))
    (disjunction12 : signature.Disjunction
      (max (bindOrder 0 argument)
        (bindOrder (bindOrder 0 argument) argument)))
    (phi psi : Formula signature real [argument] 0) :
    ImplicationReading negation1 disjunction12
      (.always existential0.universal
        (implication negation0 disjunction0 phi psi))
      (.always universal2
        (star_9_22_body existential0 existential1
          negation0 disjunction0 phi psi))
      (star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi) := by
  let premissMatrix := implication negation0 disjunction0 phi psi
  let negatedPremiss := star_9_01 existential0 negation0 premissMatrix
  refine {
    negated := negatedPremiss
    negationDefinition := ?_
    disjunctionDefinition := ?_
  }
  · exact ImplicationNegation.star_9_01 negation1
      existential0.universal existential0 negation0 premissMatrix
  · unfold negatedPremiss premissMatrix star_9_22_consequent
    unfold star_9_22_body
    apply ImplicationDisjunction.star_9_04
      existential1.universal universal2
    apply ImplicationDisjunction.star_9_05 existential0 existential1
    apply ImplicationDisjunction.star_9_06 existential0 existential0
    rw [star_9_22_premiss_scope_rename,
      star_9_22_consequent_scope_rename]
    unfold star_9_22_matrix
    exact ImplicationDisjunction.star_1_01_same disjunction0
      (.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX)))
      (implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ))

private def star_9_22_line6Left
    (existential0 : ExistentialVocabulary signature argument 0)
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real [argument] (bindOrder 0 argument) :=
  .sometimes existential0
    (.neg negation0
      (implication negation0 disjunction0
        (phi.rename star_9_3x_slotOuter)
        (psi.rename star_9_3x_slotOuter)))

private def star_9_22_line6Right
    (existential0 : ExistentialVocabulary signature argument 0)
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real [argument] (bindOrder 0 argument) :=
  .sometimes existential0
    (implication negation0 disjunction0
      (phi.rename star_9_3x_slotOuter)
      (psi.rename star_9_3x_slotInner))

/-- The proof line together with the three scope readings printed after it.
`Derivation` stores only the expanded formula, so the readings are retained
beside line (4) to record the eliminable steps ✱9·08, ✱9·07 and ✱9·01·02. -/
private structure Star922PrintedDemonstration
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (negation1 : signature.Negation (bindOrder 0 argument))
    (disjunction1 : signature.Disjunction (bindOrder 0 argument))
    (disjunction11 : signature.Disjunction
      (max (bindOrder 0 argument) (bindOrder 0 argument)))
    (disjunction12 : signature.Disjunction
      (max (bindOrder 0 argument)
        (bindOrder (bindOrder 0 argument) argument)))
    (phi psi : Formula signature real [argument] 0) where
  line4 : Derivation (.assertion (.always universal2
    (star_9_22_body existential0 existential1
      negation0 disjunction0 phi psi)))
  line5 : ImplicationReading negation1 disjunction12
    (.always existential0.universal
      (implication negation0 disjunction0 phi psi))
    (.always universal2
      (star_9_22_body existential0 existential1
        negation0 disjunction0 phi psi))
    (star_9_22_consequent existential0 existential1
      negation0 disjunction0 phi psi)
  line6 : ImplicationDisjunction signature real
    (.sometimes existential1
      (star_9_22_line6Left existential0 negation0 disjunction0 phi psi))
    (.always existential1.universal
      (star_9_22_line6Right existential0 negation0 disjunction0 phi psi))
    (star_9_08 existential1 universal2 disjunction1
      ((star_9_22_line6Left existential0 negation0 disjunction0 phi psi).rename
        implicationScopeHead)
      ((star_9_22_line6Right existential0 negation0 disjunction0 phi psi).rename
        (fun v => .succ v)))
  line7 : ImplicationReading negation1 disjunction11
    (.sometimes existential0 phi)
    (star_9_22_consequent existential0 existential1
      negation0 disjunction0 phi psi)
    (.sometimes existential0 psi)

/-- ✱9·22. Lines 1–4 are PM's printed Id, two existential
introductions with detachment, and real-to-apparent generalization. Lines
5–7 retain the exact scope-definition certificates, including the final
✱9·01·02 reading of the displayed implication.
`demonstration_provenance: follows-printed`. -/
theorem star_9_22
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument (bindOrder 0 argument))
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
    Derivation (.assertion (.always universal2
      (star_9_22_body existential0 existential1 negation0 disjunction0 phi psi))) := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  let core := implication negation0 disjunction0
    (phi.weakenReal.instantiate z) (psi.weakenReal.instantiate z)
  have line1 : Derivation (.assertion
      ((star_9_22_bodyY negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_matrix_all_real negation0 disjunction0 phi psi)
      (star_2_08 negation0 disjunction0 core)
  have line2 : Derivation (.assertion
      ((star_9_22_bodyX existential0 negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_bodyX_at_z existential0 negation0 disjunction0 phi psi)
      (Derivation.star_9_12 negation0 disjunction01 line1
        (Derivation.star_9_1 existential0 negation0 disjunction01
          (star_9_22_bodyY negation0 disjunction0 phi psi) z))
  have line3 := Derivation.star_9_12 negation1 disjunction12 line2
    (Derivation.star_9_1 existential1 negation1 disjunction12
      (star_9_22_bodyX existential0 negation0 disjunction0 phi psi) z)
  have line4 := Derivation.star_9_13 universal2
    (star_9_22_body existential0 existential1 negation0 disjunction0 phi psi)
    (Derivation.castAssertion
      (star_9_22_body_at_z existential0 existential1 negation0 disjunction0 phi psi)
      line3)
  have line5 : ImplicationReading negation1 disjunction12
      (.always existential0.universal
        (implication negation0 disjunction0 phi psi))
      (.always universal2
        (star_9_22_body existential0 existential1
          negation0 disjunction0 phi psi))
      (star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi) := by
    let premissMatrix := implication negation0 disjunction0 phi psi
    let negatedPremiss := star_9_01 existential0 negation0 premissMatrix
    refine {
      negated := negatedPremiss
      negationDefinition := ?_
      disjunctionDefinition := ?_
    }
    · exact ImplicationNegation.star_9_01 negation1
        existential0.universal existential0 negation0 premissMatrix
    · unfold negatedPremiss premissMatrix star_9_22_consequent
      unfold star_9_22_body
      apply ImplicationDisjunction.star_9_04
        existential1.universal universal2
      apply ImplicationDisjunction.star_9_05 existential0 existential1
      apply ImplicationDisjunction.star_9_06 existential0 existential0
      rw [star_9_22_premiss_scope_rename,
        star_9_22_consequent_scope_rename]
      unfold star_9_22_matrix
      let left := Formula.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_22_slotX) (psi.rename star_9_22_slotX))
      let right := implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ)
      let disjunction00 : signature.Disjunction (max 0 0) :=
        Eq.mp (congrArg signature.Disjunction (natMaxSelf 0).symm)
          disjunction0
      exact Eq.mp (congrArg
        (ImplicationDisjunction signature real left right)
        (sameDisjunction_unfold disjunction0 left right).symm)
        (ImplicationDisjunction.star_1_01 disjunction00 left right)
  let disjunction1 : signature.Disjunction (bindOrder 0 argument) := by
    change signature.Disjunction (max 0 (bindOrder 0 argument))
    exact disjunction01
  have line6 := ImplicationDisjunction.star_9_08
    existential1 existential1.universal universal2 disjunction1
    (star_9_22_line6Left existential0 negation0 disjunction0 phi psi)
    (star_9_22_line6Right existential0 negation0 disjunction0 phi psi)
  let disjunction11 : signature.Disjunction
      (max (bindOrder 0 argument) (bindOrder 0 argument)) :=
    Eq.mp (congrArg signature.Disjunction
      (natMaxSelf (bindOrder 0 argument)).symm) disjunction1
  have line7 : ImplicationReading negation1 disjunction11
      (.sometimes existential0 phi)
      (star_9_22_consequent existential0 existential1
        negation0 disjunction0 phi psi)
      (.sometimes existential0 psi) := by
    refine {
      negated := star_9_02 existential0.universal negation0 phi
      negationDefinition := ?_
      disjunctionDefinition := ?_
    }
    · exact ImplicationNegation.star_9_02 negation1 existential0
        existential0.universal negation0 phi
    · exact Eq.mp (congrArg
        (ImplicationDisjunction signature real
          (star_9_02 existential0.universal negation0 phi)
          (.sometimes existential0 psi))
        (star_9_22_consequent_eq_star_9_07 existential0 existential1
          negation0 disjunction0 phi psi).symm)
        (ImplicationDisjunction.star_9_07
          existential0.universal existential0 existential1.universal
          disjunction0 (.neg negation0 phi) psi)
  let printedDemonstration : Star922PrintedDemonstration existential0
      existential1 universal2 negation0 disjunction0 negation1
      disjunction1 disjunction11 disjunction12 phi psi := {
    line4 := line4
    line5 := line5
    line6 := line6
    line7 := line7
  }
  exact printedDemonstration.line4

/-- The Df reading of printed line (5).  The innermost occurrence of
✱9·06 is kept visible rather than replaced by its scoped normal form. -/
private def star_9_21_line5Formula
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real []
      (bindOrder (bindOrder (bindOrder 0 argument) argument) argument) :=
  .always universal2 (.sometimes existential1
    (star_9_06 existential0 disjunction0
      (.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX)))
      (implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ))))

/-- The constructor-level reading of printed line (6), after ✱1·01 and the
quantified-disjunction scope convention have been eliminated. -/
private def star_9_21_line6Formula
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real []
      (bindOrder (bindOrder (bindOrder 0 argument) argument) argument) :=
  .always universal2 (.sometimes existential1 (.sometimes existential0
    (.disj disjunction0
      ((Formula.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX))).rename
          (fun v => .succ v))
      (implication negation0 disjunction0
        (phi.rename star_9_22_slotY) (psi.rename star_9_22_slotZ)))))

/-- The Df reading of printed line (7), and hence of the displayed conclusion.
Its three binders are the expansions of the three independently printed
quantifiers; no two members of an implication are identified by construction. -/
def star_9_21_formula
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Formula signature real []
      (bindOrder (bindOrder (bindOrder 0 argument) argument) argument) :=
  .always universal2 (.sometimes existential1
    (star_9_06 existential0 disjunction0
      (.neg negation0 (implication negation0 disjunction0
        (phi.rename star_9_21_slotX) (psi.rename star_9_21_slotX)))
      (.disj disjunction0 (.neg negation0 (phi.rename star_9_22_slotY))
        (psi.rename star_9_22_slotZ))))

def star_9_21_reading
    (existential0 : ExistentialVocabulary signature argument 0)
    (existential1 : ExistentialVocabulary signature argument
      (bindOrder 0 argument))
    (universal2 : signature.Universal argument
      (bindOrder (bindOrder 0 argument) argument))
    (negation0 : signature.Negation 0)
    (disjunction0 : signature.Disjunction 0)
    (phi psi : Formula signature real [argument] 0) :
    Star9Reading signature real where
  printed := PM.pmPrinted "⊢:.(x).φx⊃ψx.⊃:.(x).φx.⊃.(x).ψx"
  parsed := .assertion (star_9_21_formula existential0 existential1
    universal2 negation0 disjunction0 phi psi)
  scopeReading := "The parsed AST is printed line (7): the three quantifiers are retained through the eliminable definitions ✱9·06 and ✱9·08, and bound-variable renaming is definitional in the de Bruijn syntax."

/-- ✱9·21.  Lines 1--4 are PM's printed `Id`, two existential
introductions with detachment, and real-to-apparent generalization.  Lines
5--7 are the printed definitional rewrites ✱9·06, ✱1·01, and ✱9·08.
`demonstration_provenance: follows-printed`. -/
theorem star_9_21
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
    Derivation (star_9_21_reading existential0 existential1 universal2
      negation0 disjunction0 phi psi).parsed := by
  let z : Term signature (argument :: real) [] argument := .real .zero
  let core := implication negation0 disjunction0
    (phi.weakenReal.instantiate z) (psi.weakenReal.instantiate z)
  have line1 : Derivation (.assertion
      ((star_9_22_bodyY negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_matrix_all_real negation0 disjunction0 phi psi)
      (star_2_08 negation0 disjunction0 core)
  have line2 : Derivation (.assertion
      ((star_9_22_bodyX existential0 negation0 disjunction0 phi psi).instantiate z)) :=
    Derivation.castAssertion
      (star_9_22_bodyX_at_z existential0 negation0 disjunction0 phi psi)
      (Derivation.star_9_12 negation0 disjunction01 line1
        (Derivation.star_9_1 existential0 negation0 disjunction01
          (star_9_22_bodyY negation0 disjunction0 phi psi) z))
  have line3 := Derivation.star_9_12 negation1 disjunction12 line2
    (Derivation.star_9_1 existential1 negation1 disjunction12
      (star_9_22_bodyX existential0 negation0 disjunction0 phi psi) z)
  have line4 := Derivation.star_9_13 universal2
    (star_9_22_body existential0 existential1 negation0 disjunction0 phi psi)
    (Derivation.castAssertion
      (star_9_22_body_at_z existential0 existential1 negation0 disjunction0 phi psi)
      line3)
  have line5 : Derivation (.assertion (star_9_21_line5Formula existential0
      existential1 universal2 negation0 disjunction0 phi psi)) := by
    unfold star_9_21_line5Formula
    rw [star_9_06_unfold]
    rw [star_9_21_fixed_rename]
    unfold star_9_22_body star_9_22_matrix at line4
    exact line4
  have line6 : Derivation (.assertion (star_9_21_line6Formula existential0
      existential1 universal2 negation0 disjunction0 phi psi)) := by
    unfold star_9_21_line5Formula at line5
    rw [star_9_06_unfold] at line5
    unfold star_9_21_line6Formula
    exact line5
  have line7 : Derivation (.assertion (star_9_21_formula existential0
      existential1 universal2 negation0 disjunction0 phi psi)) := by
    unfold star_9_21_formula
    rw [star_9_06_unfold]
    unfold star_9_21_line6Formula at line6
    unfold implication mixedImplication at line6 ⊢
    exact line6
  exact line7


#print axioms star_9_1
#print axioms star_9_11
#print axioms star_9_12
#print axioms star_9_13
#print axioms star_9_14
#print axioms star_9_15
#print axioms star_9_22
#print axioms star_9_22_fixedMatrix_all_real
#print axioms star_9_22_under_fixed
#print axioms star_9_32
#print axioms star_9_2
#print axioms star_9_3
#print axioms star_9_4
#print axioms star_9_361
#print axioms star_9_23
#print axioms star_9_24
#print axioms star_9_25
#print axioms star_9_41
#print axioms star_9_42
#print axioms star_9_51
#print axioms star_9_21
#print axioms star_9_33
#print axioms star_9_5
#print axioms star_9_52
#print axioms star_9_61
#print axioms star_9_62
#print axioms star_9_63

end PM.RamifiedSyntax
