import Principia.Deduction.Star3Ramified

namespace PM.RamifiedSyntax

private theorem detach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (line1 : ⊢ᵣ p)
    (line2 : ⊢ᵣ implication negation disjunction p q) :
    ⊢ᵣ q := by
  cases real with
  | nil => exact Derivation.star_1_1 negation disjunction line1 line2
  | cons head tail => exact Derivation.star_1_11 negation disjunction line1 line2

private theorem conjoin
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order)
    (phiDerived : ⊢ᵣ phi)
    (psiDerived : ⊢ᵣ psi) :
    ⊢ᵣ conjunction negation disjunction phi psi := by
  have line1 := star_3_2 negation disjunction phi psi
  have line2 := detach negation disjunction phi
    (implication negation disjunction psi
      (conjunction negation disjunction phi psi)) phiDerived line1
  have line3 := detach negation disjunction psi
    (conjunction negation disjunction phi psi) psiDerived line2
  exact line3

/-!
# Derived declarations for PM I, ✱11

These declarations expose the three primitive propositions of ✱11 through
the ramified assertion judgement.  No additional rule is introduced.
-/

/-- Catalogue reading of the primitive proposition ✱11·07. -/
def star_11_07_reading
    (leftInner : signature.Universal leftSort matrixOrder)
    (rightOuter : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (rightInner : signature.Universal rightSort matrixOrder)
    (leftOuter : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort)
        (bindOrder (bindOrder matrixOrder rightSort) leftSort)))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    ClaimReading signature real where
  printed := "“Whatever possible argument x may be, φ(x, y) is true whatever\npossible argument y may be” implies the corresponding statement with x and y\ninterchanged.  Pp."
  parsed := .assertion (star_11_07_formula leftInner rightOuter rightInner
    leftOuter negation disjunction body)

/-- ✱11·07, exactly the primitive exchange of two universal apparent variables. -/
theorem star_11_07
    (leftInner : signature.Universal leftSort matrixOrder)
    (rightOuter : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (rightInner : signature.Universal rightSort matrixOrder)
    (leftOuter : signature.Universal leftSort
      (bindOrder matrixOrder rightSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort)
        (bindOrder (bindOrder matrixOrder rightSort) leftSort)))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    ⊢ᵣ star_11_07_formula leftInner rightOuter rightInner leftOuter
      negation disjunction body := by
  have line1 := Derivation.star_11_07 leftInner rightOuter rightInner
    leftOuter negation disjunction body
  exact line1

/-- Catalogue reading of ✱11·1. -/
def star_11_1_reading
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort) matrixOrder))
    (body : Formula signature real [leftSort, rightSort] matrixOrder)
    (z : Term signature real [] leftSort)
    (w : Term signature real [] rightSort) : ClaimReading signature real where
  printed := "⊢ : (x, y).φ(x, y) .⊃ .φ(z, w)"
  parsed := .assertion
    (star_11_1_formula inner outer negation disjunction body z w)

/-- ✱11·1, exactly the primitive double universal specialization. -/
theorem star_11_1
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (max (bindOrder (bindOrder matrixOrder leftSort) rightSort) matrixOrder))
    (body : Formula signature real [leftSort, rightSort] matrixOrder)
    (z : Term signature real [] leftSort)
    (w : Term signature real [] rightSort) :
    ⊢ᵣ star_11_1_formula inner outer negation disjunction body z w := by
  have line1 := Derivation.star_11_1 inner outer negation disjunction body z w
  exact line1

/-- Catalogue reading of the primitive proposition ✱11·11. -/
def star_11_11_reading
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    ClaimReading signature real where
  printed := "If φ(z, w) is true whatever possible arguments z and w may be,\nthen (x, y).φ(x, y) is true."
  parsed := .assertion (body.always₂ inner outer)

/-- ✱11·11, exactly the primitive double generalization rule. -/
theorem star_11_11
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder)
    (hypothesis : ∀ z : Term signature real [] leftSort,
      ∀ w : Term signature real [] rightSort,
        ⊢ᵣ body.instantiate₂ z w) :
    ⊢ᵣ body.always₂ inner outer := by
  have line1 := Derivation.star_11_11 inner outer body hypothesis
  exact line1

/-- Catalogue reading of the metalinguistic rule ✱11·13. -/
def star_11_13_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "If φ(x̂, ŷ), ψ(x̂, ŷ) take their first and second arguments respectively\nof the same type, and we have “⊢.φ(x, y)” and “⊢.ψ(x, y),” we shall have\n“⊢.φ(x, y).ψ(x, y).”  [Proof as in ✱10·13]"
  parsed := .assertion (conjunction negation disjunction phi psi)

/-- ✱11·13, by the proof of ✱10·13 cited in print.
`demonstration_provenance: follows-printed`. -/
theorem star_11_13
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order)
    (phiDerived : ⊢ᵣ phi)
    (psiDerived : ⊢ᵣ psi) :
    Derivation (star_11_13_reading negation disjunction phi psi).parsed := by
  have line1 := conjoin negation disjunction phi psi phiDerived psiDerived
  exact line1

/-- Catalogue reading of the metalinguistic rule ✱11·311. -/
def star_11_311_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order) :
    ClaimReading signature real where
  printed := "If φ(x̂, ŷ), ψ(x̂, ŷ) take arguments of the same type, and we have\n“⊢.φ(x, y)” and “⊢.ψ(x, y),” we shall have “⊢.φ(x, y).ψ(x, y).”\n[Proof as in ✱10·13.]"
  parsed := .assertion (conjunction negation disjunction phi psi)

/-- ✱11·311, by the proof of ✱10·13 cited in print.
`demonstration_provenance: follows-printed`. -/
theorem star_11_311
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order)
    (phiDerived : ⊢ᵣ phi)
    (psiDerived : ⊢ᵣ psi) :
    Derivation (star_11_311_reading negation disjunction phi psi).parsed := by
  have line1 := conjoin negation disjunction phi psi phiDerived psiDerived
  exact line1

#print axioms star_11_07
#print axioms star_11_1
#print axioms star_11_11
#print axioms star_11_13
#print axioms star_11_311

end PM.RamifiedSyntax
