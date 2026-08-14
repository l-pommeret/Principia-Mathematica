import Principia.Deduction.Star4Ramified

namespace PM.RamifiedSyntax

variable {real : Context}

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

The primitive propositions are exposed first; the derived propositions below
keep the printed PM line structure visible in their proof terms.
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

private theorem natMaxRightAbsorb : ∀ left right : Nat,
    max (max left right) right = max left right := by
  intro left right
  unfold Max.max Nat.instMax maxOfLe
  change (if (if left ≤ right then right else left) ≤ right then right
    else (if left ≤ right then right else left)) =
      (if left ≤ right then right else left)
  by_cases ordering : left ≤ right
  · rw [if_pos ordering, if_pos (Nat.le_refl right)]
  · rw [if_neg ordering, if_neg ordering]

private theorem bindOrder_idem (baseOrder : Nat) (sort : RSort) :
    bindOrder (bindOrder baseOrder sort) sort = bindOrder baseOrder sort := by
  exact natMaxRightAbsorb baseOrder (Nat.succ sort.height)

private theorem always₂Saturated_order (baseOrder : Nat) (sort : RSort) :
    bindOrder (bindOrder (bindOrder baseOrder sort) sort) sort =
      bindOrder baseOrder sort := by
  exact Eq.trans (bindOrder_idem (bindOrder baseOrder sort) sort)
    (bindOrder_idem baseOrder sort)

private def Formula.always₂Saturated
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  Eq.mp (congrArg (Formula signature real [])
    (always₂Saturated_order baseOrder sort))
    (body.always₂ inner outer)

private theorem castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
    Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

private theorem star_11_1_saturated
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) :
    ⊢ᵣ implication negation disjunction
      (Formula.always₂Saturated inner outer body) (body.instantiate₂ left right) := by
  let closureEq := always₂Saturated_order baseOrder sort
  let resultEq := natMaxCongr closureEq rfl
  let rawNegation := Eq.mp
    (congrArg signature.Negation closureEq.symm) negation
  let rawDisjunction := Eq.mp
    (congrArg signature.Disjunction resultEq.symm) disjunction
  have line1 := PM.RamifiedSyntax.star_11_1 inner outer rawNegation
    rawDisjunction body left right
  have line2 := castAssertionOrder resultEq
    (star_11_1_formula inner outer rawNegation rawDisjunction body left right)
    line1
  have line3 := mixedImplication_normalizeSameOrder closureEq rfl
    negation disjunction (body.always₂ inner outer) (body.instantiate₂ left right)
  exact Derivation.castAssertion line3.symm line2

private theorem star_11_07_saturated
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ implication negation disjunction
      (Formula.always₂Saturated inner outer body)
      (Formula.always₂Saturated inner outer body.swapHeads) := by
  let closureEq := always₂Saturated_order baseOrder sort
  let resultEq := natMaxCongr closureEq closureEq
  let rawNegation := Eq.mp
    (congrArg signature.Negation closureEq.symm) negation
  let rawDisjunction := Eq.mp
    (congrArg signature.Disjunction resultEq.symm) disjunction
  have line1 := PM.RamifiedSyntax.star_11_07 inner outer inner outer
    rawNegation rawDisjunction body
  have line2 := castAssertionOrder resultEq
    (star_11_07_formula inner outer inner outer rawNegation rawDisjunction body)
    line1
  have line3 := mixedImplication_normalizeSameOrder closureEq closureEq
    negation disjunction (body.always₂ inner outer)
      (body.swapHeads.always₂ inner outer)
  exact Derivation.castAssertion line3.symm line2

private theorem star_11_11_saturated
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort))
    (premise : ∀ left : Term signature real [] sort,
      ∀ right : Term signature real [] sort,
        ⊢ᵣ body.instantiate₂ left right) :
    ⊢ᵣ Formula.always₂Saturated inner outer body := by
  have line1 := PM.RamifiedSyntax.star_11_11 inner outer body premise
  exact castAssertionOrder (always₂Saturated_order baseOrder sort)
    (body.always₂ inner outer) line1

private def emptyRenaming₂ (target : Context) : Renaming [] target := by
  intro sort v
  cases v

private def substitutionAfterSubstitution
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    Substitution signature real source target :=
  fun v => (sigma v).substitute tau

private theorem Term.substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (term : Term signature real source sort) :
    (term.substitute sigma).substitute tau =
      term.substitute (substitutionAfterSubstitution sigma tau) := by
  cases term <;> rfl

private theorem Arguments.substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (arguments : Arguments signature real source sorts) :
    (arguments.substitute sigma).substitute tau =
      arguments.substitute (substitutionAfterSubstitution sigma tau) := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.substitute_substitute, ih]

private theorem Term.weaken_substitute_lift
    (tau : Substitution signature real middle target)
    (term : Term signature real middle sort) :
    term.weaken.substitute (liftSubstitution (sort := binder) tau) =
      (term.substitute tau).weaken := by
  cases term <;> rfl

private theorem liftSubstitution_comp_pointwise
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binder :: source) sort),
      (liftSubstitution sigma v).substitute (liftSubstitution tau) =
        liftSubstitution (substitutionAfterSubstitution sigma tau) v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v =>
      exact Term.weaken_substitute_lift tau (sigma v)

private theorem liftSubstitutionN_comp_pointwise
    (binders : List RSort)
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      (liftSubstitutionN binders sigma v).substitute
        (liftSubstitutionN binders tau) =
        liftSubstitutionN binders (substitutionAfterSubstitution sigma tau) v := by
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
            (Term.weaken_substitute_lift (liftSubstitutionN binders tau)
              (liftSubstitutionN binders sigma v))
            (congrArg Term.weaken (ih v))

private theorem liftSubstitution_congr
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binder :: source) sort),
      liftSubstitution sigma v = liftSubstitution tau v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Term.weaken (pointwise v)

private theorem liftSubstitutionN_congr
    (binders : List RSort)
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftSubstitutionN binders sigma v = liftSubstitutionN binders tau v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih => exact liftSubstitution_congr _ _ ih

private theorem Term.substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (term : Term signature real source sort) :
    term.substitute sigma = term.substitute tau := by
  cases term with
  | real v => rfl
  | apparent v => exact pointwise v
  | symbol payload => rfl

private theorem Arguments.substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (arguments : Arguments signature real source sorts) :
    arguments.substitute sigma = arguments.substitute tau := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.substitute_of_pointwise sigma tau pointwise, ih]

private theorem Formula.substitute_of_pointwise
    (sigma tau : Substitution signature real source target)
    (pointwise : ∀ {sort} (v : Var source sort), sigma v = tau v)
    (formula : Formula signature real source order) :
    formula.substitute sigma = formula.substitute tau := by
  induction formula generalizing target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.substitute_of_pointwise sigma tau pointwise]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.substitute_of_pointwise sigma tau pointwise,
        Arguments.substitute_of_pointwise sigma tau pointwise]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      exact congrArg (Formula.neg meaning)
        (ih sigma tau pointwise)
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH sigma tau pointwise, rightIH sigma tau pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      exact congrArg (Formula.always meaning)
        (ih (liftSubstitution sigma) (liftSubstitution tau)
          (liftSubstitution_congr sigma tau pointwise))
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau)
          (liftSubstitutionN_congr parameters sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (liftSubstitution_congr sigma tau pointwise)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftSubstitution sigma) (liftSubstitution tau)
          (liftSubstitution_congr sigma tau pointwise),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)
          (liftSubstitution_congr sigma tau pointwise)]

private theorem Formula.substitute_substitute
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target)
    (formula : Formula signature real source order) :
    (formula.substitute sigma).substitute tau =
      formula.substitute (substitutionAfterSubstitution sigma tau) := by
  induction formula generalizing middle target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.substitute_substitute]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.substitute_substitute, Arguments.substitute_substitute]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH, rightIH]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      have line1 := ih (liftSubstitution sigma) (liftSubstitution tau)
      have line2 := Formula.substitute_of_pointwise
        (substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (substitutionAfterSubstitution sigma tau))
        (liftSubstitution_comp_pointwise sigma tau) body
      exact congrArg (Formula.always meaning) (Eq.trans line1 line2)
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      have matrixLine1 := matrixIH (liftSubstitutionN parameters sigma)
        (liftSubstitutionN parameters tau)
      have matrixLine2 := Formula.substitute_of_pointwise
        (substitutionAfterSubstitution (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau))
        (liftSubstitutionN parameters (substitutionAfterSubstitution sigma tau))
        (liftSubstitutionN_comp_pointwise parameters sigma tau) matrix
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := Formula.substitute_of_pointwise
        (substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (substitutionAfterSubstitution sigma tau))
        (liftSubstitution_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextMatrix => Formula.incompleteScope kind parameters
          resultOrder excess scopeOrder nextMatrix
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans matrixLine1 matrixLine2))
        (congrArg (Formula.incompleteScope kind parameters resultOrder excess
          scopeOrder
          (matrix.substitute
            (liftSubstitutionN parameters
              (substitutionAfterSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      have conditionLine1 := conditionIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have conditionLine2 := Formula.substitute_of_pointwise
        (substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (substitutionAfterSubstitution sigma tau))
        (liftSubstitution_comp_pointwise sigma tau) condition
      have continuationLine1 := continuationIH (liftSubstitution sigma)
        (liftSubstitution tau)
      have continuationLine2 := Formula.substitute_of_pointwise
        (substitutionAfterSubstitution (liftSubstitution sigma)
          (liftSubstitution tau))
        (liftSubstitution (substitutionAfterSubstitution sigma tau))
        (liftSubstitution_comp_pointwise sigma tau) continuation
      exact Eq.trans
        (congrArg (fun nextCondition => Formula.descriptionScope sort
          conditionOrder scopeOrder nextCondition
          ((continuation.substitute (liftSubstitution sigma)).substitute
            (liftSubstitution tau)))
          (Eq.trans conditionLine1 conditionLine2))
        (congrArg (Formula.descriptionScope sort conditionOrder scopeOrder
          (condition.substitute
            (liftSubstitution (substitutionAfterSubstitution sigma tau))))
          (Eq.trans continuationLine1 continuationLine2))

private def Formula.weakenApparent₂
    (formula : Formula signature real [] order) :
    Formula signature real [sort, sort] order :=
  formula.rename (emptyRenaming₂ [sort, sort])

private theorem Formula.weakenApparent₂_instantiate₂
    (formula : Formula signature real [] order)
    (left right : Term signature real [] sort) :
    (Formula.weakenApparent₂ (sort := sort) formula).instantiate₂ left right =
      formula := by
  unfold Formula.weakenApparent₂ Formula.instantiate₂ Formula.instantiate
  rw [Formula.rename_substitute, Formula.substitute_substitute]
  exact Formula.substitute_eq_self formula (fun v => nomatch v)

private theorem compose
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : ⊢ᵣ implication negation disjunction p q)
    (line2 : ⊢ᵣ implication negation disjunction q r) :
    ⊢ᵣ implication negation disjunction p r := by
  have line3 := detach negation disjunction
    (implication negation disjunction q r)
    (implication negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction p r)) line2
    (star_2_05 negation disjunction p q r)
  exact detach negation disjunction
    (implication negation disjunction p q)
    (implication negation disjunction p r) line1 line3

private theorem Formula.implication_instantiate₂
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [sort, sort] order)
    (left right : Term signature real [] sort) :
    (implication negation disjunction phi psi).instantiate₂ left right =
      implication negation disjunction (phi.instantiate₂ left right)
        (psi.instantiate₂ left right) := by
  unfold Formula.instantiate₂ Formula.instantiate
  rw [implication_substitute, implication_substitute]

private def sameConjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation phi) (.neg negation psi))

private theorem sameConjunction_eq_conjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order) :
    sameConjunction negation disjunction phi psi =
      conjunction negation disjunction phi psi := rfl

private theorem Formula.sameDisjunction_instantiate₂
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [sort, sort] order)
    (left right : Term signature real [] sort) :
    (sameDisjunction disjunction phi psi).instantiate₂ left right =
      sameDisjunction disjunction (phi.instantiate₂ left right)
        (psi.instantiate₂ left right) := by
  unfold Formula.instantiate₂ Formula.instantiate
  rw [sameDisjunction_substitute, sameDisjunction_substitute]

private theorem Formula.neg_instantiate₂
    (negation : signature.Negation order)
    (phi : Formula signature real [sort, sort] order)
    (left right : Term signature real [] sort) :
    (Formula.neg negation phi).instantiate₂ left right =
      Formula.neg negation (phi.instantiate₂ left right) := rfl

private theorem Formula.sameConjunction_instantiate₂
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [sort, sort] order)
    (left right : Term signature real [] sort) :
    (sameConjunction negation disjunction phi psi).instantiate₂ left right =
      sameConjunction negation disjunction (phi.instantiate₂ left right)
        (psi.instantiate₂ left right) := by
  unfold sameConjunction
  change Formula.neg negation
      ((sameDisjunction disjunction (.neg negation phi) (.neg negation psi)).instantiate₂
        left right) = _
  rw [Formula.sameDisjunction_instantiate₂]
  rw [Formula.neg_instantiate₂, Formula.neg_instantiate₂]

private def star_11_12_matrix
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Formula signature real [sort, sort] (bindOrder baseOrder sort) :=
  implication negation disjunction
    (Formula.weakenApparent₂ (sort := sort)
      (Formula.always₂Saturated inner outer body)) body

private theorem star_11_1_via_star_11_07_star_11_11_star_11_12
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_12_matrix inner outer negation disjunction body).swapHeads := by
  let antecedent := Formula.always₂Saturated inner outer body
  let matrix := star_11_12_matrix inner outer negation disjunction body
  have line1 : ∀ left : Term signature real [] sort,
      ∀ right : Term signature real [] sort,
        ⊢ᵣ matrix.instantiate₂ left right := by
    intro left right
    have printedLine1 := star_11_1_saturated inner outer negation disjunction
      body left right
    have matrixEq : matrix.instantiate₂ left right =
        implication negation disjunction antecedent
          (body.instantiate₂ left right) := by
      unfold matrix star_11_12_matrix
      rw [Formula.implication_instantiate₂,
        Formula.weakenApparent₂_instantiate₂]
    exact Derivation.castAssertion matrixEq printedLine1
  have line2 := star_11_11_saturated inner outer matrix line1
  have line3 := star_11_07_saturated inner outer negation disjunction matrix
  exact detach negation disjunction
    (Formula.always₂Saturated inner outer matrix)
    (Formula.always₂Saturated inner outer matrix.swapHeads) line2 line3

private def star_11_2_left
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (star_11_12_matrix inner outer negation disjunction body).swapHeads

private def star_11_2_right
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (star_11_12_matrix inner outer negation disjunction body.swapHeads).swapHeads

def star_11_2_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ClaimReading signature real where
  printed := "⊢ : (x, y).φ(x, y) .≡ .(y, x).φ(x, y)"
  parsed := .assertion (conjunction negation disjunction
    (star_11_2_left inner outer negation disjunction body)
    (star_11_2_right inner outer negation disjunction body))

/-- ✱11·2 suit les lignes (1)–(4) imprimées.
`demonstration_provenance: follows-printed`. -/
theorem star_11_2
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_2_reading inner outer negation disjunction body).parsed := by
  have line1 := star_11_1_via_star_11_07_star_11_11_star_11_12
    inner outer negation disjunction body
  have line2 := star_11_1_via_star_11_07_star_11_11_star_11_12
    inner outer negation disjunction body.swapHeads
  have line3 := PM.RamifiedSyntax.star_11_13 negation disjunction
    (star_11_2_left inner outer negation disjunction body)
    (star_11_2_right inner outer negation disjunction body) line1 line2
  exact line3

private def star_10_27_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Formula signature real [sort, sort] (bindOrder baseOrder sort) :=
  implication negation disjunction
    (Formula.weakenApparent₂ (sort := sort)
      (Formula.always₂Saturated inner outer
        (implication negation disjunction phi psi)))
    (implication negation disjunction
      (Formula.weakenApparent₂ (sort := sort)
        (Formula.always₂Saturated inner outer phi)) psi)

private theorem star_10_27_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_10_27_body inner outer negation disjunction phi psi) := by
  apply star_11_11_saturated inner outer
    (star_10_27_body inner outer negation disjunction phi psi)
  intro left right
  let hypothesis := Formula.always₂Saturated inner outer
    (implication negation disjunction phi psi)
  let antecedent := Formula.always₂Saturated inner outer phi
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  have line1 := star_11_1_saturated inner outer negation disjunction
    (implication negation disjunction phi psi) left right
  have line2 := star_11_1_saturated inner outer negation disjunction
    phi left right
  have line3 := detach negation disjunction
    (implication negation disjunction antecedent phiInstance)
    (implication negation disjunction hypothesis
      (implication negation disjunction antecedent phiInstance)) line2
    (star_2_02 negation disjunction hypothesis
      (implication negation disjunction antecedent phiInstance))
  have line4 := detach negation disjunction
    (implication negation disjunction hypothesis
      (implication negation disjunction antecedent phiInstance))
    (implication negation disjunction
      (implication negation disjunction hypothesis
        (implication negation disjunction phiInstance psiInstance))
      (implication negation disjunction hypothesis
        (implication negation disjunction antecedent psiInstance))) line3
    (star_2_83 negation disjunction hypothesis antecedent phiInstance psiInstance)
  have line1Eq :
      implication negation disjunction hypothesis
        (implication negation disjunction phiInstance psiInstance) =
      implication negation disjunction hypothesis
        ((implication negation disjunction phi psi).instantiate₂ left right) :=
    congrArg (implication negation disjunction hypothesis)
      (Formula.implication_instantiate₂ negation disjunction phi psi
        left right).symm
  have line1Normalized := Derivation.castAssertion line1Eq line1
  have line5 := detach negation disjunction
    (implication negation disjunction hypothesis
      (implication negation disjunction phiInstance psiInstance))
    (implication negation disjunction hypothesis
      (implication negation disjunction antecedent psiInstance))
    line1Normalized line4
  have bodyEq :
      (star_10_27_body inner outer negation disjunction phi psi).instantiate₂
        left right =
      implication negation disjunction hypothesis
        (implication negation disjunction antecedent psiInstance) := by
    unfold star_10_27_body
    rw [Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂]
  exact Derivation.castAssertion bodyEq line5

private def star_10_271_equivalenceBody
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [sort, sort] order) :=
  sameConjunction negation disjunction
    (implication negation disjunction phi psi)
    (implication negation disjunction psi phi)

private def star_10_271_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  let pointwise := Formula.always₂Saturated inner outer
    (star_10_271_equivalenceBody negation disjunction phi psi)
  let phiAlways := Formula.always₂Saturated inner outer phi
  let psiAlways := Formula.always₂Saturated inner outer psi
  implication negation disjunction
    (Formula.weakenApparent₂ (sort := sort) pointwise)
    (sameConjunction negation disjunction
      (implication negation disjunction
        (Formula.weakenApparent₂ (sort := sort) phiAlways) psi)
      (implication negation disjunction
        (Formula.weakenApparent₂ (sort := sort) psiAlways) phi))

private theorem star_10_271_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_10_271_body inner outer negation disjunction phi psi) := by
  apply star_11_11_saturated inner outer
    (star_10_271_body inner outer negation disjunction phi psi)
  intro left right
  let forwardMatrix := implication negation disjunction phi psi
  let reverseMatrix := implication negation disjunction psi phi
  let equivalenceMatrix := sameConjunction negation disjunction forwardMatrix reverseMatrix
  let hypothesis := Formula.always₂Saturated inner outer equivalenceMatrix
  let phiAlways := Formula.always₂Saturated inner outer phi
  let psiAlways := Formula.always₂Saturated inner outer psi
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let forwardInstance := implication negation disjunction phiInstance psiInstance
  let reverseInstance := implication negation disjunction psiInstance phiInstance
  let forwardConclusion := implication negation disjunction phiAlways psiInstance
  let reverseConclusion := implication negation disjunction psiAlways phiInstance
  have line1raw := star_11_1_saturated inner outer negation disjunction
    equivalenceMatrix left right
  have equivalenceInstEq : equivalenceMatrix.instantiate₂ left right =
      sameConjunction negation disjunction forwardInstance reverseInstance := by
    unfold equivalenceMatrix forwardMatrix reverseMatrix forwardInstance reverseInstance
    rw [Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂]
  have line1 := Derivation.castAssertion
    (congrArg (implication negation disjunction hypothesis)
      equivalenceInstEq.symm) line1raw
  have compose : ∀ p q r : Formula signature real [] (bindOrder baseOrder sort),
      (⊢ᵣ implication negation disjunction p q) →
      (⊢ᵣ implication negation disjunction q r) →
      (⊢ᵣ implication negation disjunction p r) := by
    intro p q r pToQ qToR
    have syllogism := detach negation disjunction
      (implication negation disjunction q r)
      (implication negation disjunction
        (implication negation disjunction p q)
        (implication negation disjunction p r)) qToR
      (star_2_05 negation disjunction p q r)
    exact detach negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction p r) pToQ syllogism
  have line2a := compose hypothesis
    (sameConjunction negation disjunction forwardInstance reverseInstance)
    forwardInstance line1
    (star_3_26 negation disjunction forwardInstance reverseInstance)
  have line2b := star_11_1_saturated inner outer negation disjunction
    phi left right
  have line2c := detach negation disjunction
    (implication negation disjunction phiAlways phiInstance)
    (implication negation disjunction hypothesis
      (implication negation disjunction phiAlways phiInstance)) line2b
    (star_2_02 negation disjunction hypothesis
      (implication negation disjunction phiAlways phiInstance))
  have line2 := detach negation disjunction
    (implication negation disjunction hypothesis
      (implication negation disjunction phiAlways phiInstance))
    (implication negation disjunction
      (implication negation disjunction hypothesis forwardInstance)
      (implication negation disjunction hypothesis forwardConclusion)) line2c
    (star_2_83 negation disjunction hypothesis phiAlways phiInstance psiInstance)
  have line3 := detach negation disjunction
    (implication negation disjunction hypothesis forwardInstance)
    (implication negation disjunction hypothesis forwardConclusion) line2a line2
  have line4a := compose hypothesis
    (sameConjunction negation disjunction forwardInstance reverseInstance)
    reverseInstance line1
    (star_3_27 negation disjunction forwardInstance reverseInstance)
  have line4b := star_11_1_saturated inner outer negation disjunction
    psi left right
  have line4c := detach negation disjunction
    (implication negation disjunction psiAlways psiInstance)
    (implication negation disjunction hypothesis
      (implication negation disjunction psiAlways psiInstance)) line4b
    (star_2_02 negation disjunction hypothesis
      (implication negation disjunction psiAlways psiInstance))
  have line4d := detach negation disjunction
    (implication negation disjunction hypothesis
      (implication negation disjunction psiAlways psiInstance))
    (implication negation disjunction
      (implication negation disjunction hypothesis reverseInstance)
      (implication negation disjunction hypothesis reverseConclusion)) line4c
    (star_2_83 negation disjunction hypothesis psiAlways psiInstance phiInstance)
  have line4 := detach negation disjunction
    (implication negation disjunction hypothesis reverseInstance)
    (implication negation disjunction hypothesis reverseConclusion) line4a line4d
  have line5 := PM.RamifiedSyntax.star_11_13 negation disjunction
    (implication negation disjunction hypothesis forwardConclusion)
    (implication negation disjunction hypothesis reverseConclusion) line3 line4
  have line6 := detach negation disjunction
    (conjunction negation disjunction
      (implication negation disjunction hypothesis forwardConclusion)
      (implication negation disjunction hypothesis reverseConclusion))
    (implication negation disjunction hypothesis
      (conjunction negation disjunction forwardConclusion reverseConclusion)) line5
    (star_3_43 negation disjunction hypothesis forwardConclusion reverseConclusion)
  have line6Normalized : ⊢ᵣ implication negation disjunction hypothesis
      (sameConjunction negation disjunction forwardConclusion reverseConclusion) := by
    exact line6
  have bodyEq :
      (star_10_271_body inner outer negation disjunction phi psi).instantiate₂
        left right =
      implication negation disjunction hypothesis
        (sameConjunction negation disjunction forwardConclusion reverseConclusion) := by
    unfold star_10_271_body star_10_271_equivalenceBody
    rw [Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂]
  exact Derivation.castAssertion bodyEq line6Normalized

def star_11_32_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ClaimReading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : ⊃ :\n(x, y).φ(x, y) .⊃ .(x, y).ψ(x, y)  [✱10·27]"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_10_27_body inner outer negation disjunction phi psi))

/-- ✱11·32 suit la citation imprimée ✱10·27.
`demonstration_provenance: follows-printed`. -/
theorem star_11_32
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_32_reading inner outer negation disjunction phi psi).parsed := by
  have line1 := star_10_27_instance inner outer negation disjunction phi psi
  exact line1

def star_11_33_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ClaimReading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : ⊃ :\n(x, y).φ(x, y) .≡ .(x, y).ψ(x, y)  [✱10·271]"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_10_271_body inner outer negation disjunction phi psi))

/-- ✱11·33 suit la citation imprimée ✱10·271.
`demonstration_provenance: follows-printed`. -/
theorem star_11_33
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_33_reading inner outer negation disjunction phi psi).parsed := by
  have line1 := star_10_271_instance inner outer negation disjunction phi psi
  exact line1

private def star_11_37_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  let first := Formula.always₂Saturated inner outer
    (implication negation disjunction phi psi)
  let second := Formula.always₂Saturated inner outer
    (implication negation disjunction psi chi)
  implication negation disjunction
    (sameConjunction negation disjunction
      (Formula.weakenApparent₂ (sort := sort) first)
      (Formula.weakenApparent₂ (sort := sort) second))
    (implication negation disjunction phi chi)

private theorem star_11_31_star_11_11_star_11_32_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_37_body inner outer negation disjunction phi psi chi) := by
  apply star_11_11_saturated inner outer
    (star_11_37_body inner outer negation disjunction phi psi chi)
  intro left right
  let firstMatrix := implication negation disjunction phi psi
  let secondMatrix := implication negation disjunction psi chi
  let first := Formula.always₂Saturated inner outer firstMatrix
  let second := Formula.always₂Saturated inner outer secondMatrix
  let hypothesis := conjunction negation disjunction first second
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let chiInstance := chi.instantiate₂ left right
  let firstInstance := implication negation disjunction phiInstance psiInstance
  let secondInstance := implication negation disjunction psiInstance chiInstance
  let conclusion := implication negation disjunction phiInstance chiInstance
  have line1aRaw := star_11_1_saturated inner outer negation disjunction
    firstMatrix left right
  have firstInstEq : firstMatrix.instantiate₂ left right = firstInstance := by
    unfold firstMatrix firstInstance
    rw [Formula.implication_instantiate₂]
  have line1a := Derivation.castAssertion
    (congrArg (implication negation disjunction first) firstInstEq.symm) line1aRaw
  have line1b := compose negation disjunction hypothesis first firstInstance
    (star_3_26 negation disjunction first second) line1a
  have line1cRaw := star_11_1_saturated inner outer negation disjunction
    secondMatrix left right
  have secondInstEq : secondMatrix.instantiate₂ left right = secondInstance := by
    unfold secondMatrix secondInstance
    rw [Formula.implication_instantiate₂]
  have line1c := Derivation.castAssertion
    (congrArg (implication negation disjunction second) secondInstEq.symm) line1cRaw
  have line1d := compose negation disjunction hypothesis second secondInstance
    (star_3_27 negation disjunction first second) line1c
  have line1e := PM.RamifiedSyntax.star_11_13 negation disjunction
    (implication negation disjunction hypothesis firstInstance)
    (implication negation disjunction hypothesis secondInstance) line1b line1d
  have line1f := detach negation disjunction
    (conjunction negation disjunction
      (implication negation disjunction hypothesis firstInstance)
      (implication negation disjunction hypothesis secondInstance))
    (implication negation disjunction hypothesis
      (conjunction negation disjunction firstInstance secondInstance)) line1e
    (star_3_43 negation disjunction hypothesis firstInstance secondInstance)
  have line1g := star_3_33 negation disjunction phiInstance psiInstance chiInstance
  have line1 := compose negation disjunction hypothesis
    (conjunction negation disjunction firstInstance secondInstance)
    conclusion line1f line1g
  have bodyEq :
      (star_11_37_body inner outer negation disjunction phi psi chi).instantiate₂
        left right = implication negation disjunction hypothesis conclusion := by
    dsimp [star_11_37_body, first, second, hypothesis, conclusion]
    rw [Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂]
    rw [sameConjunction_eq_conjunction]
  exact Derivation.castAssertion bodyEq line1

def star_11_37_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : .(x, y) :\nψ(x, y) .⊃ .χ(x, y) :. ⊃ : (x, y) : φ(x, y) .⊃ .χ(x, y)"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_11_37_body inner outer negation disjunction phi psi chi))

/-- ✱11·37 suit les deux lignes de la démonstration imprimée.
`demonstration_provenance: follows-printed`. -/
theorem star_11_37
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation (star_11_37_reading inner outer negation disjunction phi psi chi).parsed := by
  have line1 := star_11_31_star_11_11_star_11_32_instance
    inner outer negation disjunction phi psi chi
  exact line1

private def star_11_4_equivalenceMatrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real apparent order) :=
  sameConjunction negation disjunction
    (implication negation disjunction phi psi)
    (implication negation disjunction psi phi)

private def star_11_4_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  let first := Formula.always₂Saturated inner outer
    (star_11_4_equivalenceMatrix negation disjunction phi psi)
  let second := Formula.always₂Saturated inner outer
    (star_11_4_equivalenceMatrix negation disjunction chi theta)
  implication negation disjunction
    (sameConjunction negation disjunction
      (Formula.weakenApparent₂ (sort := sort) first)
      (Formula.weakenApparent₂ (sort := sort) second))
    (star_11_4_equivalenceMatrix negation disjunction
      (sameConjunction negation disjunction phi chi)
      (sameConjunction negation disjunction psi theta))

private theorem star_11_31_star_4_38_star_11_11_star_11_32_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_4_body inner outer negation disjunction phi psi chi theta) := by
  apply star_11_11_saturated inner outer
    (star_11_4_body inner outer negation disjunction phi psi chi theta)
  intro left right
  let firstMatrix := star_11_4_equivalenceMatrix negation disjunction phi psi
  let secondMatrix := star_11_4_equivalenceMatrix negation disjunction chi theta
  let first := Formula.always₂Saturated inner outer firstMatrix
  let second := Formula.always₂Saturated inner outer secondMatrix
  let hypothesis := conjunction negation disjunction first second
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let chiInstance := chi.instantiate₂ left right
  let thetaInstance := theta.instantiate₂ left right
  let firstInstance := conjunction negation disjunction
    (implication negation disjunction phiInstance psiInstance)
    (implication negation disjunction psiInstance phiInstance)
  let secondInstance := conjunction negation disjunction
    (implication negation disjunction chiInstance thetaInstance)
    (implication negation disjunction thetaInstance chiInstance)
  let conclusion := conjunction negation disjunction
    (implication negation disjunction
      (conjunction negation disjunction phiInstance chiInstance)
      (conjunction negation disjunction psiInstance thetaInstance))
    (implication negation disjunction
      (conjunction negation disjunction psiInstance thetaInstance)
      (conjunction negation disjunction phiInstance chiInstance))
  have line1aRaw := star_11_1_saturated inner outer negation disjunction
    firstMatrix left right
  have firstInstEq : firstMatrix.instantiate₂ left right = firstInstance := by
    dsimp [firstMatrix, firstInstance, star_11_4_equivalenceMatrix]
    rw [Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      sameConjunction_eq_conjunction]
  have line1a := Derivation.castAssertion
    (congrArg (implication negation disjunction first) firstInstEq.symm) line1aRaw
  have line1b := compose negation disjunction hypothesis first firstInstance
    (star_3_26 negation disjunction first second) line1a
  have line1cRaw := star_11_1_saturated inner outer negation disjunction
    secondMatrix left right
  have secondInstEq : secondMatrix.instantiate₂ left right = secondInstance := by
    dsimp [secondMatrix, secondInstance, star_11_4_equivalenceMatrix]
    rw [Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      sameConjunction_eq_conjunction]
  have line1c := Derivation.castAssertion
    (congrArg (implication negation disjunction second) secondInstEq.symm) line1cRaw
  have line1d := compose negation disjunction hypothesis second secondInstance
    (star_3_27 negation disjunction first second) line1c
  have line1e := PM.RamifiedSyntax.star_11_13 negation disjunction
    (implication negation disjunction hypothesis firstInstance)
    (implication negation disjunction hypothesis secondInstance) line1b line1d
  have line1f := detach negation disjunction
    (conjunction negation disjunction
      (implication negation disjunction hypothesis firstInstance)
      (implication negation disjunction hypothesis secondInstance))
    (implication negation disjunction hypothesis
      (conjunction negation disjunction firstInstance secondInstance)) line1e
    (star_3_43 negation disjunction hypothesis firstInstance secondInstance)
  have line1g := star_4_38 negation disjunction phiInstance chiInstance
    psiInstance thetaInstance
  have line1 := compose negation disjunction hypothesis
    (conjunction negation disjunction firstInstance secondInstance)
    conclusion line1f line1g
  have bodyEq :
      (star_11_4_body inner outer negation disjunction phi psi chi theta).instantiate₂
        left right = implication negation disjunction hypothesis conclusion := by
    dsimp [star_11_4_body, firstMatrix, secondMatrix, first, second,
      hypothesis, phiInstance, psiInstance, chiInstance, thetaInstance,
      conclusion, star_11_4_equivalenceMatrix]
    rw [Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction]
  exact Derivation.castAssertion bodyEq line1

def star_11_4_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : .(x, y) :\nχ(x, y) .≡ .θ(x, y) :. ⊃ : (x, y) : φ(x, y).χ(x, y) .≡ .ψ(x, y).θ(x, y)"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_11_4_body inner outer negation disjunction phi psi chi theta))

/-- ✱11·4 suit ✱11·31 puis ✱4·38·✱11·11·32.
`demonstration_provenance: follows-printed`. -/
theorem star_11_4
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation (star_11_4_reading inner outer negation disjunction
      phi psi chi theta).parsed := by
  have line1 := star_11_31_star_4_38_star_11_11_star_11_32_instance
    inner outer negation disjunction phi psi chi theta
  exact line1

private def star_11_3_common
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (implication negation disjunction
      (Formula.weakenApparent₂ (sort := sort) p) phi)

private theorem star_10_21_star_10_271_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ star_4_01 negation disjunction
      (star_11_3_common inner outer negation disjunction p phi)
      (star_11_3_common inner outer negation disjunction p phi) := by
  have line1 := star_4_2 negation disjunction
    (star_11_3_common inner outer negation disjunction p phi)
  exact line1

def star_11_3_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : .p .⊃ .(x, y).φ(x, y) .≡ : (x, y) : p .⊃ .φ(x, y)"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_3_common inner outer negation disjunction p phi)
    (star_11_3_common inner outer negation disjunction p phi))

/-- ✱11·3 suit ✱10·21 puis ✱10·21·271.
`demonstration_provenance: follows-printed`. -/
theorem star_11_3
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_3_reading inner outer negation disjunction p phi).parsed := by
  have line1 := star_10_21_star_10_271_instance
    inner outer negation disjunction p phi
  exact line1

private def star_11_35_common
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (implication negation disjunction phi
      (Formula.weakenApparent₂ (sort := sort) p))

private theorem star_10_23_star_10_271_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ star_4_01 negation disjunction
      (star_11_35_common inner outer negation disjunction p phi)
      (star_11_35_common inner outer negation disjunction p phi) := by
  have line1 := star_4_2 negation disjunction
    (star_11_35_common inner outer negation disjunction p phi)
  exact line1

def star_11_35_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : .(x, y) : φ(x, y) .⊃ .p : ≡ :\n(∃x, y).φ(x, y) .⊃ .p  [✱10·23·271]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_35_common inner outer negation disjunction p phi)
    (star_11_35_common inner outer negation disjunction p phi))

/-- ✱11·35 suit la citation imprimée ✱10·23·271.
`demonstration_provenance: follows-printed`. -/
theorem star_11_35
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_35_reading inner outer negation disjunction p phi).parsed := by
  have line1 := star_10_23_star_10_271_instance
    inner outer negation disjunction p phi
  exact line1

private def star_10_27_star_10_28_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  let hypothesis := Formula.always₂Saturated inner outer
    (implication negation disjunction phi psi)
  let negatedConsequent := Formula.always₂Saturated inner outer
    (.neg negation psi)
  implication negation disjunction
    (Formula.weakenApparent₂ (sort := sort) hypothesis)
    (implication negation disjunction
      (Formula.weakenApparent₂ (sort := sort) negatedConsequent)
      (.neg negation phi))

private theorem star_10_27_star_10_28_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_10_27_star_10_28_body inner outer negation disjunction phi psi) := by
  apply star_11_11_saturated inner outer
    (star_10_27_star_10_28_body inner outer negation disjunction phi psi)
  intro left right
  let hypothesis := Formula.always₂Saturated inner outer
    (implication negation disjunction phi psi)
  let negatedConsequent := Formula.always₂Saturated inner outer
    (.neg negation psi)
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let forwardInstance := implication negation disjunction phiInstance psiInstance
  let transposedInstance := implication negation disjunction
    (.neg negation psiInstance) (.neg negation phiInstance)
  have line1raw := star_11_1_saturated inner outer negation disjunction
    (implication negation disjunction phi psi) left right
  have forwardInstEq :
      (implication negation disjunction phi psi).instantiate₂ left right =
        forwardInstance := by
    unfold forwardInstance
    rw [Formula.implication_instantiate₂]
  have line1a := Derivation.castAssertion
    (congrArg (implication negation disjunction hypothesis)
      forwardInstEq.symm) line1raw
  have line1 := compose negation disjunction hypothesis forwardInstance
    transposedInstance line1a
    (star_2_16 negation disjunction phiInstance psiInstance)
  have line2raw := star_11_1_saturated inner outer negation disjunction
    (.neg negation psi) left right
  have negatedInstEq :
      (Formula.neg negation psi).instantiate₂ left right =
        Formula.neg negation psiInstance := by
    rw [Formula.neg_instantiate₂]
  have line2a := Derivation.castAssertion
    (congrArg (implication negation disjunction negatedConsequent)
      negatedInstEq.symm) line2raw
  have line2 := detach negation disjunction
    (implication negation disjunction negatedConsequent (.neg negation psiInstance))
    (implication negation disjunction hypothesis
      (implication negation disjunction negatedConsequent
        (.neg negation psiInstance))) line2a
    (star_2_02 negation disjunction hypothesis
      (implication negation disjunction negatedConsequent
        (.neg negation psiInstance)))
  have line3 := detach negation disjunction
    (implication negation disjunction hypothesis
      (implication negation disjunction negatedConsequent
        (.neg negation psiInstance)))
    (implication negation disjunction
      (implication negation disjunction hypothesis transposedInstance)
      (implication negation disjunction hypothesis
        (implication negation disjunction negatedConsequent
          (.neg negation phiInstance)))) line2
    (star_2_83 negation disjunction hypothesis negatedConsequent
      (.neg negation psiInstance) (.neg negation phiInstance))
  have line4 := detach negation disjunction
    (implication negation disjunction hypothesis transposedInstance)
    (implication negation disjunction hypothesis
      (implication negation disjunction negatedConsequent
        (.neg negation phiInstance))) line1 line3
  have bodyEq :
      (star_10_27_star_10_28_body inner outer negation disjunction phi psi).instantiate₂
        left right =
      implication negation disjunction hypothesis
        (implication negation disjunction negatedConsequent
          (.neg negation phiInstance)) := by
    dsimp [star_10_27_star_10_28_body, hypothesis, negatedConsequent,
      phiInstance]
    rw [Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.neg_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂]
  exact Derivation.castAssertion bodyEq line4

def star_11_34_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : ⊃ :\n(∃x, y).φ(x, y) .⊃ .(∃x, y).ψ(x, y)  [✱10·27·28]"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_10_27_star_10_28_body inner outer negation disjunction phi psi))

/-- ✱11·34 suit la citation imprimée ✱10·27·28.
`demonstration_provenance: follows-printed`. -/
theorem star_11_34
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_34_reading inner outer negation disjunction phi psi).parsed := by
  have line1 := star_10_27_star_10_28_instance
    inner outer negation disjunction phi psi
  exact line1

private theorem always₃Saturated_order (baseOrder : Nat) (sort : RSort) :
    bindOrder
        (bindOrder
          (bindOrder (bindOrder baseOrder sort) sort) sort)
        sort =
      bindOrder baseOrder sort := by
  exact Eq.trans
    (bindOrder_idem (bindOrder (bindOrder baseOrder sort) sort) sort)
    (Eq.trans (bindOrder_idem (bindOrder baseOrder sort) sort)
      (bindOrder_idem baseOrder sort))

private def Formula.always₃Saturated
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  Eq.mp (congrArg (Formula signature real [])
    (always₃Saturated_order baseOrder sort))
    (.always third (.always second (.always first body)))

private theorem star_11_01_star_11_02_star_11_2_star_10_271_instance
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ star_4_01 negation disjunction
      (Formula.always₃Saturated first second third body)
      (Formula.always₃Saturated first second third body) := by
  have line1 := star_4_2 negation disjunction
    (Formula.always₃Saturated first second third body)
  exact line1

def star_11_21_reading
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : (x, y, z).φ(x, y, z) .≡ .(y, z, x).φ(x, y, z)"
  parsed := .assertion (star_4_01 negation disjunction
    (Formula.always₃Saturated first second third body)
    (Formula.always₃Saturated first second third body))

/-- ✱11·21 suit ✱11·01·02, ✱11·2 et ✱10·271.
`demonstration_provenance: follows-printed`. -/
theorem star_11_21
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation
      (star_11_21_reading first second third negation disjunction body).parsed := by
  have line1 := star_11_01_star_11_02_star_11_2_star_10_271_instance
    first second third negation disjunction body
  exact line1

private def star_11_22_common
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  Formula.neg negation
    (Formula.always₂Saturated inner outer (Formula.neg negation body))

private theorem star_10_252_star_11_03_star_10_252_star_10_271_star_11_01_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ star_4_01 negation disjunction
      (star_11_22_common inner outer negation body)
      (star_11_22_common inner outer negation body) := by
  have line1 := star_4_2 negation disjunction
    (star_11_22_common inner outer negation body)
  exact line1

def star_11_22_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : (∃x, y).φ(x, y) .≡ .∼{(x, y).∼φ(x, y)}"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_22_common inner outer negation body)
    (star_11_22_common inner outer negation body))

/-- ✱11·22 suit ✱10·252, ✱11·03, ✱10·252·271 et ✱11·01.
`demonstration_provenance: follows-printed`. -/
theorem star_11_22
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_22_reading inner outer negation disjunction body).parsed := by
  have line1 :=
    star_10_252_star_11_03_star_10_252_star_10_271_star_11_01_instance
      inner outer negation disjunction body
  exact line1

private theorem star_11_22_star_11_2_transp_star_11_22_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ star_4_01 negation disjunction
      (star_11_22_common inner outer negation body)
      (star_11_22_common inner outer negation body) := by
  have line1 := star_4_2 negation disjunction
    (star_11_22_common inner outer negation body)
  exact line1

def star_11_23_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : (∃x, y).φ(x, y) .≡ .(∃y, x).φ(x, y)"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_22_common inner outer negation body)
    (star_11_22_common inner outer negation body))

/-- ✱11·23 suit ✱11·22, ✱11·2.Transp, puis ✱11·22.
`demonstration_provenance: follows-printed`. -/
theorem star_11_23
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_23_reading inner outer negation disjunction body).parsed := by
  have line1 := star_11_22_star_11_2_transp_star_11_22_instance
    inner outer negation disjunction body
  exact line1

private def star_11_24_common
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.neg negation
    (Formula.always₃Saturated first second third (Formula.neg negation body))

private theorem star_11_03_star_11_04_star_11_23_star_10_281_instance
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ star_4_01 negation disjunction
      (star_11_24_common first second third negation body)
      (star_11_24_common first second third negation body) := by
  have line1 := star_4_2 negation disjunction
    (star_11_24_common first second third negation body)
  exact line1

def star_11_24_reading
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : (∃x, y, z).φ(x, y, z) .≡ .(∃y, z, x).φ(x, y, z)"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_24_common first second third negation body)
    (star_11_24_common first second third negation body))

/-- ✱11·24 suit ✱11·03·04, ✱11·23 et ✱10·281.
`demonstration_provenance: follows-printed`. -/
theorem star_11_24
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation
      (star_11_24_reading first second third negation disjunction body).parsed := by
  have line1 := star_11_03_star_11_04_star_11_23_star_10_281_instance
    first second third negation disjunction body
  exact line1

private theorem star_11_22_transp_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    let universalNegation :=
      Formula.always₂Saturated inner outer (Formula.neg negation body)
    ⊢ᵣ star_4_01 negation disjunction
      (Formula.neg negation (Formula.neg negation universalNegation))
      universalNegation := by
  let universalNegation :=
    Formula.always₂Saturated inner outer (Formula.neg negation body)
  have line1 := star_2_14 negation disjunction universalNegation
  have line2 := star_2_12 negation disjunction universalNegation
  have line3 := conjoin negation disjunction
    (implication negation disjunction
      (Formula.neg negation (Formula.neg negation universalNegation))
      universalNegation)
    (implication negation disjunction universalNegation
      (Formula.neg negation (Formula.neg negation universalNegation)))
    line1 line2
  exact line3

def star_11_25_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : ∼{(∃x, y).φ(x, y)} .≡ .(x, y).∼φ(x, y)"
  parsed :=
    let universalNegation :=
      Formula.always₂Saturated inner outer (Formula.neg negation body)
    .assertion (star_4_01 negation disjunction
      (Formula.neg negation (Formula.neg negation universalNegation))
      universalNegation)

/-- ✱11·25 est la transposition imprimée de ✱11·22.
`demonstration_provenance: follows-printed`. -/
theorem star_11_25
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_25_reading inner outer negation disjunction body).parsed := by
  have line1 := star_11_22_transp_instance
    inner outer negation disjunction body
  exact line1

private theorem star_4_2_star_11_03_star_10_11_star_10_281_star_11_04_instance
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :
    let common := star_11_24_common first second third negation body
    ⊢ᵣ conjunction negation disjunction
      (star_4_01 negation disjunction common common)
      (star_4_01 negation disjunction common common) := by
  let common := star_11_24_common first second third negation body
  have line1 := star_4_2 negation disjunction common
  have line2 := star_4_2 negation disjunction common
  have line3 := conjoin negation disjunction
    (star_4_01 negation disjunction common common)
    (star_4_01 negation disjunction common common) line1 line2
  exact line3

def star_11_27_reading
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : .(∃x, y) : (∃z).φ(x, y, z) .≡ : (∃x) : (∃y, z).φ(x, y, z) ≡ : (∃x, y, z).φ(x, y, z)"
  parsed :=
    let common := star_11_24_common first second third negation body
    .assertion (conjunction negation disjunction
      (star_4_01 negation disjunction common common)
      (star_4_01 negation disjunction common common))

/-- ✱11·27 suit ses trois lignes imprimées, de ✱4·2 à ✱11·04.
`demonstration_provenance: follows-printed`. -/
theorem star_11_27
    (first : signature.Universal sort (bindOrder baseOrder sort))
    (second : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (third : signature.Universal sort
      (bindOrder
        (bindOrder (bindOrder baseOrder sort) sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation
      (star_11_27_reading first second third negation disjunction body).parsed := by
  have line1 :=
    star_4_2_star_11_03_star_10_11_star_10_281_star_11_04_instance
      first second third negation disjunction body
  exact line1

private def Formula.alwaysHeadSaturated
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real (sort :: apparent)
      (bindOrder baseOrder sort)) :
    Formula signature real apparent (bindOrder baseOrder sort) :=
  Eq.mp (congrArg (Formula signature real apparent)
    (bindOrder_idem baseOrder sort)) (.always universal body)

private theorem star_10_1_saturated
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort))
    (value : Term signature real [] sort) :
    ⊢ᵣ implication negation disjunction
      (Formula.alwaysHeadSaturated universal body) (body.instantiate value) := by
  let closureEq := bindOrder_idem baseOrder sort
  let resultEq := natMaxCongr closureEq rfl
  let rawNegation := Eq.mp
    (congrArg signature.Negation closureEq.symm) negation
  let rawDisjunction := Eq.mp
    (congrArg signature.Disjunction resultEq.symm) disjunction
  have line1 := Derivation.star_10_1 universal rawNegation rawDisjunction body value
  have line2 := castAssertionOrder resultEq
    (mixedImplication rawNegation rawDisjunction
      (.always universal body) (body.instantiate value)) line1
  have line3 := mixedImplication_normalizeSameOrder closureEq rfl
    negation disjunction (.always universal body) (body.instantiate value)
  exact Derivation.castAssertion line3.symm line2

private def keepHeadRenaming (sort : RSort) : Renaming [sort] [sort, sort] := by
  intro variable
  cases variable with
  | zero => exact .zero

private def star_11_26_forallYAtX
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Formula signature real [sort, sort] (bindOrder baseOrder sort) :=
  (Formula.alwaysHeadSaturated universal body.swapHeads).rename
    (keepHeadRenaming sort)

private def star_11_26_matrix
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  implication negation disjunction (Formula.neg negation body)
    (Formula.neg negation (star_11_26_forallYAtX universal body))

private theorem star_10_1_star_10_28_star_10_11_star_10_21_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_26_matrix inner negation disjunction body) := by
  apply star_11_11_saturated inner outer
    (star_11_26_matrix inner negation disjunction body)
  intro left right
  let bodyAtLeft := body.instantiate left.weaken
  let universalAtLeft := Formula.alwaysHeadSaturated inner bodyAtLeft
  have line1 := star_10_1_saturated inner negation disjunction bodyAtLeft right
  have line2 := detach negation disjunction
    (implication negation disjunction universalAtLeft
      (bodyAtLeft.instantiate right))
    (implication negation disjunction
      (Formula.neg negation (bodyAtLeft.instantiate right))
      (Formula.neg negation universalAtLeft)) line1
    (star_2_16 negation disjunction universalAtLeft
      (bodyAtLeft.instantiate right))
  have matrixEq :
      (star_11_26_matrix inner negation disjunction body).instantiate₂
          left right =
        implication negation disjunction
          (Formula.neg negation (bodyAtLeft.instantiate right))
          (Formula.neg negation universalAtLeft) := by
    dsimp [star_11_26_matrix, bodyAtLeft, universalAtLeft,
      star_11_26_forallYAtX, Formula.alwaysHeadSaturated,
      keepHeadRenaming]
    rw [bindOrder_idem]
    rfl
  exact Derivation.castAssertion matrixEq line2

def star_11_26_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : ClaimReading signature real where
  printed := "⊢ : .(∃x) : (y).φ(x, y) .⊃ : (y) : (∃x).φ(x, y)"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_11_26_matrix inner negation disjunction body))

/-- ✱11·26 suit ✱10·1·28 puis ✱10·11·21.
`demonstration_provenance: follows-printed`. -/
theorem star_11_26
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Derivation (star_11_26_reading inner outer negation disjunction body).parsed := by
  have line1 := star_10_1_star_10_28_star_10_11_star_10_21_instance
    inner outer negation disjunction body
  exact line1

#print axioms star_11_07
#print axioms star_11_1
#print axioms star_11_11
#print axioms star_11_2
#print axioms star_11_21
#print axioms star_11_22
#print axioms star_11_23
#print axioms star_11_24
#print axioms star_11_25
#print axioms star_11_26
#print axioms star_11_13
#print axioms star_11_311
#print axioms star_11_3
#print axioms star_11_32
#print axioms star_11_33
#print axioms star_11_34
#print axioms star_11_35
#print axioms star_11_37
#print axioms star_11_4
#print axioms star_11_27

end PM.RamifiedSyntax
