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

private theorem castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
    Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

private theorem Term.rename_rename_of_pointwise
    (rho : Renaming source middle) (tau : Renaming middle target)
    (upsilon : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), tau (rho v) = upsilon v)
    (term : Term signature realCtx source sort) :
    (term.rename rho).rename tau = term.rename upsilon := by
  cases term with
  | real v => rfl
  | apparent v => exact congrArg Term.apparent (pointwise v)
  | symbol payload => rfl

private theorem Arguments.rename_rename_of_pointwise
    (rho : Renaming source middle) (tau : Renaming middle target)
    (upsilon : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), tau (rho v) = upsilon v)
    (arguments : Arguments signature realCtx source sorts) :
    (arguments.rename rho).rename tau = arguments.rename upsilon := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.rename_rename_of_pointwise rho tau upsilon pointwise term, ih]

private theorem liftRenaming_comp_pointwise
    (rho : Renaming source middle) (tau : Renaming middle target)
    (upsilon : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), tau (rho v) = upsilon v) :
    ∀ {sort} (v : Var (binder :: source) sort),
      liftRenaming tau (liftRenaming rho v) = liftRenaming upsilon v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Var.succ (pointwise v)

private theorem liftRenamingN_comp_pointwise
    (binders : List RSort)
    (rho : Renaming source middle) (tau : Renaming middle target)
    (upsilon : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), tau (rho v) = upsilon v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftRenamingN binders tau (liftRenamingN binders rho v) =
        liftRenamingN binders upsilon v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih => exact liftRenaming_comp_pointwise _ _ _ ih

private theorem Formula.rename_rename_of_pointwise
    (rho : Renaming source middle) (tau : Renaming middle target)
    (upsilon : Renaming source target)
    (pointwise : ∀ {sort} (v : Var source sort), tau (rho v) = upsilon v)
    (formula : Formula signature realCtx source order) :
    (formula.rename rho).rename tau = formula.rename upsilon := by
  induction formula generalizing middle target with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.rename_rename_of_pointwise rho tau upsilon pointwise term]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.rename_rename_of_pointwise rho tau upsilon pointwise function,
        Arguments.rename_rename_of_pointwise rho tau upsilon pointwise arguments]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih rho tau upsilon pointwise]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH rho tau upsilon pointwise, rightIH rho tau upsilon pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      rw [ih (liftRenaming rho) (liftRenaming tau) (liftRenaming upsilon)
        (liftRenaming_comp_pointwise rho tau upsilon pointwise)]
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftRenamingN parameters rho) (liftRenamingN parameters tau)
          (liftRenamingN parameters upsilon)
          (liftRenamingN_comp_pointwise parameters rho tau upsilon pointwise),
        continuationIH (liftRenaming rho) (liftRenaming tau) (liftRenaming upsilon)
          (liftRenaming_comp_pointwise rho tau upsilon pointwise)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftRenaming rho) (liftRenaming tau) (liftRenaming upsilon)
          (liftRenaming_comp_pointwise rho tau upsilon pointwise),
        continuationIH (liftRenaming rho) (liftRenaming tau) (liftRenaming upsilon)
          (liftRenaming_comp_pointwise rho tau upsilon pointwise)]

private theorem Term.rename_eq_self
    (rho : Renaming source source)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = v)
    (term : Term signature realCtx source sort) :
    term.rename rho = term := by
  cases term with
  | real v => rfl
  | apparent v => exact congrArg Term.apparent (pointwise v)
  | symbol payload => rfl

private theorem Arguments.rename_eq_self
    (rho : Renaming source source)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = v)
    (arguments : Arguments signature realCtx source sorts) :
    arguments.rename rho = arguments := by
  induction arguments with
  | nil => rfl
  | cons term tail ih =>
      show Arguments.cons _ _ = Arguments.cons _ _
      rw [Term.rename_eq_self rho pointwise term, ih]

private theorem liftRenaming_eq_self
    (rho : Renaming source source)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = v) :
    ∀ {sort} (v : Var (binder :: source) sort), liftRenaming rho v = v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v => exact congrArg Var.succ (pointwise v)

private theorem liftRenamingN_eq_self
    (binders : List RSort)
    (rho : Renaming source source)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = v) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftRenamingN binders rho v = v := by
  induction binders with
  | nil => exact pointwise
  | cons binder binders ih => exact liftRenaming_eq_self _ ih

private theorem Formula.rename_eq_self
    (rho : Renaming source source)
    (pointwise : ∀ {sort} (v : Var source sort), rho v = v)
    (formula : Formula signature realCtx source order) :
    formula.rename rho = formula := by
  induction formula with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.rename_eq_self rho pointwise term]
  | apply function arguments =>
      change Formula.apply (function.rename rho) (arguments.rename rho) = _
      rw [Term.rename_eq_self rho pointwise function,
        Arguments.rename_eq_self rho pointwise arguments]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih rho pointwise]
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH rho pointwise, rightIH rho pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      rw [ih (liftRenaming rho) (liftRenaming_eq_self rho pointwise)]
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftRenamingN parameters rho)
          (liftRenamingN_eq_self parameters rho pointwise),
        continuationIH (liftRenaming rho) (liftRenaming_eq_self rho pointwise)]
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftRenaming rho) (liftRenaming_eq_self rho pointwise),
        continuationIH (liftRenaming rho) (liftRenaming_eq_self rho pointwise)]

private theorem Formula.swapHeads_swapHeads
    (formula : Formula signature real
      (leftSort :: rightSort :: apparent) order) :
    formula.swapHeads.swapHeads = formula := by
  have pointwise : ∀ {sort} (v : Var
      (leftSort :: rightSort :: apparent) sort),
      swapHeadsRenaming (swapHeadsRenaming v) = v := by
    intro sort v
    cases v with
    | zero => rfl
    | succ v =>
        cases v with
        | zero => rfl
        | succ v => rfl
  have line1 := Formula.rename_rename_of_pointwise
    (signature := signature) (realCtx := real)
    swapHeadsRenaming swapHeadsRenaming (fun v => v) pointwise formula
  have line2 := Formula.rename_eq_self (signature := signature)
    (realCtx := real) (fun v => v) (fun _ => rfl) formula
  exact Eq.trans line1 line2

private theorem exchangeSameSort
    (inner : signature.Universal sort matrixOrder)
    (outer : signature.Universal sort (bindOrder matrixOrder sort))
    (swappedInner : signature.Universal sort matrixOrder)
    (swappedOuter : signature.Universal sort (bindOrder matrixOrder sort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder sort) sort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder sort) sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    ⊢ᵣ implication negation disjunction
      (body.always₂ inner outer)
      (body.swapHeads.always₂ swappedInner swappedOuter) := by
  let castDisjunction := Eq.mp
    (congrArg signature.Disjunction
      (natMaxSelf (bindOrder (bindOrder matrixOrder sort) sort)).symm)
    disjunction
  have line1 := Derivation.star_11_07 inner outer swappedInner swappedOuter
    negation castDisjunction body
  exact castAssertionOrder
    (natMaxSelf (bindOrder (bindOrder matrixOrder sort) sort))
    (mixedImplication negation castDisjunction
      (body.always₂ inner outer)
      (body.swapHeads.always₂ swappedInner swappedOuter)) line1

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

/-- Catalogue reading of ✱11·2. -/
def star_11_2_reading
    (leftInner : signature.Universal sort matrixOrder)
    (rightOuter : signature.Universal sort (bindOrder matrixOrder sort))
    (rightInner : signature.Universal sort matrixOrder)
    (leftOuter : signature.Universal sort (bindOrder matrixOrder sort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder sort) sort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder sort) sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    ClaimReading signature real where
  printed := "⊢ : (x, y).φ(x, y) .≡ .(y, x).φ(x, y)"
  parsed := .assertion (conjunction negation disjunction
    (implication negation disjunction
      (body.always₂ leftInner rightOuter)
      (body.swapHeads.always₂ rightInner leftOuter))
    (implication negation disjunction
      (body.swapHeads.always₂ rightInner leftOuter)
      (body.always₂ leftInner rightOuter)))

/-- ✱11·2, reconstructed from primitive exchange in both directions and adjunction.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_11_2
    (leftInner : signature.Universal sort matrixOrder)
    (rightOuter : signature.Universal sort (bindOrder matrixOrder sort))
    (rightInner : signature.Universal sort matrixOrder)
    (leftOuter : signature.Universal sort (bindOrder matrixOrder sort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder sort) sort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder sort) sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    Derivation (star_11_2_reading leftInner rightOuter rightInner leftOuter
      negation disjunction body).parsed := by
  have line1 := exchangeSameSort leftInner rightOuter rightInner leftOuter
    negation disjunction body
  have line2 := exchangeSameSort rightInner leftOuter leftInner rightOuter
    negation disjunction body.swapHeads
  rw [Formula.swapHeads_swapHeads] at line2
  have line3 := conjoin negation disjunction
    (implication negation disjunction
      (body.always₂ leftInner rightOuter)
      (body.swapHeads.always₂ rightInner leftOuter))
    (implication negation disjunction
      (body.swapHeads.always₂ rightInner leftOuter)
      (body.always₂ leftInner rightOuter)) line1 line2
  exact line3

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
#print axioms star_11_2
#print axioms star_11_13
#print axioms star_11_311

end PM.RamifiedSyntax
