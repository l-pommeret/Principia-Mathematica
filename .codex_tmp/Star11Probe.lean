import Principia.Deduction.Star11Derived

namespace PM.RamifiedSyntax.Probe

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

private def emptyRenaming (target : Context) : Renaming [] target := by
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
      liftSubstitution tau (liftSubstitution sigma v) =
        liftSubstitution (substitutionAfterSubstitution sigma tau) v := by
  intro sort v
  cases v with
  | zero => rfl
  | succ v =>
      exact Eq.trans (Term.weaken_substitute_lift tau (sigma v))
        (congrArg Term.weaken (Term.substitute_substitute sigma tau (sigma v)))

private theorem liftSubstitutionN_comp_pointwise
    (binders : List RSort)
    (sigma : Substitution signature real source middle)
    (tau : Substitution signature real middle target) :
    ∀ {sort} (v : Var (binders ++ source) sort),
      liftSubstitutionN binders tau (liftSubstitutionN binders sigma v) =
        liftSubstitutionN binders (substitutionAfterSubstitution sigma tau) v := by
  induction binders with
  | nil =>
      intro sort v
      exact Term.substitute_substitute sigma tau (sigma v)
  | cons binder binders ih =>
      intro sort v
      cases v with
      | zero => rfl
      | succ v =>
          exact Eq.trans
            (Term.weaken_substitute_lift (liftSubstitutionN binders tau)
              (liftSubstitutionN binders sigma v))
            (congrArg Term.weaken (ih v))

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
  induction formula with
  | proposition term =>
      show Formula.proposition _ = Formula.proposition _
      rw [Term.substitute_of_pointwise sigma tau pointwise]
  | apply function arguments =>
      show Formula.apply _ _ = Formula.apply _ _
      rw [Term.substitute_of_pointwise sigma tau pointwise,
        Arguments.substitute_of_pointwise sigma tau pointwise]
  | neg meaning body ih =>
      show Formula.neg _ _ = Formula.neg _ _
      rw [ih (liftSubstitution sigma) (liftSubstitution tau)]
      exact liftSubstitution_pointwise (fun v => v) sigma tau pointwise
  | disj meaning left right leftIH rightIH =>
      show Formula.disj _ _ _ = Formula.disj _ _ _
      rw [leftIH sigma tau pointwise, rightIH sigma tau pointwise]
  | always meaning body ih =>
      show Formula.always _ _ = Formula.always _ _
      rw [ih (liftSubstitution sigma) (liftSubstitution tau)]
      exact liftSubstitution_pointwise (fun v => v) sigma tau pointwise
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH (liftSubstitutionN parameters sigma)
          (liftSubstitutionN parameters tau),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)]
      · exact liftSubstitutionN_pointwise parameters (fun v => v) sigma tau pointwise
      · exact liftSubstitution_pointwise (fun v => v) sigma tau pointwise
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH (liftSubstitution sigma) (liftSubstitution tau),
        continuationIH (liftSubstitution sigma) (liftSubstitution tau)]
      · exact liftSubstitution_pointwise (fun v => v) sigma tau pointwise
      · exact liftSubstitution_pointwise (fun v => v) sigma tau pointwise

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
      rw [ih]
      exact congrArg (Formula.always meaning)
        (Formula.substitute_of_pointwise _ _
          (liftSubstitution_comp_pointwise sigma tau) body)
  | incompleteScope kind parameters resultOrder excess scopeOrder
      matrix continuation matrixIH continuationIH =>
      show Formula.incompleteScope _ _ _ _ _ _ _ =
        Formula.incompleteScope _ _ _ _ _ _ _
      rw [matrixIH, continuationIH]
      congr
      · exact Formula.substitute_of_pointwise _ _
          (liftSubstitutionN_comp_pointwise parameters sigma tau) matrix
      · exact Formula.substitute_of_pointwise _ _
          (liftSubstitution_comp_pointwise sigma tau) continuation
  | descriptionScope sort conditionOrder scopeOrder
      condition continuation conditionIH continuationIH =>
      show Formula.descriptionScope _ _ _ _ _ =
        Formula.descriptionScope _ _ _ _ _
      rw [conditionIH, continuationIH]
      congr
      · exact Formula.substitute_of_pointwise _ _
          (liftSubstitution_comp_pointwise sigma tau) condition
      · exact Formula.substitute_of_pointwise _ _
          (liftSubstitution_comp_pointwise sigma tau) continuation

private def Formula.weakenApparent₂
    (formula : Formula signature real [] order) :
    Formula signature real [sort, sort] order :=
  formula.rename (emptyRenaming [sort, sort])

private theorem Formula.weakenApparent₂_instantiate₂
    (formula : Formula signature real [] order)
    (left right : Term signature real [] sort) :
    (Formula.weakenApparent₂ (sort := sort) formula).instantiate₂ left right =
      formula := by
  unfold Formula.weakenApparent₂ Formula.instantiate₂ Formula.instantiate
  rw [Formula.rename_substitute, Formula.substitute_substitute]
  exact Formula.substitute_eq_self formula (fun v => nomatch v)

#print axioms PM.RamifiedSyntax.Probe.bindOrder_idem
#print axioms PM.RamifiedSyntax.Probe.star_11_1_saturated
#print axioms PM.RamifiedSyntax.Probe.star_11_11_saturated
#print axioms PM.RamifiedSyntax.Probe.Formula.weakenApparent₂_instantiate₂

end PM.RamifiedSyntax.Probe
