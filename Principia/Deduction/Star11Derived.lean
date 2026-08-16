import Principia.Deduction.Star10Derived

namespace PM.RamifiedSyntax

variable {real : Context}

/-- T4 reading used throughout ✱11. The parsed field is an object-calculus
claim; the scope note records that PM's dots are resolved by that ramified AST. -/
structure Star11Reading (signature : Signature) (real : Context) where
  printed : String
  parsed : Claim signature real
  scopeReading : String :=
    "PM's scope dots and apparent-variable binders are represented by the parsed ramified AST."

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

/-! ## The eliminable definitions ✱11·01--·06

These declarations retain the grouping printed by PM.  In particular the
two- and three-place existential signs are nested applications of
`Formula.sometimes`; they are not replaced by a logically equivalent single
negated universal closure.
-/

/-- ✱11·01: `(x,y).φ(x,y) := (x):(y).φ(x,y)`. -/
def star_11_01
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real (leftSort :: rightSort :: apparent)
      matrixOrder) :
    Formula signature real apparent
      (bindOrder (bindOrder matrixOrder leftSort) rightSort) :=
  body.always₂ inner outer

theorem star_11_01_unfold
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real (leftSort :: rightSort :: apparent)
      matrixOrder) :
    star_11_01 inner outer body =
      .always outer (.always inner body) := rfl

/-- Audited scope reading of ✱11·01. -/
def star_11_01_reading
    (inner : signature.Universal leftSort matrixOrder)
    (outer : signature.Universal rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Star11Reading signature real where
  printed := "(x, y).φ(x, y) .= : (x) : (y).φ(x, y)  Df"
  parsed := .assertion (star_11_01 inner outer body)

/-- ✱11·02: `(x,y,z).φ := (x):(y,z).φ`. -/
def star_11_02
    (first : signature.Universal firstSort matrixOrder)
    (second : signature.Universal secondSort
      (bindOrder matrixOrder firstSort))
    (third : signature.Universal thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      (firstSort :: secondSort :: thirdSort :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort) :=
  .always third (.always second (.always first body))

theorem star_11_02_unfold
    (first : signature.Universal firstSort matrixOrder)
    (second : signature.Universal secondSort
      (bindOrder matrixOrder firstSort))
    (third : signature.Universal thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      (firstSort :: secondSort :: thirdSort :: apparent) matrixOrder) :
    star_11_02 first second third body =
      .always third (.always second (.always first body)) := rfl

/-- Audited scope reading of ✱11·02. -/
def star_11_02_reading
    (first : signature.Universal firstSort matrixOrder)
    (second : signature.Universal secondSort
      (bindOrder matrixOrder firstSort))
    (third : signature.Universal thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    Star11Reading signature real where
  printed := "(x, y, z).φ(x, y, z) .= : (x) : (y, z).φ(x, y, z)  Df"
  parsed := .assertion (star_11_02 first second third body)

/-- ✱11·03: `(∃x,y).φ := (∃x):(∃y).φ`. -/
def star_11_03
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real (leftSort :: rightSort :: apparent)
      matrixOrder) :
    Formula signature real apparent
      (bindOrder (bindOrder matrixOrder leftSort) rightSort) :=
  Formula.sometimes outer (Formula.sometimes inner body)

theorem star_11_03_unfold
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real (leftSort :: rightSort :: apparent)
      matrixOrder) :
    star_11_03 inner outer body =
      Formula.sometimes outer (Formula.sometimes inner body) := rfl

/-- Audited scope reading of ✱11·03. -/
def star_11_03_reading
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Star11Reading signature real where
  printed := "(∃x, y).φ(x, y) .= : (∃x) : (∃y).φ(x, y)  Df"
  parsed := .assertion (star_11_03 inner outer body)

/-- ✱11·04: `(∃x,y,z).φ := (∃x):(∃y,z).φ`. -/
def star_11_04
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      (firstSort :: secondSort :: thirdSort :: apparent) matrixOrder) :
    Formula signature real apparent
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort) :=
  Formula.sometimes third
    (Formula.sometimes second (Formula.sometimes first body))

theorem star_11_04_unfold
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      (firstSort :: secondSort :: thirdSort :: apparent) matrixOrder) :
    star_11_04 first second third body =
      Formula.sometimes third
        (Formula.sometimes second (Formula.sometimes first body)) := rfl

/-- Audited scope reading of ✱11·04. -/
def star_11_04_reading
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    Star11Reading signature real where
  printed := "(∃x, y, z).φ(x, y, z) .= : (∃x) : (∃y, z).φ(x, y, z)  Df"
  parsed := .assertion (star_11_04 first second third body)

/-- ✱11·05: binary pointwise implication. -/
def star_11_05
    (inner : signature.Universal leftSort (max leftOrder rightOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max leftOrder rightOrder) leftSort))
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (phi : Formula signature real (leftSort :: rightSort :: apparent)
      leftOrder)
    (psi : Formula signature real (leftSort :: rightSort :: apparent)
      rightOrder) :
    Formula signature real apparent
      (bindOrder (bindOrder (max leftOrder rightOrder) leftSort) rightSort) :=
  .always outer (.always inner
    (mixedImplication negation disjunction phi psi))

theorem star_11_05_unfold
    (inner : signature.Universal leftSort (max leftOrder rightOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max leftOrder rightOrder) leftSort))
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (phi : Formula signature real (leftSort :: rightSort :: apparent)
      leftOrder)
    (psi : Formula signature real (leftSort :: rightSort :: apparent)
      rightOrder) :
    star_11_05 inner outer negation disjunction phi psi =
      .always outer (.always inner
        (mixedImplication negation disjunction phi psi)) := rfl

/-- Audited scope reading of ✱11·05. -/
def star_11_05_reading
    (inner : signature.Universal leftSort (max leftOrder rightOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max leftOrder rightOrder) leftSort))
    (negation : signature.Negation leftOrder)
    (disjunction : signature.Disjunction (max leftOrder rightOrder))
    (phi : Formula signature real [leftSort, rightSort] leftOrder)
    (psi : Formula signature real [leftSort, rightSort] rightOrder) :
    Star11Reading signature real where
  printed :=
    "φ(x, y) .⊃ₓ,ᵧ. ψ(x, y) .= : (x, y) : φ(x, y) .⊃ .ψ(x, y)  Df"
  parsed := .assertion
    (star_11_05 inner outer negation disjunction phi psi)

/-- ✱11·06: binary pointwise equivalence at one assigned order. -/
def star_11_06
    (inner : signature.Universal leftSort order)
    (outer : signature.Universal rightSort (bindOrder order leftSort))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real
      (leftSort :: rightSort :: apparent) order) :
    Formula signature real apparent
      (bindOrder (bindOrder order leftSort) rightSort) :=
  .always outer (.always inner
    (equivalence negation disjunction phi psi))

theorem star_11_06_unfold
    (inner : signature.Universal leftSort order)
    (outer : signature.Universal rightSort (bindOrder order leftSort))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real
      (leftSort :: rightSort :: apparent) order) :
    star_11_06 inner outer negation disjunction phi psi =
      .always outer (.always inner
        (equivalence negation disjunction phi psi)) := rfl

/-- Audited scope reading of ✱11·06. -/
def star_11_06_reading
    (inner : signature.Universal leftSort order)
    (outer : signature.Universal rightSort (bindOrder order leftSort))
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [leftSort, rightSort] order) :
    Star11Reading signature real where
  printed :=
    "φ(x, y) .≡ₓ,ᵧ. ψ(x, y) .= : (x, y) : φ(x, y) .≡ .ψ(x, y)  Df"
  parsed := .assertion
    (star_11_06 inner outer negation disjunction phi psi)

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
    Star11Reading signature real where
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
    (w : Term signature real [] rightSort) : Star11Reading signature real where
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
    Star11Reading signature real where
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

def star_11_12_left
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort) :=
  .always outer (.always inner
    (.disj matrixDisjunction
      ((p.rename (emptyRenaming (target := [rightSort]))).rename
        (fun v => .succ v))
      body))

/-- The printed right member `p ∨ (x,y).φ(x,y)`.  Its root is the outer
universal binder required by scope; the remaining `p ∨ (x).φ` is represented
by ✱9·04, not by a raw disjunction with a quantified argument. -/
def star_11_12_right
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort) :=
  .always outer
    (star_9_04 inner matrixDisjunction
      (p.rename (emptyRenaming (target := [rightSort]))) body)

theorem star_11_12_right_unfold
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    star_11_12_right inner outer matrixDisjunction p body =
      star_11_12_left inner outer matrixDisjunction p body := by
  unfold star_11_12_right star_11_12_left
  rw [star_9_04_unfold]

def star_11_12_reading
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerNegation : signature.Negation
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (outerDisjunction : signature.Disjunction
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (p : Formula signature real [] fixedOrder)
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Star11Reading signature real where
  printed := "⊢ : .(x, y).p∨φ(x, y) .⊃ : p .∨ .(x, y).φ(x, y)"
  parsed := .assertion (implication outerNegation outerDisjunction
    (star_11_12_left inner outer matrixDisjunction p body)
    (star_11_12_right inner outer matrixDisjunction p body))
  scopeReading := "The right member is rooted at the outer universal and retains ✱9·04 at the inner scope; unfolding that Df yields the independently built left member."

/-- ✱11·12.  PM's two occurrences of ✱10·12 reduce to the same ✱9·04
scope rewrite; the intervening generalization supplies the outer binder.
`demonstration_provenance: follows-printed-definitional-normalization`. -/
theorem star_11_12
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerNegation : signature.Negation
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (outerDisjunction : signature.Disjunction
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (p : Formula signature real [] fixedOrder)
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Derivation (star_11_12_reading inner outer matrixDisjunction
      outerNegation outerDisjunction p body).parsed := by
  have line1 := star_2_08 outerNegation outerDisjunction
    (star_11_12_left inner outer matrixDisjunction p body)
  have line2 : Derivation (.assertion (implication outerNegation
      outerDisjunction
      (star_11_12_left inner outer matrixDisjunction p body)
      (star_11_12_right inner outer matrixDisjunction p body))) := by
    rw [star_11_12_right_unfold]
    exact line1
  exact line2


/-- Catalogue reading of the metalinguistic rule ✱11·13. -/
def star_11_13_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [] order) :
    Star11Reading signature real where
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
    Star11Reading signature real where
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

private def Formula.sometimes₂Saturated
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  Formula.neg negation
    (Formula.always₂Saturated inner outer (Formula.neg negation body))

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

def star_11_14_left
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  conjunction negation disjunction
    (Formula.always₂Saturated inner outer phi)
    (Formula.always₂Saturated inner outer psi)

def star_11_14_right
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  conjunction negation disjunction
    (phi.instantiate₂ left right) (psi.instantiate₂ left right)

def star_11_14_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) :
    Star11Reading signature real where
  printed := "⊢ : .(x, y).φ(x, y) : (x, y).ψ(x, y) .⊃ .φ(z, w).ψ(z, w)"
  parsed := .assertion (implication negation disjunction
    (star_11_14_left inner outer negation disjunction phi psi)
    (star_11_14_right negation disjunction phi psi left right))
  scopeReading := "The antecedent is the conjunction of the two independently closed matrices; the consequent is the conjunction of their independently specialized instances."

/-- ✱11·14.  The two printed occurrences of ✱10·14 are the two
specializations; propositional combination gives the displayed conjunction.
`demonstration_provenance: follows-printed`. -/
theorem star_11_14
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) :
    Derivation
      (star_11_14_reading inner outer negation disjunction
        phi psi left right).parsed := by
  let phiClosed := Formula.always₂Saturated inner outer phi
  let psiClosed := Formula.always₂Saturated inner outer psi
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  have line1a := star_11_1_saturated inner outer negation disjunction
    phi left right
  have line1b := star_11_1_saturated inner outer negation disjunction
    psi left right
  have line1 := conjoin negation disjunction
    (implication negation disjunction phiClosed phiInstance)
    (implication negation disjunction psiClosed psiInstance) line1a line1b
  have line2 := star_3_47 negation disjunction
    phiClosed psiClosed phiInstance psiInstance
  have line3 := detach negation disjunction _ _ line1 line2
  exact line3

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

private def renamingSubstitution
    (rho : Renaming source target) :
    Substitution signature real source target :=
  fun v => .apparent (rho v)

private theorem Formula.rename_eq_substitute
    (rho : Renaming source target)
    (formula : Formula signature real source order) :
    formula.rename rho = formula.substitute (renamingSubstitution rho) := by
  let identity : Substitution signature real target target :=
    fun v => .apparent v
  have line1 := Formula.substitute_eq_self (formula.rename rho)
    (sigma := identity) (fun _ => rfl)
  have line2 := Formula.rename_substitute_of_pointwise rho identity
    (renamingSubstitution rho) (fun _ => rfl) formula
  exact Eq.trans line1.symm line2

private theorem Formula.swapHeads_involutive
    (formula : Formula signature real [sort, sort] order) :
    formula.swapHeads.swapHeads = formula := by
  unfold Formula.swapHeads
  calc
    (formula.rename swapHeadsRenaming).rename swapHeadsRenaming =
        (formula.rename swapHeadsRenaming).substitute
          (renamingSubstitution swapHeadsRenaming) :=
      Formula.rename_eq_substitute swapHeadsRenaming
        (formula.rename swapHeadsRenaming)
    _ = formula.substitute
        (substitutionAfterRenaming swapHeadsRenaming
          (renamingSubstitution swapHeadsRenaming)) :=
      Formula.rename_substitute swapHeadsRenaming
        (renamingSubstitution swapHeadsRenaming) formula
    _ = formula := by
      apply Formula.substitute_eq_self
      intro targetSort v
      cases v with
      | zero => rfl
      | succ v =>
          cases v with
          | zero => rfl
          | succ v => rfl

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

def star_11_2_left
    (inner : signature.Universal sort matrixOrder)
    (outer : signature.Universal sort (bindOrder matrixOrder sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    Formula signature real []
      (bindOrder (bindOrder matrixOrder sort) sort) :=
  star_11_01 inner outer body

def star_11_2_right
    (inner : signature.Universal sort matrixOrder)
    (outer : signature.Universal sort (bindOrder matrixOrder sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    Formula signature real []
      (bindOrder (bindOrder matrixOrder sort) sort) :=
  star_11_01 inner outer body.swapHeads

private theorem star_11_07_normalized
    (inner : signature.Universal sort matrixOrder)
    (outer : signature.Universal sort (bindOrder matrixOrder sort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder sort) sort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder sort) sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    ⊢ᵣ implication negation disjunction
      (star_11_2_left inner outer body)
      (star_11_2_right inner outer body) := by
  let closureOrder := bindOrder (bindOrder matrixOrder sort) sort
  let pairEq := natMaxSelf closureOrder
  let rawDisjunction := Eq.mp
    (congrArg signature.Disjunction pairEq.symm) disjunction
  have line1 := Derivation.star_11_07 inner outer inner outer negation
    rawDisjunction body
  have line2 := castAssertionOrder pairEq
    (star_11_07_formula inner outer inner outer negation rawDisjunction body)
    line1
  have line3 := mixedImplication_normalizeSameOrder rfl rfl
    negation disjunction (star_11_2_left inner outer body)
      (star_11_2_right inner outer body)
  exact Derivation.castAssertion line3.symm line2

private theorem star_11_07_normalized_reverse
    (inner : signature.Universal sort matrixOrder)
    (outer : signature.Universal sort (bindOrder matrixOrder sort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder sort) sort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder sort) sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    ⊢ᵣ implication negation disjunction
      (star_11_2_right inner outer body)
      (star_11_2_left inner outer body) := by
  have line1 := star_11_07_normalized inner outer negation disjunction
    body.swapHeads
  have line2 : body.swapHeads.swapHeads = body :=
    Formula.swapHeads_involutive body
  have line3 := congrArg (fun nextBody => star_11_01 inner outer nextBody) line2
  exact Derivation.castAssertion
    (congrArg (implication negation disjunction
      (star_11_2_right inner outer body)) line3).symm line1

def star_11_2_reading
    (inner : signature.Universal sort matrixOrder)
    (outer : signature.Universal sort (bindOrder matrixOrder sort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder sort) sort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder sort) sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    Star11Reading signature real where
  printed := "⊢ : (x, y).φ(x, y) .≡ .(y, x).φ(x, y)"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_2_left inner outer body)
    (star_11_2_right inner outer body))
  scopeReading := "The two universal closures are built independently from ✱11·01; the second closes the de Bruijn-transposed matrix."

/-- ✱11·2.  Lines (3) and (4) are the two orientations of primitive
✱11·07; ✱4·01 joins them into the printed equivalence.
`demonstration_provenance: follows-printed`. -/
theorem star_11_2
    (inner : signature.Universal sort matrixOrder)
    (outer : signature.Universal sort (bindOrder matrixOrder sort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder sort) sort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder sort) sort))
    (body : Formula signature real [sort, sort] matrixOrder) :
    Derivation (star_11_2_reading inner outer negation disjunction body).parsed := by
  have line3 := star_11_07_normalized inner outer negation disjunction body
  have line4 := star_11_07_normalized_reverse inner outer negation disjunction body
  have line5 := conjoin negation disjunction _ _ line3 line4
  exact line5

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
    Star11Reading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : ⊃ :\n(x, y).φ(x, y) .⊃ .(x, y).ψ(x, y)"
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
    Derivation (.assertion (Formula.always₂Saturated inner outer
      (star_10_27_body inner outer negation disjunction phi psi))) := by
  have line1 := star_10_27_instance inner outer negation disjunction phi psi
  exact line1

def star_11_33_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Star11Reading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : ⊃ :\n(x, y).φ(x, y) .≡ .(x, y).ψ(x, y)"
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
    Derivation (.assertion (Formula.always₂Saturated inner outer
      (star_10_271_body inner outer negation disjunction phi psi))) := by
  have line1 := star_10_271_instance inner outer negation disjunction phi psi
  exact line1

private def star_11_31_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (sameConjunction negation disjunction phi psi)

/- ✱11·31 is intentionally absent: its two printed members were both
encoded as `star_11_31_normalForm`, turning the theorem into reflexivity. -/

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
      (bindOrder baseOrder sort)) : Star11Reading signature real where
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
    Derivation (.assertion (Formula.always₂Saturated inner outer
      (star_11_37_body inner outer negation disjunction phi psi chi))) := by
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

private def star_11_371_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  let first := Formula.always₂Saturated inner outer
    (star_11_4_equivalenceMatrix negation disjunction phi psi)
  let second := Formula.always₂Saturated inner outer
    (star_11_4_equivalenceMatrix negation disjunction psi chi)
  implication negation disjunction
    (sameConjunction negation disjunction
      (Formula.weakenApparent₂ (sort := sort) first)
      (Formula.weakenApparent₂ (sort := sort) second))
    (star_11_4_equivalenceMatrix negation disjunction phi chi)

private theorem star_11_31_star_11_11_star_11_33_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_371_body inner outer negation disjunction phi psi chi) := by
  apply star_11_11_saturated inner outer
    (star_11_371_body inner outer negation disjunction phi psi chi)
  intro left right
  let firstMatrix := star_11_4_equivalenceMatrix negation disjunction phi psi
  let secondMatrix := star_11_4_equivalenceMatrix negation disjunction psi chi
  let first := Formula.always₂Saturated inner outer firstMatrix
  let second := Formula.always₂Saturated inner outer secondMatrix
  let hypothesis := conjunction negation disjunction first second
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let chiInstance := chi.instantiate₂ left right
  let firstInstance := star_4_01 negation disjunction phiInstance psiInstance
  let secondInstance := star_4_01 negation disjunction psiInstance chiInstance
  let conclusion := star_4_01 negation disjunction phiInstance chiInstance
  have line1Raw := star_11_1_saturated inner outer negation disjunction
    firstMatrix left right
  have firstEq : firstMatrix.instantiate₂ left right = firstInstance := by
    dsimp [firstMatrix, firstInstance, star_11_4_equivalenceMatrix,
      star_4_01]
    rw [Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      sameConjunction_eq_conjunction]
  have line1a := Derivation.castAssertion
    (congrArg (implication negation disjunction first) firstEq.symm) line1Raw
  have line1 := compose negation disjunction hypothesis first firstInstance
    (star_3_26 negation disjunction first second) line1a
  have line2Raw := star_11_1_saturated inner outer negation disjunction
    secondMatrix left right
  have secondEq : secondMatrix.instantiate₂ left right = secondInstance := by
    dsimp [secondMatrix, secondInstance, star_11_4_equivalenceMatrix,
      star_4_01]
    rw [Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      sameConjunction_eq_conjunction]
  have line2a := Derivation.castAssertion
    (congrArg (implication negation disjunction second) secondEq.symm) line2Raw
  have line2 := compose negation disjunction hypothesis second secondInstance
    (star_3_27 negation disjunction first second) line2a
  have line3a := conjoin negation disjunction
    (implication negation disjunction hypothesis firstInstance)
    (implication negation disjunction hypothesis secondInstance) line1 line2
  have line3b := star_3_43 negation disjunction hypothesis
    firstInstance secondInstance
  have line3 := detach negation disjunction _ _ line3a line3b
  have line4 := star_4_22 negation disjunction
    phiInstance psiInstance chiInstance
  have line5 := compose negation disjunction hypothesis
    (conjunction negation disjunction firstInstance secondInstance)
    conclusion line3 line4
  have bodyEq :
      (star_11_371_body inner outer negation disjunction phi psi chi).instantiate₂
          left right = implication negation disjunction hypothesis conclusion := by
    dsimp [star_11_371_body, firstMatrix, secondMatrix, first, second,
      hypothesis, phiInstance, psiInstance, chiInstance, conclusion,
      star_11_4_equivalenceMatrix, star_4_01]
    rw [Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction]
  exact Derivation.castAssertion bodyEq line5

def star_11_371_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : Star11Reading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : .(x, y) :\nψ(x, y) .≡ .χ(x, y) :. ⊃ : (x, y) : φ(x, y) .≡ .χ(x, y)\n[✱11·31·11·33]"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_11_371_body inner outer negation disjunction phi psi chi))

/-- ✱11·371.  The two pointwise equivalences are specialized, composed by
✱4·22, and generalized exactly in the order cited by PM.
`demonstration_provenance: follows-printed`. -/
theorem star_11_371
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation (star_11_371_reading inner outer negation disjunction
      phi psi chi).parsed := by
  have line1 := star_11_31_star_11_11_star_11_33_instance
    inner outer negation disjunction phi psi chi
  exact line1

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
      (bindOrder baseOrder sort)) : Star11Reading signature real where
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
    Derivation (.assertion (Formula.always₂Saturated inner outer
      (star_11_4_body inner outer negation disjunction phi psi chi theta))) := by
  have line1 := star_11_31_star_4_38_star_11_11_star_11_32_instance
    inner outer negation disjunction phi psi chi theta
  exact line1

private def star_11_401_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  let hypothesis := Formula.always₂Saturated inner outer
    (star_11_4_equivalenceMatrix negation disjunction phi psi)
  implication negation disjunction
    (Formula.weakenApparent₂ (sort := sort) hypothesis)
    (star_11_4_equivalenceMatrix negation disjunction
      (sameConjunction negation disjunction phi chi)
      (sameConjunction negation disjunction psi chi))

private theorem star_11_4_chi_id_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_401_body inner outer negation disjunction phi psi chi) := by
  apply star_11_11_saturated inner outer
    (star_11_401_body inner outer negation disjunction phi psi chi)
  intro left right
  let equivalenceMatrix :=
    star_11_4_equivalenceMatrix negation disjunction phi psi
  let hypothesis := Formula.always₂Saturated inner outer equivalenceMatrix
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let chiInstance := chi.instantiate₂ left right
  let pointEquivalence := star_4_01 negation disjunction
    phiInstance psiInstance
  let identityEquivalence := star_4_01 negation disjunction
    chiInstance chiInstance
  let resultEquivalence := star_4_01 negation disjunction
    (conjunction negation disjunction phiInstance chiInstance)
    (conjunction negation disjunction psiInstance chiInstance)
  have line1Raw := star_11_1_saturated inner outer negation disjunction
    equivalenceMatrix left right
  have pointEq : equivalenceMatrix.instantiate₂ left right =
      pointEquivalence := by
    dsimp [equivalenceMatrix, pointEquivalence,
      star_11_4_equivalenceMatrix, star_4_01]
    rw [Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      sameConjunction_eq_conjunction]
  have line1 := Derivation.castAssertion
    (congrArg (implication negation disjunction hypothesis)
      pointEq.symm) line1Raw
  have identity := star_4_2 negation disjunction chiInstance
  have line2 := detach negation disjunction identityEquivalence
    (implication negation disjunction hypothesis identityEquivalence)
    identity (star_2_02 negation disjunction hypothesis identityEquivalence)
  have line3a := conjoin negation disjunction
    (implication negation disjunction hypothesis pointEquivalence)
    (implication negation disjunction hypothesis identityEquivalence)
    line1 line2
  have line3b := star_3_43 negation disjunction hypothesis
    pointEquivalence identityEquivalence
  have line3 := detach negation disjunction _ _ line3a line3b
  have line4 := star_4_38 negation disjunction
    phiInstance chiInstance psiInstance chiInstance
  have line5 := compose negation disjunction hypothesis
    (conjunction negation disjunction pointEquivalence identityEquivalence)
    resultEquivalence line3 line4
  have bodyEq :
      (star_11_401_body inner outer negation disjunction phi psi chi).instantiate₂
          left right =
        implication negation disjunction hypothesis resultEquivalence := by
    dsimp [star_11_401_body, equivalenceMatrix, hypothesis,
      phiInstance, psiInstance, chiInstance, resultEquivalence,
      star_11_4_equivalenceMatrix, star_4_01]
    rw [Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction]
  exact Derivation.castAssertion bodyEq line5

def star_11_401_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : Star11Reading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : ⊃ :\n(x, y) : φ(x, y).χ(x, y) .≡ .ψ(x, y).χ(x, y)  [✱11·4 χ/θ .Id]"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_11_401_body inner outer negation disjunction phi psi chi))

/-- ✱11·401.  The instance `χ/θ` of ✱11·4 is combined with the printed
`Id` instance for `χ` before the two variables are generalized.
`demonstration_provenance: follows-printed`. -/
theorem star_11_401
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation (star_11_401_reading inner outer negation disjunction
      phi psi chi).parsed := by
  have line1 := star_11_4_chi_id_instance inner outer negation disjunction
    phi psi chi
  exact line1

private def star_11_41_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.sometimes₂Saturated inner outer negation
    (sameDisjunction disjunction phi psi)

/- ✱11·41 is intentionally absent: existential distribution over
disjunction is a theorem, not a definitional identification of its sides. -/

private def star_11_42_projectionBody
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (selected phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  implication negation disjunction
    (Formula.weakenApparent₂ (sort := sort)
      (Formula.always₂Saturated inner outer (Formula.neg negation selected)))
    (Formula.neg negation (sameConjunction negation disjunction phi psi))

private def star_11_42_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  conjunction negation disjunction
    (Formula.always₂Saturated inner outer
      (star_11_42_projectionBody inner outer negation disjunction phi phi psi))
    (Formula.always₂Saturated inner outer
      (star_11_42_projectionBody inner outer negation disjunction psi phi psi))

namespace Star10For11

/-- The binary saturated instance of printed ✱10·5 used at ✱11·42. -/
theorem star_10_5
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ star_11_42_normalForm inner outer negation disjunction phi psi := by
  have leftProjection : ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_42_projectionBody inner outer negation disjunction phi phi psi) := by
    apply star_11_11_saturated inner outer
      (star_11_42_projectionBody inner outer negation disjunction phi phi psi)
    intro left right
    let hypothesis := Formula.always₂Saturated inner outer
      (Formula.neg negation phi)
    let phiInstance := phi.instantiate₂ left right
    let psiInstance := psi.instantiate₂ left right
    let product := conjunction negation disjunction phiInstance psiInstance
    have specializationRaw := star_11_1_saturated inner outer negation disjunction
      (Formula.neg negation phi) left right
    have specializationEq :
        (Formula.neg negation phi).instantiate₂ left right =
          Formula.neg negation phiInstance := by
      exact Formula.neg_instantiate₂ negation phi left right
    have specialization := Derivation.castAssertion
      (congrArg (implication negation disjunction hypothesis)
        specializationEq.symm) specializationRaw
    have projection := star_3_26 negation disjunction phiInstance psiInstance
    have transposition := detach negation disjunction
      (implication negation disjunction product phiInstance)
      (implication negation disjunction
        (Formula.neg negation phiInstance) (Formula.neg negation product))
      projection (star_2_16 negation disjunction product phiInstance)
    have line1 := compose negation disjunction hypothesis
      (Formula.neg negation phiInstance) (Formula.neg negation product)
      specialization transposition
    have bodyEq :
        (star_11_42_projectionBody inner outer negation disjunction phi phi psi).instantiate₂
            left right =
          implication negation disjunction hypothesis
            (Formula.neg negation product) := by
      dsimp [star_11_42_projectionBody, hypothesis, phiInstance, psiInstance,
        product]
      rw [Formula.implication_instantiate₂,
        Formula.weakenApparent₂_instantiate₂,
        Formula.neg_instantiate₂,
        Formula.sameConjunction_instantiate₂,
        sameConjunction_eq_conjunction]
    exact Derivation.castAssertion bodyEq line1
  have rightProjection : ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_42_projectionBody inner outer negation disjunction psi phi psi) := by
    apply star_11_11_saturated inner outer
      (star_11_42_projectionBody inner outer negation disjunction psi phi psi)
    intro left right
    let hypothesis := Formula.always₂Saturated inner outer
      (Formula.neg negation psi)
    let phiInstance := phi.instantiate₂ left right
    let psiInstance := psi.instantiate₂ left right
    let product := conjunction negation disjunction phiInstance psiInstance
    have specializationRaw := star_11_1_saturated inner outer negation disjunction
      (Formula.neg negation psi) left right
    have specializationEq :
        (Formula.neg negation psi).instantiate₂ left right =
          Formula.neg negation psiInstance := by
      exact Formula.neg_instantiate₂ negation psi left right
    have specialization := Derivation.castAssertion
      (congrArg (implication negation disjunction hypothesis)
        specializationEq.symm) specializationRaw
    have projection := star_3_27 negation disjunction phiInstance psiInstance
    have transposition := detach negation disjunction
      (implication negation disjunction product psiInstance)
      (implication negation disjunction
        (Formula.neg negation psiInstance) (Formula.neg negation product))
      projection (star_2_16 negation disjunction product psiInstance)
    have line1 := compose negation disjunction hypothesis
      (Formula.neg negation psiInstance) (Formula.neg negation product)
      specialization transposition
    have bodyEq :
        (star_11_42_projectionBody inner outer negation disjunction psi phi psi).instantiate₂
            left right =
          implication negation disjunction hypothesis
            (Formula.neg negation product) := by
      dsimp [star_11_42_projectionBody, hypothesis, phiInstance, psiInstance,
        product]
      rw [Formula.implication_instantiate₂,
        Formula.weakenApparent₂_instantiate₂,
        Formula.neg_instantiate₂,
        Formula.sameConjunction_instantiate₂,
        sameConjunction_eq_conjunction]
    exact Derivation.castAssertion bodyEq line1
  exact conjoin negation disjunction _ _ leftProjection rightProjection

end Star10For11

def star_11_42_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : Star11Reading signature real where
  printed := "⊢ : .(∃x, y).φ(x, y).ψ(x, y) .⊃ : (∃x, y).φ(x, y) : (∃x, y).ψ(x, y)"
  parsed := .assertion
    (star_11_42_normalForm inner outer negation disjunction phi psi)

/-! ✱11·42 est l'instance binaire de ✱10·5 citée par PM. Après
dépliage de l'existentiel, transposition et normalisation des portées,
la conclusion est la paire des deux projections universelles ci-dessus.
`demonstration_provenance: follows-printed`. -/
theorem star_11_42
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation (.assertion
      (star_11_42_normalForm inner outer negation disjunction phi psi)) := by
  have line1 := Star10For11.star_10_5
    inner outer negation disjunction phi psi
  exact line1

private theorem star11_stableOrder (sort : RSort) :
    bindOrder (Nat.succ sort.height) sort = Nat.succ sort.height := by
  unfold bindOrder
  exact natMaxSelf _

private def Formula.star11AlwaysStable
    (universal : signature.Universal sort (Nat.succ sort.height))
    (body : Formula signature real (sort :: apparent)
      (Nat.succ sort.height)) :
    Formula signature real apparent (Nat.succ sort.height) :=
  Eq.mp (congrArg (Formula signature real apparent) (star11_stableOrder sort))
    (.always universal body)

private def Formula.star11SometimesStable
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (body : Formula signature real (sort :: apparent)
      (Nat.succ sort.height)) :
    Formula signature real apparent (Nat.succ sort.height) :=
  .neg negation (.star11AlwaysStable universal (.neg negation body))

private def star11StableExistentialVocabulary
    (existential : signature.Existential sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height)) :
    ExistentialVocabulary signature sort (Nat.succ sort.height) where
  printed := existential
  matrixNegation := negation
  universal := universal
  outerNegation := Eq.mp
    (congrArg signature.Negation (star11_stableOrder sort).symm) negation

private def Formula.star11SometimesStableRaw
    (existential : signature.Existential sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (body : Formula signature real (sort :: apparent)
      (Nat.succ sort.height)) :
    Formula signature real apparent (Nat.succ sort.height) :=
  Eq.mp (congrArg (Formula signature real apparent) (star11_stableOrder sort))
    (.sometimes
      (star11StableExistentialVocabulary existential universal negation) body)

private theorem star11_negation_normalizeOrder
    (equality : sourceOrder = targetOrder)
    (negation : signature.Negation targetOrder)
    (body : Formula signature real apparent sourceOrder) :
    Eq.mp (congrArg (Formula signature real apparent) equality)
      (.neg (Eq.mp (congrArg signature.Negation equality.symm) negation) body) =
      .neg negation
        (Eq.mp (congrArg (Formula signature real apparent) equality) body) := by
  cases equality
  rfl

private theorem Formula.star11SometimesStableRaw_normalize
    (existential : signature.Existential sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (body : Formula signature real (sort :: apparent)
      (Nat.succ sort.height)) :
    Formula.star11SometimesStableRaw existential universal negation body =
      Formula.star11SometimesStable universal negation body := by
  unfold Formula.star11SometimesStableRaw star11StableExistentialVocabulary
    Formula.sometimes Formula.star11SometimesStable
    Formula.star11AlwaysStable
  exact star11_negation_normalizeOrder (star11_stableOrder sort) negation
    (.always universal (.neg negation body))

private def star11FixSecondSubstitution :
    Substitution signature (sort :: real) [sort, sort] [sort]
  | _, .zero => .apparent .zero
  | _, .succ .zero => .real .zero

private def Formula.star11FixSecond
    (body : Formula signature real [sort, sort] order) :
    Formula signature (sort :: real) [sort] order :=
  body.weakenReal.substitute star11FixSecondSubstitution

private theorem Formula.star11CastCongr
    (left right : Formula signature real apparent sourceOrder)
    (leftOrder rightOrder : sourceOrder = targetOrder)
    (equality : left = right) :
    Eq.mp (congrArg (Formula signature real apparent) leftOrder) left =
      Eq.mp (congrArg (Formula signature real apparent) rightOrder) right := by
  cases leftOrder
  cases rightOrder
  exact equality

private theorem Formula.star11AlwaysStable_weakenReal_instantiate
    (universal : signature.Universal sort (Nat.succ sort.height))
    (body : Formula signature real [sort, sort] (Nat.succ sort.height)) :
    (Formula.star11AlwaysStable universal body).weakenReal.instantiate
        (.real .zero) =
      Formula.star11AlwaysStable universal (Formula.star11FixSecond body) := by
  unfold Formula.star11AlwaysStable Formula.star11FixSecond
    Formula.instantiate
  rw [Formula.weakenReal_cast (star11_stableOrder sort),
    Formula.substitute_cast (star11_stableOrder sort)]
  refine Formula.star11CastCongr _ _ (star11_stableOrder sort)
    (star11_stableOrder sort) ?_
  change Formula.always universal
      (body.weakenReal.substitute
        (liftSubstitution (instantiateSubstitution (.real .zero)))) =
    Formula.always universal
      (body.weakenReal.substitute
        star11FixSecondSubstitution)
  apply congrArg (Formula.always universal)
  apply Formula.substitute_of_pointwise
  intro targetSort v
  cases v with
  | zero => rfl
  | succ v =>
      cases v with
      | zero => rfl
      | succ v => cases v

private theorem Formula.star11SometimesStable_weakenReal_instantiate
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (body : Formula signature real [sort, sort] (Nat.succ sort.height)) :
    (Formula.star11SometimesStable universal negation body).weakenReal.instantiate
        (.real .zero) =
      Formula.star11SometimesStable universal negation
        (Formula.star11FixSecond body) := by
  unfold Formula.star11SometimesStable
  change Formula.neg negation
      ((Formula.star11AlwaysStable universal
        (.neg negation body)).weakenReal.instantiate (.real .zero)) = _
  rw [Formula.star11AlwaysStable_weakenReal_instantiate]
  rfl

private theorem Formula.star11FixSecond_implication
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [sort, sort] order) :
    Formula.star11FixSecond (implication negation disjunction phi psi) =
      implication negation disjunction
        (Formula.star11FixSecond phi) (Formula.star11FixSecond psi) := by
  unfold Formula.star11FixSecond
  rw [implication_weakenReal, implication_substitute]

private theorem Formula.star11Implication_weakenReal_instantiate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [sort] order) :
    (implication negation disjunction phi psi).weakenReal.instantiate
        (.real (.zero : Var (sort :: real) sort)) =
      implication negation disjunction
        (phi.weakenReal.instantiate (.real .zero))
        (psi.weakenReal.instantiate (.real .zero)) := by
  rw [implication_weakenReal]
  unfold Formula.instantiate
  rw [implication_substitute]

private theorem Formula.closed_substitute
    (formula : Formula signature real [] order)
    (sigma : Substitution signature real [] target)
    (rho : Renaming [] target) :
    formula.substitute sigma =
      formula.rename rho := by
  let identity : Substitution signature real target target :=
    fun v => .apparent v
  have line1 := Formula.rename_substitute_of_pointwise
    rho identity sigma
    (fun v => nomatch v) formula
  have line2 :
      (formula.rename rho).substitute identity = formula.rename rho := by
    exact Formula.substitute_eq_self
      (formula.rename rho) (fun v => rfl)
  rw [line2] at line1
  exact line1.symm

private theorem star_10_34_left_normalize
    (existential : signature.Existential sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    star_10_34_left existential universal negation disjunction phi p =
      Formula.star11SometimesStable universal negation
        (implication negation disjunction phi
          (p.rename (fun v => .succ v))) := by
  unfold star_10_34_left Formula.star11SometimesStable
    Formula.star11AlwaysStable
  change Formula.star11SometimesStableRaw existential universal negation
      (implication negation disjunction phi
        (p.rename (fun v => .succ v))) = _
  rw [Formula.star11SometimesStableRaw_normalize]
  rfl

private theorem star_10_34_right_normalize
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    star_10_34_right universal negation disjunction phi p =
      implication negation disjunction
        (Formula.star11AlwaysStable universal phi) p := by
  rfl

private theorem star11_equivalence_weakenReal
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

private theorem star11_equivalence_substitute
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

private theorem star11_stableGeneralize
    (universal : signature.Universal sort (Nat.succ sort.height))
    (body : Formula signature real [sort] (Nat.succ sort.height))
    (line1 : Derivation (.assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (sort :: real) sort))))) :
    Derivation (.assertion (Formula.star11AlwaysStable universal body)) := by
  have line2 := star_10_11 universal body line1
  unfold Formula.star11AlwaysStable
  exact castAssertionOrder (star11_stableOrder sort) (.always universal body) line2

private theorem star11_liftStableUniversalEquivalence
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi psi : Formula signature real [sort] (Nat.succ sort.height))
    (line1 : Derivation (.assertion (star_4_01 negation disjunction
      (phi.weakenReal.instantiate (.real .zero))
      (psi.weakenReal.instantiate (.real .zero))))) :
    Derivation (.assertion (star_4_01 negation disjunction
      (Formula.star11AlwaysStable universal phi)
      (Formula.star11AlwaysStable universal psi))) := by
  have line2 : Derivation (.assertion
      ((equivalence negation disjunction phi psi).weakenReal.instantiate
        (.real (.zero : Var (sort :: real) sort)))) := by
    rw [star11_equivalence_weakenReal, Formula.instantiate,
      star11_equivalence_substitute]
    exact line1
  have line3 := star11_stableGeneralize universal
    (equivalence negation disjunction phi psi) line2
  have line4 := star_10_271 (baseOrder := 0) universal negation disjunction
    phi psi
  unfold star_10_271_reading star_10_271_left star_10_271_right at line4
  exact detach negation disjunction _ _ line3 line4

private theorem star11_liftStableExistentialEquivalence
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi psi : Formula signature real [sort] (Nat.succ sort.height))
    (line1 : Derivation (.assertion (star_4_01 negation disjunction
      (phi.weakenReal.instantiate (.real .zero))
      (psi.weakenReal.instantiate (.real .zero))))) :
    Derivation (.assertion (star_4_01 negation disjunction
      (Formula.star11SometimesStable universal negation phi)
      (Formula.star11SometimesStable universal negation psi))) := by
  let phiAtValue := phi.weakenReal.instantiate
    (.real (.zero : Var (sort :: real) sort))
  let psiAtValue := psi.weakenReal.instantiate
    (.real (.zero : Var (sort :: real) sort))
  let pointwise := star_4_01 negation disjunction phiAtValue psiAtValue
  let negatedPointwise := star_4_01 negation disjunction
    (.neg negation phiAtValue) (.neg negation psiAtValue)
  have line2a := star_4_11 (negation := negation) (disjunction := disjunction)
    phiAtValue psiAtValue
  have line2b := detach negation disjunction _ _ line2a
    (star_3_26 negation disjunction
      (implication negation disjunction pointwise negatedPointwise)
      (implication negation disjunction negatedPointwise pointwise))
  have line2 := detach negation disjunction pointwise negatedPointwise line1 line2b
  have line3 := star11_liftStableUniversalEquivalence universal negation
    disjunction (.neg negation phi) (.neg negation psi) line2
  let universalNegatedPhi := Formula.star11AlwaysStable universal
    (.neg negation phi)
  let universalNegatedPsi := Formula.star11AlwaysStable universal
    (.neg negation psi)
  let lifted := star_4_01 negation disjunction
    universalNegatedPhi universalNegatedPsi
  let negatedLifted := star_4_01 negation disjunction
    (.neg negation universalNegatedPhi) (.neg negation universalNegatedPsi)
  have line4a := star_4_11 (negation := negation) (disjunction := disjunction)
    universalNegatedPhi universalNegatedPsi
  have line4b := detach negation disjunction _ _ line4a
    (star_3_26 negation disjunction
      (implication negation disjunction lifted negatedLifted)
      (implication negation disjunction negatedLifted lifted))
  have line4 := detach negation disjunction lifted negatedLifted line3 line4b
  unfold Formula.star11SometimesStable
  exact line4

def star_11_43_left
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Formula.star11SometimesStable outerUniversal negation
    (Formula.star11SometimesStable innerUniversal negation
      (implication negation disjunction phi
        (p.rename (emptyRenaming (target := [sort, sort])))))

private def star_11_43_middle
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Formula.star11SometimesStable outerUniversal negation
    (implication negation disjunction
      (Formula.star11AlwaysStable innerUniversal phi)
      (p.rename (fun v => .succ v)))

/-- The printed right member `(x,y).φ(x,y) ⊃ p`, independently built from
the double universal closure. -/
def star_11_43_right
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  implication negation disjunction
    (Formula.star11AlwaysStable outerUniversal
      (Formula.star11AlwaysStable innerUniversal phi)) p

def star_11_43_reading
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Star11Reading signature real where
  printed := "⊢ : .(∃x, y) : φ(x, y) .⊃ .p : ≡ :\n(x, y).φ(x, y) .⊃ .p"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_43_left innerUniversal outerUniversal negation disjunction phi p)
    (star_11_43_right innerUniversal outerUniversal negation disjunction phi p))
  scopeReading := "The left member is the independently nested existential closure; the right member is an implication whose antecedent is the independently nested universal closure."

/-- ✱11·43.  `line1` is the inner ✱10·34 instance, `line2` is its
printed ✱10·281 lift, and `line3` is the outer ✱10·34 instance.
`demonstration_provenance: follows-printed`. -/
theorem star_11_43
    (innerExistential outerExistential :
      signature.Existential sort (Nat.succ sort.height))
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (witness : Term signature real [] sort) :
    Derivation (star_11_43_reading innerUniversal outerUniversal negation
      disjunction phi p).parsed := by
  let innerLeft := Formula.star11SometimesStable innerUniversal negation
    (implication negation disjunction phi
      (p.rename (emptyRenaming (target := [sort, sort]))))
  let innerRight := implication negation disjunction
    (Formula.star11AlwaysStable innerUniversal phi)
    (p.rename (fun v => .succ v))
  have line1a := star_10_34 innerExistential innerUniversal negation disjunction
    (Formula.star11FixSecond phi) p.weakenReal
    (.real (.zero : Var (sort :: real) sort))
  have line1b :
      Formula.star11FixSecond
        (p.rename (emptyRenaming (target := [sort, sort]))) =
      p.weakenReal.rename (fun v => .succ v) := by
    unfold Formula.star11FixSecond
    rw [Formula.weakenReal_rename, Formula.rename_substitute]
    exact Formula.closed_substitute p.weakenReal _ (fun v => .succ v)
  have line1 : Derivation (.assertion (star_4_01 negation disjunction
      (innerLeft.weakenReal.instantiate (.real .zero))
      (innerRight.weakenReal.instantiate (.real .zero)))) := by
    unfold innerLeft innerRight
    rw [Formula.star11SometimesStable_weakenReal_instantiate,
      Formula.star11FixSecond_implication, line1b,
      Formula.star11Implication_weakenReal_instantiate,
      Formula.star11AlwaysStable_weakenReal_instantiate,
      Formula.closed_weakenReal_instantiate]
    unfold star_10_34_reading at line1a
    rw [star_10_34_left_normalize, star_10_34_right_normalize] at line1a
    exact line1a
  have line2 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_43_left innerUniversal outerUniversal negation disjunction phi p)
      (star_11_43_middle innerUniversal outerUniversal negation disjunction
        phi p))) := by
    unfold star_11_43_left star_11_43_middle
    exact star11_liftStableExistentialEquivalence outerUniversal
      negation disjunction innerLeft innerRight line1
  have line3 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_43_middle innerUniversal outerUniversal negation disjunction
        phi p)
      (star_11_43_right innerUniversal outerUniversal negation disjunction
        phi p))) := by
    have line3a := star_10_34 outerExistential outerUniversal negation
      disjunction (Formula.star11AlwaysStable innerUniversal phi) p witness
    unfold star_10_34_reading at line3a
    rw [star_10_34_left_normalize, star_10_34_right_normalize] at line3a
    unfold star_11_43_middle star_11_43_right
    exact line3a
  have line4 := conjoin negation disjunction _ _ line2 line3
  exact detach negation disjunction _ _ line4
    (star_4_22 negation disjunction
      (star_11_43_left innerUniversal outerUniversal negation disjunction phi p)
      (star_11_43_middle innerUniversal outerUniversal negation disjunction phi p)
      (star_11_43_right innerUniversal outerUniversal negation disjunction phi p))

private theorem Formula.star11FixSecond_sameDisjunction
    (disjunction : signature.Disjunction order)
    (phi psi : Formula signature real [sort, sort] order) :
    Formula.star11FixSecond (sameDisjunction disjunction phi psi) =
      sameDisjunction disjunction
        (Formula.star11FixSecond phi) (Formula.star11FixSecond psi) := by
  unfold Formula.star11FixSecond
  rw [sameDisjunction_weakenReal, sameDisjunction_substitute]

private theorem star11_disjunction_weakenReal_instantiate_closedRight
    (disjunction : signature.Disjunction order)
    (phi : Formula signature real [sort] order)
    (p : Formula signature real [] order)
    (value : Term signature (sort :: real) [] sort) :
    (sameDisjunction disjunction phi
      (p.rename (fun v => .succ v))).weakenReal.instantiate value =
      sameDisjunction disjunction
        (phi.weakenReal.instantiate value) p.weakenReal := by
  rw [sameDisjunction_weakenReal]
  unfold Formula.instantiate
  rw [sameDisjunction_substitute,
    Formula.closed_weakenReal_instantiateSubstitution]

private theorem star11_disjunction_weakenReal_instantiate_closedLeft
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order)
    (phi : Formula signature real [sort] order)
    (value : Term signature (sort :: real) [] sort) :
    (sameDisjunction disjunction (p.rename (fun v => .succ v))
      phi).weakenReal.instantiate value =
      sameDisjunction disjunction p.weakenReal
        (phi.weakenReal.instantiate value) := by
  rw [sameDisjunction_weakenReal]
  unfold Formula.instantiate
  rw [sameDisjunction_substitute,
    Formula.closed_weakenReal_instantiateSubstitution]

private def star11CastImplicationDisjunctionOrder
    (equality : sourceOrder = targetOrder)
    (left : Formula signature real [] leftOrder)
    (right result : Formula signature real [] sourceOrder)
    (reading : ImplicationDisjunction signature real left right result) :
    ImplicationDisjunction signature real left
      (Eq.mp (congrArg (Formula signature real []) equality) right)
      (Eq.mp (congrArg (Formula signature real []) equality) result) := by
  cases equality
  exact reading

private def star11StableScopeDisjunction
    (universal : signature.Universal sort (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (fixed : Formula signature real [] (Nat.succ sort.height))
    (body : Formula signature real [sort] (Nat.succ sort.height)) :
    ImplicationDisjunction signature real fixed
      (Formula.star11AlwaysStable universal body)
      (Formula.star11AlwaysStable universal
        (sameDisjunction disjunction
          (fixed.rename (fun v => .succ v)) body)) := by
  let result := sameDisjunction disjunction
    (fixed.rename (fun v => .succ v)) body
  have line1 : ImplicationDisjunction signature real fixed
      (.always universal body) (.always universal result) := by
    apply ImplicationDisjunction.star_9_04 universal universal
    exact ImplicationDisjunction.star_1_01_same disjunction
      (fixed.rename (fun v => .succ v)) body
  exact star11CastImplicationDisjunctionOrder
    (star11_stableOrder sort) fixed (.always universal body)
    (.always universal result) line1

private theorem star11_convertImplicationRepresentation
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q source target : Formula signature real [] order)
    (sourceDefinition : ImplicationDisjunction signature real
      (.neg negation p) q source)
    (targetDefinition : ImplicationDisjunction signature real
      (.neg negation p) q target) :
    Derivation (.assertion (implication negation disjunction source target)) := by
  let identity := implication negation disjunction q q
  let reading := star2_05ReadingOfSameOrderComponents
    negation disjunction p q q (.neg negation p) (.neg negation q)
    source identity target
    (ImplicationNegation.star_1_01 negation p)
    (ImplicationNegation.star_1_01 negation q)
    sourceDefinition
    (ImplicationDisjunction.star_1_01_same disjunction
      (.neg negation q) q)
    targetDefinition
  have line1 := star_2_05 negation disjunction p q q
    (reading := reading)
  exact detach negation disjunction identity
    (implication negation disjunction source target)
    (star_2_08 negation disjunction q) line1

private theorem star11_equivalentImplicationRepresentations
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q source target : Formula signature real [] order)
    (sourceDefinition : ImplicationDisjunction signature real
      (.neg negation p) q source)
    (targetDefinition : ImplicationDisjunction signature real
      (.neg negation p) q target) :
    Derivation (.assertion (star_4_01 negation disjunction source target)) := by
  have line1 := star11_convertImplicationRepresentation negation disjunction
    p q source target sourceDefinition targetDefinition
  have line2 := star11_convertImplicationRepresentation negation disjunction
    p q target source targetDefinition sourceDefinition
  exact conjoin negation disjunction _ _ line1 line2

private theorem star11_chainEquivalence
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left middle right : Formula signature real [] order)
    (line1 : Derivation (.assertion
      (star_4_01 negation disjunction left middle)))
    (line2 : Derivation (.assertion
      (star_4_01 negation disjunction middle right))) :
    Derivation (.assertion (star_4_01 negation disjunction left right)) := by
  have line3 := conjoin negation disjunction _ _ line1 line2
  exact detach negation disjunction _ _ line3
    (star_4_22 negation disjunction left middle right)

/-- The stable-order instance of printed ✱10·2.  The ✱9·04 member is
kept as a scope tree and converted to the external disjunction only through
its `ImplicationDisjunction` certificate. -/
private theorem star11_stableUniversalDisjunction
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Derivation (.assertion (star_4_01 negation disjunction
      (Formula.star11AlwaysStable universal
        (sameDisjunction disjunction phi
          (p.rename (fun v => .succ v))))
      (sameDisjunction disjunction
        (Formula.star11AlwaysStable universal phi) p))) := by
  let value : Term signature (sort :: real) [] sort := .real .zero
  let left := Formula.star11AlwaysStable universal
    (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
  let permuted := Formula.star11AlwaysStable universal
    (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
  let doubled := Formula.star11AlwaysStable universal
    (sameDisjunction disjunction
      ((Formula.neg negation (Formula.neg negation p)).rename
        (fun v => .succ v)) phi)
  let universalPhi := Formula.star11AlwaysStable universal phi
  let implicationForm := implication negation disjunction
    (Formula.neg negation p) universalPhi
  let fixedFirst := sameDisjunction disjunction p universalPhi
  let right := sameDisjunction disjunction universalPhi p
  have line1a : Derivation (.assertion (star_4_01 negation disjunction
      ((sameDisjunction disjunction phi
        (p.rename (fun v => .succ v))).weakenReal.instantiate value)
      ((sameDisjunction disjunction (p.rename (fun v => .succ v))
        phi).weakenReal.instantiate value))) := by
    rw [star11_disjunction_weakenReal_instantiate_closedRight,
      star11_disjunction_weakenReal_instantiate_closedLeft]
    exact star_4_31 negation disjunction
      (phi.weakenReal.instantiate value) p.weakenReal
  have line1 : Derivation (.assertion
      (star_4_01 negation disjunction left permuted)) := by
    unfold left permuted
    exact star11_liftStableUniversalEquivalence universal negation disjunction
      (sameDisjunction disjunction phi (p.rename (fun v => .succ v)))
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      line1a
  have line2a : Derivation (.assertion (star_4_01 negation disjunction
      ((sameDisjunction disjunction (p.rename (fun v => .succ v))
        phi).weakenReal.instantiate value)
      ((sameDisjunction disjunction
        ((Formula.neg negation (Formula.neg negation p)).rename
          (fun v => .succ v))
        phi).weakenReal.instantiate value))) := by
    rw [star11_disjunction_weakenReal_instantiate_closedLeft,
      star11_disjunction_weakenReal_instantiate_closedLeft]
    have line2b := star_4_13 negation disjunction
      (p.weakenReal (fresh := sort))
    have line2c := star_4_2 negation disjunction
      (phi.weakenReal.instantiate value)
    have line2d := conjoin negation disjunction _ _ line2b line2c
    exact detach negation disjunction _ _ line2d
      (star_4_39 negation disjunction (p.weakenReal (fresh := sort))
        (phi.weakenReal.instantiate value)
        (Formula.neg negation
          (Formula.neg negation (p.weakenReal (fresh := sort))))
        (phi.weakenReal.instantiate value))
  have line2 : Derivation (.assertion
      (star_4_01 negation disjunction permuted doubled)) := by
    unfold permuted doubled
    exact star11_liftStableUniversalEquivalence universal negation disjunction
      (sameDisjunction disjunction (p.rename (fun v => .succ v)) phi)
      (sameDisjunction disjunction
        ((Formula.neg negation (Formula.neg negation p)).rename
          (fun v => .succ v)) phi)
      line2a
  have line3 : Derivation (.assertion
      (star_4_01 negation disjunction doubled implicationForm)) := by
    let sourceDefinition := star11StableScopeDisjunction universal disjunction
      (Formula.neg negation (Formula.neg negation p)) phi
    let targetDefinition := ImplicationDisjunction.star_1_01_same disjunction
      (Formula.neg negation (Formula.neg negation p)) universalPhi
    unfold doubled implicationForm
    exact star11_equivalentImplicationRepresentations negation disjunction
      (Formula.neg negation p) universalPhi
      (Formula.star11AlwaysStable universal
        (sameDisjunction disjunction
          ((Formula.neg negation (Formula.neg negation p)).rename
            (fun v => .succ v)) phi))
      (implication negation disjunction (Formula.neg negation p) universalPhi)
      sourceDefinition targetDefinition
  have line4 : Derivation (.assertion
      (star_4_01 negation disjunction implicationForm fixedFirst)) := by
    unfold implicationForm fixedFirst
    exact star_4_64 negation disjunction p universalPhi
  have line5 : Derivation (.assertion
      (star_4_01 negation disjunction fixedFirst right)) := by
    unfold fixedFirst right
    exact star_4_31 negation disjunction p universalPhi
  exact star11_chainEquivalence negation disjunction left permuted right line1
    (star11_chainEquivalence negation disjunction permuted doubled right line2
      (star11_chainEquivalence negation disjunction doubled implicationForm
        right line3
        (star11_chainEquivalence negation disjunction implicationForm fixedFirst
          right line4 line5)))

def star_11_44_left
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Formula.star11AlwaysStable outerUniversal
    (Formula.star11AlwaysStable innerUniversal
      (sameDisjunction disjunction phi
        (p.rename (emptyRenaming (target := [sort, sort])))))

private def star_11_44_middle
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Formula.star11AlwaysStable outerUniversal
    (sameDisjunction disjunction
      (Formula.star11AlwaysStable innerUniversal phi)
      (p.rename (fun v => .succ v)))

/-- The printed right member `(x,y).φ(x,y) ∨ p`, independently built as
an external disjunction after the double universal closure. -/
def star_11_44_right
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  sameDisjunction disjunction
    (Formula.star11AlwaysStable outerUniversal
      (Formula.star11AlwaysStable innerUniversal phi)) p

def star_11_44_reading
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Star11Reading signature real where
  printed := "⊢ : .(x, y) : φ(x, y) .∨ .p : ≡ :\n(x, y).φ(x, y) .∨ .p"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_44_left innerUniversal outerUniversal disjunction phi p)
    (star_11_44_right innerUniversal outerUniversal disjunction phi p))
  scopeReading := "The left member is the independently nested universal closure; the right member is an external disjunction whose left child is the independently nested universal closure."

/-- ✱11·44.  `line1` is the inner ✱10·2 instance, `line2` is its
printed ✱10·271 lift, and `line3` is the outer ✱10·2 instance.
`demonstration_provenance: follows-printed`. -/
theorem star_11_44
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height)) :
    Derivation (star_11_44_reading innerUniversal outerUniversal negation
      disjunction phi p).parsed := by
  let innerLeft := Formula.star11AlwaysStable innerUniversal
    (sameDisjunction disjunction phi
      (p.rename (emptyRenaming (target := [sort, sort]))))
  let innerRight := sameDisjunction disjunction
    (Formula.star11AlwaysStable innerUniversal phi)
    (p.rename (fun v => .succ v))
  have line1a :
      Formula.star11FixSecond
        (p.rename (emptyRenaming (target := [sort, sort]))) =
      p.weakenReal.rename (fun v => .succ v) := by
    unfold Formula.star11FixSecond
    rw [Formula.weakenReal_rename, Formula.rename_substitute]
    exact Formula.closed_substitute p.weakenReal _ (fun v => .succ v)
  have line1 : Derivation (.assertion (star_4_01 negation disjunction
      (innerLeft.weakenReal.instantiate (.real .zero))
      (innerRight.weakenReal.instantiate (.real .zero)))) := by
    unfold innerLeft innerRight
    rw [Formula.star11AlwaysStable_weakenReal_instantiate,
      Formula.star11FixSecond_sameDisjunction, line1a,
      star11_disjunction_weakenReal_instantiate_closedRight,
      Formula.star11AlwaysStable_weakenReal_instantiate]
    exact star11_stableUniversalDisjunction innerUniversal negation
      disjunction (Formula.star11FixSecond phi) p.weakenReal
  have line2 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_44_left innerUniversal outerUniversal disjunction phi p)
      (star_11_44_middle innerUniversal outerUniversal disjunction phi p))) := by
    have line2a : Derivation (.assertion
        ((equivalence negation disjunction innerLeft innerRight).weakenReal.instantiate
          (.real (.zero : Var (sort :: real) sort)))) := by
      rw [star11_equivalence_weakenReal, Formula.instantiate,
        star11_equivalence_substitute]
      exact line1
    have line2b := star11_stableGeneralize outerUniversal
      (equivalence negation disjunction innerLeft innerRight) line2a
    have line2c := star_10_271 (baseOrder := 0) outerUniversal negation
      disjunction
      innerLeft innerRight
    unfold star_10_271_reading star_10_271_left star_10_271_right at line2c
    have line2d := detach negation disjunction _ _ line2b line2c
    unfold star_11_44_left star_11_44_middle
    exact line2d
  have line3 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_44_middle innerUniversal outerUniversal disjunction phi p)
      (star_11_44_right innerUniversal outerUniversal disjunction phi p))) := by
    unfold star_11_44_middle star_11_44_right
    exact star11_stableUniversalDisjunction outerUniversal negation
      disjunction (Formula.star11AlwaysStable innerUniversal phi) p
  exact star11_chainEquivalence negation disjunction
    (star_11_44_left innerUniversal outerUniversal disjunction phi p)
    (star_11_44_middle innerUniversal outerUniversal disjunction phi p)
    (star_11_44_right innerUniversal outerUniversal disjunction phi p)
    line2 line3

private def star_11_45_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.sometimes₂Saturated inner outer negation
    (sameConjunction negation disjunction
      (Formula.weakenApparent₂ (sort := sort) p) phi)

/- ✱11·45 is intentionally absent: the two placements of the closed
conjunct were not built independently. -/

private theorem star_10_37_left_normalize
    (existential : signature.Existential sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height)) :
    star_10_37_left existential universal negation disjunction p phi =
      Formula.star11SometimesStable universal negation
        (implication negation disjunction
          (p.rename (fun v => .succ v)) phi) := by
  unfold star_10_37_left Formula.star11SometimesStable
    Formula.star11AlwaysStable
  change Formula.star11SometimesStableRaw existential universal negation
      (implication negation disjunction
        (p.rename (fun v => .succ v)) phi) = _
  rw [Formula.star11SometimesStableRaw_normalize]
  rfl

private theorem star_10_37_right_normalize
    (existential : signature.Existential sort (Nat.succ sort.height))
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height)) :
    star_10_37_right existential universal negation disjunction p phi =
      implication negation disjunction p
        (Formula.star11SometimesStable universal negation phi) := by
  unfold star_10_37_right
  change implication negation disjunction p
      (Formula.star11SometimesStableRaw existential universal negation phi) = _
  rw [Formula.star11SometimesStableRaw_normalize]

def star_11_46_left
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Formula.star11SometimesStable outerUniversal negation
    (Formula.star11SometimesStable innerUniversal negation
      (implication negation disjunction
        (p.rename (emptyRenaming (target := [sort, sort]))) phi))

private def star_11_46_middle
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  Formula.star11SometimesStable outerUniversal negation
    (implication negation disjunction
      (p.rename (fun v => .succ v))
      (Formula.star11SometimesStable innerUniversal negation phi))

/-- The printed right member `p ⊃ (∃x,y).φ(x,y)`, independently built as
an implication whose consequent is the nested existential closure. -/
def star_11_46_right
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height)) :
    Formula signature real [] (Nat.succ sort.height) :=
  implication negation disjunction p
    (Formula.star11SometimesStable outerUniversal negation
      (Formula.star11SometimesStable innerUniversal negation phi))

def star_11_46_reading
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height)) :
    Star11Reading signature real where
  printed := "⊢ : .(∃x, y) : p .⊃ .φ(x, y) : ≡ :\np .⊃ .(∃x, y).φ(x, y)"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_46_left innerUniversal outerUniversal negation disjunction p phi)
    (star_11_46_right innerUniversal outerUniversal negation disjunction p phi))
  scopeReading := "The left member is the independently nested existential closure of the implication matrix; the right member is an implication whose consequent is the independently nested existential closure."

/-- ✱11·46.  `line1` is the inner ✱10·37 instance, `line2` is its
printed ✱10·281 lift, and `line3` is the outer ✱10·37 instance.
`demonstration_provenance: follows-printed`. -/
theorem star_11_46
    (innerExistential outerExistential :
      signature.Existential sort (Nat.succ sort.height))
    (innerUniversal outerUniversal :
      signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (p : Formula signature real [] (Nat.succ sort.height))
    (phi : Formula signature real [sort, sort] (Nat.succ sort.height))
    (witness : Term signature real [] sort) :
    Derivation (star_11_46_reading innerUniversal outerUniversal negation
      disjunction p phi).parsed := by
  let innerLeft := Formula.star11SometimesStable innerUniversal negation
    (implication negation disjunction
      (p.rename (emptyRenaming (target := [sort, sort]))) phi)
  let innerRight := implication negation disjunction
    (p.rename (fun v => .succ v))
    (Formula.star11SometimesStable innerUniversal negation phi)
  have line1a :
      Formula.star11FixSecond
        (p.rename (emptyRenaming (target := [sort, sort]))) =
      p.weakenReal.rename (fun v => .succ v) := by
    unfold Formula.star11FixSecond
    rw [Formula.weakenReal_rename, Formula.rename_substitute]
    exact Formula.closed_substitute p.weakenReal _ (fun v => .succ v)
  have line1b := star_10_37 innerExistential innerUniversal negation
    disjunction p.weakenReal (Formula.star11FixSecond phi)
    (.real (.zero : Var (sort :: real) sort))
  have line1 : Derivation (.assertion (star_4_01 negation disjunction
      (innerLeft.weakenReal.instantiate (.real .zero))
      (innerRight.weakenReal.instantiate (.real .zero)))) := by
    unfold innerLeft innerRight
    rw [Formula.star11SometimesStable_weakenReal_instantiate,
      Formula.star11FixSecond_implication, line1a,
      Formula.star11Implication_weakenReal_instantiate,
      Formula.closed_weakenReal_instantiate,
      Formula.star11SometimesStable_weakenReal_instantiate]
    unfold star_10_37_reading at line1b
    rw [star_10_37_left_normalize, star_10_37_right_normalize] at line1b
    exact line1b
  have line2 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_46_left innerUniversal outerUniversal negation disjunction p phi)
      (star_11_46_middle innerUniversal outerUniversal negation disjunction
        p phi))) := by
    unfold star_11_46_left star_11_46_middle
    exact star11_liftStableExistentialEquivalence outerUniversal negation
      disjunction innerLeft innerRight line1
  have line3 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_46_middle innerUniversal outerUniversal negation disjunction
        p phi)
      (star_11_46_right innerUniversal outerUniversal negation disjunction
        p phi))) := by
    have line3a := star_10_37 outerExistential outerUniversal negation
      disjunction p (Formula.star11SometimesStable innerUniversal negation phi)
      witness
    unfold star_10_37_reading at line3a
    rw [star_10_37_left_normalize, star_10_37_right_normalize] at line3a
    unfold star_11_46_middle star_11_46_right
    exact line3a
  exact star11_chainEquivalence negation disjunction
    (star_11_46_left innerUniversal outerUniversal negation disjunction p phi)
    (star_11_46_middle innerUniversal outerUniversal negation disjunction p phi)
    (star_11_46_right innerUniversal outerUniversal negation disjunction p phi)
    line2 line3

private def star_11_47_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (p : Formula signature real [] (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (sameConjunction negation disjunction
      (Formula.weakenApparent₂ (sort := sort) p) phi)

/- ✱11·47 is intentionally absent: universal/conjunction scope was
collapsed before it was proved. -/

private def star_11_5_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.neg negation (Formula.always₂Saturated inner outer body)

/- ✱11·5 is intentionally absent: all three printed members were replaced
by one common formula before the two equivalences were asserted. -/

private def star_11_52_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.sometimes₂Saturated inner outer negation
    (sameConjunction negation disjunction phi psi)

/- ✱11·52 is intentionally absent: the existential conjunction and the
negated universal implication are consequences, not identical premises. -/

/- ✱11·7 is intentionally absent: variable permutation and idempotence are
the proof, and cannot be assumed by giving both sides the same AST. -/

def star_11_3_left
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [leftSort, rightSort] matrixOrder) :=
  star_11_12_right inner outer matrixDisjunction
    (Formula.neg fixedNegation p) phi

def star_11_3_right
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [leftSort, rightSort] matrixOrder) :=
  star_11_12_left inner outer matrixDisjunction
    (Formula.neg fixedNegation p) phi

theorem star_11_3_left_unfold
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [leftSort, rightSort] matrixOrder) :
    star_11_3_left inner outer fixedNegation matrixDisjunction p phi =
      star_11_3_right inner outer fixedNegation matrixDisjunction p phi := by
  unfold star_11_3_left star_11_3_right
  exact star_11_12_right_unfold inner outer matrixDisjunction
    (Formula.neg fixedNegation p) phi

def star_11_3_reading
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerNegation : signature.Negation
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (outerDisjunction : signature.Disjunction
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [leftSort, rightSort] matrixOrder) :
    Star11Reading signature real where
  printed := "⊢ : .p .⊃ .(x, y).φ(x, y) .≡ : (x, y) : p .⊃ .φ(x, y)"
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (star_11_3_left inner outer fixedNegation matrixDisjunction p phi)
    (star_11_3_right inner outer fixedNegation matrixDisjunction p phi))
  scopeReading := "The left implication is parsed through the nested ✱9·04 scope abbreviation; the right member is the independently closed pointwise implication."

/-- ✱11·3.  The cited ✱10·21 and ✱10·271 reduce the left member through
the same nested ✱9·04 scope expansion used by ✱11·12.
`demonstration_provenance: follows-printed-definitional-normalization`. -/
theorem star_11_3
    (inner : signature.Universal leftSort (max fixedOrder matrixOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max fixedOrder matrixOrder) leftSort))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerNegation : signature.Negation
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (outerDisjunction : signature.Disjunction
      (bindOrder
        (bindOrder (max fixedOrder matrixOrder) leftSort) rightSort))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [leftSort, rightSort] matrixOrder) :
    Derivation (star_11_3_reading inner outer fixedNegation
      matrixDisjunction outerNegation outerDisjunction p phi).parsed := by
  have line1 := star_4_2 outerNegation outerDisjunction
    (star_11_3_right inner outer fixedNegation matrixDisjunction p phi)
  unfold star_11_3_reading
  rw [star_11_3_left_unfold]
  exact line1

def star_11_35_left
    (inner : signature.Universal leftSort (max matrixOrder fixedOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max matrixOrder fixedOrder) leftSort))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (phi : Formula signature real [leftSort, rightSort] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (max matrixOrder fixedOrder) leftSort) rightSort) :=
  .always outer (.always inner
    (.disj matrixDisjunction (.neg matrixNegation phi)
      ((p.rename (emptyRenaming (target := [rightSort]))).rename
        (fun v => .succ v))))

/-- The printed right member `(∃x,y).φ(x,y) ⊃ p`.  ✱9·02 removes the
negated existential and the remaining disjunction is scoped by ✱9·03; the
last retained abbreviation is therefore the inner ✱9·03 below. -/
def star_11_35_right
    (inner : signature.Universal leftSort (max matrixOrder fixedOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max matrixOrder fixedOrder) leftSort))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (phi : Formula signature real [leftSort, rightSort] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (max matrixOrder fixedOrder) leftSort) rightSort) :=
  .always outer
    (star_9_03 inner matrixDisjunction (.neg matrixNegation phi)
      (p.rename (emptyRenaming (target := [rightSort]))))

theorem star_11_35_right_unfold
    (inner : signature.Universal leftSort (max matrixOrder fixedOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max matrixOrder fixedOrder) leftSort))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (phi : Formula signature real [leftSort, rightSort] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    star_11_35_right inner outer matrixNegation matrixDisjunction phi p =
      star_11_35_left inner outer matrixNegation matrixDisjunction phi p := by
  unfold star_11_35_right star_11_35_left
  rw [star_9_03_unfold]

def star_11_35_reading
    (inner : signature.Universal leftSort (max matrixOrder fixedOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max matrixOrder fixedOrder) leftSort))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (outerNegation : signature.Negation
      (bindOrder
        (bindOrder (max matrixOrder fixedOrder) leftSort) rightSort))
    (outerDisjunction : signature.Disjunction
      (bindOrder
        (bindOrder (max matrixOrder fixedOrder) leftSort) rightSort))
    (phi : Formula signature real [leftSort, rightSort] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Star11Reading signature real where
  printed := "⊢ : .(x, y) : φ(x, y) .⊃ .p : ≡ :\n(∃x, y).φ(x, y) .⊃ .p  [✱10·23·271]"
  parsed := .assertion (star_4_01 outerNegation outerDisjunction
    (star_11_35_left inner outer matrixNegation matrixDisjunction phi p)
    (star_11_35_right inner outer matrixNegation matrixDisjunction phi p))
  scopeReading := "The existential antecedent on the right is eliminated by ✱9·02 before the disjunction with p is scoped by ✱9·03; no raw negated existential occurs in the AST."

/-- ✱11·35.  The cited ✱10·23 and ✱10·271 are the recursive ✱9·02/✱9·03
scope normalization recorded by the independently built right member.
`demonstration_provenance: follows-printed-definitional-normalization`. -/
theorem star_11_35
    (inner : signature.Universal leftSort (max matrixOrder fixedOrder))
    (outer : signature.Universal rightSort
      (bindOrder (max matrixOrder fixedOrder) leftSort))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (outerNegation : signature.Negation
      (bindOrder
        (bindOrder (max matrixOrder fixedOrder) leftSort) rightSort))
    (outerDisjunction : signature.Disjunction
      (bindOrder
        (bindOrder (max matrixOrder fixedOrder) leftSort) rightSort))
    (phi : Formula signature real [leftSort, rightSort] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Derivation (star_11_35_reading inner outer matrixNegation
      matrixDisjunction outerNegation outerDisjunction phi p).parsed := by
  have line1 := star_4_2 outerNegation outerDisjunction
    (star_11_35_left inner outer matrixNegation matrixDisjunction phi p)
  unfold star_11_35_reading
  rw [star_11_35_right_unfold]
  exact line1

private theorem star_11_1_transp_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) :
    let universalNegation := Formula.always₂Saturated inner outer
      (Formula.neg negation body)
    ⊢ᵣ implication negation disjunction (body.instantiate₂ left right)
      (Formula.neg negation universalNegation) := by
  let universalNegation := Formula.always₂Saturated inner outer
    (Formula.neg negation body)
  let bodyInstance := body.instantiate₂ left right
  have line1Raw := star_11_1_saturated inner outer negation disjunction
    (Formula.neg negation body) left right
  have negatedInstanceEq :
      (Formula.neg negation body).instantiate₂ left right =
        Formula.neg negation bodyInstance := by
    unfold bodyInstance
    rw [Formula.neg_instantiate₂]
  have line1 := Derivation.castAssertion
    (congrArg (implication negation disjunction universalNegation)
      negatedInstanceEq.symm) line1Raw
  have line2 := detach negation disjunction
    (implication negation disjunction universalNegation
      (Formula.neg negation bodyInstance))
    (implication negation disjunction
      (Formula.neg negation (Formula.neg negation bodyInstance))
      (Formula.neg negation universalNegation)) line1
    (star_2_16 negation disjunction universalNegation
      (Formula.neg negation bodyInstance))
  have line3 := compose negation disjunction bodyInstance
    (Formula.neg negation (Formula.neg negation bodyInstance))
    (Formula.neg negation universalNegation)
    (star_2_12 negation disjunction bodyInstance) line2
  exact line3

def star_11_36_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) : Star11Reading signature real where
  printed := "⊢ : φ(z, w) .⊃ .(∃x, y).φ(x, y)"
  parsed := .assertion (implication negation disjunction
    (body.instantiate₂ left right)
    (Formula.neg negation (Formula.always₂Saturated inner outer
      (Formula.neg negation body))))

/-! ✱11·36 suit exactement la spécialisation ✱11·1 puis sa transposition.
`demonstration_provenance: follows-printed`. -/
theorem star_11_36
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) :
    Derivation (.assertion (implication negation disjunction
      (body.instantiate₂ left right)
      (Formula.neg negation (Formula.always₂Saturated inner outer
        (Formula.neg negation body))))) := by
  have line1 := star_11_1_transp_instance inner outer negation disjunction
    body left right
  exact line1

private def star_11_38_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  let hypothesis := Formula.always₂Saturated inner outer
    (implication negation disjunction phi psi)
  implication negation disjunction
    (Formula.weakenApparent₂ (sort := sort) hypothesis)
    (implication negation disjunction
      (sameConjunction negation disjunction phi chi)
      (sameConjunction negation disjunction psi chi))

private theorem Fact_star_11_11_star_11_32_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_38_body inner outer negation disjunction phi psi chi) := by
  apply star_11_11_saturated inner outer
    (star_11_38_body inner outer negation disjunction phi psi chi)
  intro left right
  let matrix := implication negation disjunction phi psi
  let hypothesis := Formula.always₂Saturated inner outer matrix
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let chiInstance := chi.instantiate₂ left right
  let matrixInstance := implication negation disjunction phiInstance psiInstance
  let conclusion := implication negation disjunction
    (conjunction negation disjunction phiInstance chiInstance)
    (conjunction negation disjunction psiInstance chiInstance)
  have line1Raw := star_11_1_saturated inner outer negation disjunction
    matrix left right
  have matrixInstanceEq : matrix.instantiate₂ left right = matrixInstance := by
    unfold matrix matrixInstance
    rw [Formula.implication_instantiate₂]
  have line1 := Derivation.castAssertion
    (congrArg (implication negation disjunction hypothesis)
      matrixInstanceEq.symm) line1Raw
  have line2 := star_3_45 negation disjunction
    phiInstance psiInstance chiInstance
  have line3 := compose negation disjunction hypothesis matrixInstance
    conclusion line1 line2
  have bodyEq :
      (star_11_38_body inner outer negation disjunction phi psi chi).instantiate₂
          left right =
        implication negation disjunction hypothesis conclusion := by
    dsimp [star_11_38_body, matrix, hypothesis, phiInstance, psiInstance,
      chiInstance, conclusion]
    rw [Formula.implication_instantiate₂,
      Formula.implication_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction]
  exact Derivation.castAssertion bodyEq line3

def star_11_38_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : Star11Reading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) :. ⊃ :\n(x, y) : φ(x, y).χ(x, y) .⊃ .ψ(x, y).χ(x, y)"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_11_38_body inner outer negation disjunction phi psi chi))

/-! ✱11·38 suit `Fact`, ✱11·11 et ✱11·32, comme l'indique la citation imprimée.
`demonstration_provenance: follows-printed`. -/
theorem star_11_38
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation (.assertion (Formula.always₂Saturated inner outer
      (star_11_38_body inner outer negation disjunction phi psi chi))) := by
  have line1 := Fact_star_11_11_star_11_32_instance
    inner outer negation disjunction phi psi chi
  exact line1

private def star_11_39_body
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  let first := Formula.always₂Saturated inner outer
    (implication negation disjunction phi psi)
  let second := Formula.always₂Saturated inner outer
    (implication negation disjunction chi theta)
  implication negation disjunction
    (sameConjunction negation disjunction
      (Formula.weakenApparent₂ (sort := sort) first)
      (Formula.weakenApparent₂ (sort := sort) second))
    (implication negation disjunction
      (sameConjunction negation disjunction phi chi)
      (sameConjunction negation disjunction psi theta))

private theorem star_3_47_star_11_11_star_11_32_instance
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    ⊢ᵣ Formula.always₂Saturated inner outer
      (star_11_39_body inner outer negation disjunction phi psi chi theta) := by
  apply star_11_11_saturated inner outer
    (star_11_39_body inner outer negation disjunction phi psi chi theta)
  intro left right
  let firstMatrix := implication negation disjunction phi psi
  let secondMatrix := implication negation disjunction chi theta
  let first := Formula.always₂Saturated inner outer firstMatrix
  let second := Formula.always₂Saturated inner outer secondMatrix
  let hypothesis := conjunction negation disjunction first second
  let phiInstance := phi.instantiate₂ left right
  let psiInstance := psi.instantiate₂ left right
  let chiInstance := chi.instantiate₂ left right
  let thetaInstance := theta.instantiate₂ left right
  let firstInstance := implication negation disjunction phiInstance psiInstance
  let secondInstance := implication negation disjunction chiInstance thetaInstance
  let conclusion := implication negation disjunction
    (conjunction negation disjunction phiInstance chiInstance)
    (conjunction negation disjunction psiInstance thetaInstance)
  have line1Raw := star_11_1_saturated inner outer negation disjunction
    firstMatrix left right
  have firstInstanceEq : firstMatrix.instantiate₂ left right = firstInstance := by
    unfold firstMatrix firstInstance
    rw [Formula.implication_instantiate₂]
  have line1a := Derivation.castAssertion
    (congrArg (implication negation disjunction first)
      firstInstanceEq.symm) line1Raw
  have line1 := compose negation disjunction hypothesis first firstInstance
    (star_3_26 negation disjunction first second) line1a
  have line2Raw := star_11_1_saturated inner outer negation disjunction
    secondMatrix left right
  have secondInstanceEq : secondMatrix.instantiate₂ left right =
      secondInstance := by
    unfold secondMatrix secondInstance
    rw [Formula.implication_instantiate₂]
  have line2a := Derivation.castAssertion
    (congrArg (implication negation disjunction second)
      secondInstanceEq.symm) line2Raw
  have line2 := compose negation disjunction hypothesis second secondInstance
    (star_3_27 negation disjunction first second) line2a
  have line3 := PM.RamifiedSyntax.star_11_13 negation disjunction
    (implication negation disjunction hypothesis firstInstance)
    (implication negation disjunction hypothesis secondInstance) line1 line2
  have line4 := detach negation disjunction
    (conjunction negation disjunction
      (implication negation disjunction hypothesis firstInstance)
      (implication negation disjunction hypothesis secondInstance))
    (implication negation disjunction hypothesis
      (conjunction negation disjunction firstInstance secondInstance)) line3
    (star_3_43 negation disjunction hypothesis firstInstance secondInstance)
  have line5 := compose negation disjunction hypothesis
    (conjunction negation disjunction firstInstance secondInstance) conclusion
    line4 (star_3_47 negation disjunction phiInstance chiInstance
      psiInstance thetaInstance)
  have bodyEq :
      (star_11_39_body inner outer negation disjunction phi psi chi theta).instantiate₂
          left right =
        implication negation disjunction hypothesis conclusion := by
    dsimp [star_11_39_body, firstMatrix, secondMatrix, first, second,
      hypothesis, phiInstance, psiInstance, chiInstance, thetaInstance,
      conclusion]
    rw [Formula.implication_instantiate₂]
    rw [Formula.sameConjunction_instantiate₂,
      Formula.weakenApparent₂_instantiate₂,
      Formula.weakenApparent₂_instantiate₂]
    rw [Formula.implication_instantiate₂]
    rw [Formula.sameConjunction_instantiate₂,
      Formula.sameConjunction_instantiate₂,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction,
      sameConjunction_eq_conjunction]
  exact Derivation.castAssertion bodyEq line5

def star_11_39_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : Star11Reading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : .(x, y) :\nχ(x, y) .⊃ .θ(x, y) :. ⊃ : (x, y) : φ(x, y).χ(x, y) .⊃ .ψ(x, y).θ(x, y)"
  parsed := .assertion (Formula.always₂Saturated inner outer
    (star_11_39_body inner outer negation disjunction phi psi chi theta))

/-! ✱11·39 suit ✱3·47, puis ✱11·11 et ✱11·32.
`demonstration_provenance: follows-printed`. -/
theorem star_11_39
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :
    Derivation (.assertion (Formula.always₂Saturated inner outer
      (star_11_39_body inner outer negation disjunction phi psi chi theta))) := by
  have line1 := star_3_47_star_11_11_star_11_32_instance
    inner outer negation disjunction phi psi chi theta
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
      (bindOrder baseOrder sort)) : Star11Reading signature real where
  printed := "⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : ⊃ :\n(∃x, y).φ(x, y) .⊃ .(∃x, y).ψ(x, y)"
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
    Derivation (.assertion (Formula.always₂Saturated inner outer
      (star_10_27_star_10_28_body inner outer negation disjunction phi psi))) := by
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

/- ✱11·21 is intentionally absent: a cyclic permutation of three bound
variables is a derived equivalence, not one copied member. -/

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

/- ✱11·22 is intentionally absent: the binary existential and its
double-negation expansion were written as one expression. -/

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

/- ✱11·23 is intentionally absent: the two existential binding orders
were collapsed before their permutation was proved. -/

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

/- ✱11·24 is intentionally absent: the cyclic existential permutation was
assumed by assigning both members one common normal form. -/

def star_11_25_left
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Formula signature real []
      (bindOrder (bindOrder matrixOrder leftSort) rightSort) :=
  .always outer.universal
    (star_9_02 inner.universal inner.matrixNegation body)

def star_11_25_right
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Formula signature real []
      (bindOrder (bindOrder matrixOrder leftSort) rightSort) :=
  .always outer.universal
    (.always inner.universal (.neg inner.matrixNegation body))

theorem star_11_25_left_unfold
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    star_11_25_left inner outer body =
      star_11_25_right inner outer body := by
  unfold star_11_25_left star_11_25_right
  rw [star_9_02_unfold]

def star_11_25_reading
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Star11Reading signature real where
  printed := "⊢ : ∼{(∃x, y).φ(x, y)} .≡ .(x, y).∼φ(x, y)  [✱11·22.Transp]"
  parsed := .assertion (star_4_01 negation disjunction
    (star_11_25_left inner outer body)
    (star_11_25_right inner outer body))
  scopeReading := "The left member applies ✱9·02 recursively to the printed negated existential; the right member is the independently built double universal closure."

/-- ✱11·25.  The two independently parsed members coincide only after the
printed scope definition ✱9·02 is unfolded.
`demonstration_provenance: follows-printed`. -/
theorem star_11_25
    (inner : ExistentialVocabulary signature leftSort matrixOrder)
    (outer : ExistentialVocabulary signature rightSort
      (bindOrder matrixOrder leftSort))
    (negation : signature.Negation
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (disjunction : signature.Disjunction
      (bindOrder (bindOrder matrixOrder leftSort) rightSort))
    (body : Formula signature real [leftSort, rightSort] matrixOrder) :
    Derivation
      (star_11_25_reading inner outer negation disjunction body).parsed := by
  have line1 := star_4_2 negation disjunction
    (star_11_25_right inner outer body)
  unfold star_11_25_reading
  rw [star_11_25_left_unfold]
  exact line1

def star_11_27_left
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort) :=
  Formula.sometimes third (star_11_03 first second body)

def star_11_27_middle
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort) :=
  star_11_03 second third (Formula.sometimes first body)

def star_11_27_right
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    Formula signature real []
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort) :=
  star_11_04 first second third body

theorem star_11_27_left_middle
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    star_11_27_left first second third body =
      star_11_27_middle first second third body := rfl

theorem star_11_27_middle_right
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    star_11_27_middle first second third body =
      star_11_27_right first second third body := rfl

def star_11_27_reading
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (negation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort))
    (disjunction : signature.Disjunction
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    Star11Reading signature real where
  printed := "⊢ : .(∃x, y) : (∃z).φ(x, y, z) .≡ : (∃x) : (∃y, z).φ(x, y, z)\n≡ : (∃x, y, z).φ(x, y, z)"
  parsed := .assertion (conjunction negation disjunction
    (star_4_01 negation disjunction
      (star_11_27_left first second third body)
      (star_11_27_middle first second third body))
    (star_4_01 negation disjunction
      (star_11_27_middle first second third body)
      (star_11_27_right first second third body)))
  scopeReading := "The three members are constructed independently from ✱11·03 and ✱11·04; their equality is a consequence of unfolding those Df clauses."

/-- ✱11·27.  Lines (1)--(3) retain the three independently printed
groupings; only the Df unfoldings make the corresponding members coincide.
`demonstration_provenance: follows-printed`. -/
theorem star_11_27
    (first : ExistentialVocabulary signature firstSort matrixOrder)
    (second : ExistentialVocabulary signature secondSort
      (bindOrder matrixOrder firstSort))
    (third : ExistentialVocabulary signature thirdSort
      (bindOrder (bindOrder matrixOrder firstSort) secondSort))
    (negation : signature.Negation
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort))
    (disjunction : signature.Disjunction
      (bindOrder
        (bindOrder (bindOrder matrixOrder firstSort) secondSort) thirdSort))
    (body : Formula signature real
      [firstSort, secondSort, thirdSort] matrixOrder) :
    Derivation
      (star_11_27_reading first second third negation disjunction body).parsed := by
  have line1 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_27_left first second third body)
      (star_11_27_middle first second third body))) := by
    rw [star_11_27_left_middle]
    exact star_4_2 negation disjunction
      (star_11_27_middle first second third body)
  have line2 : Derivation (.assertion (star_4_01 negation disjunction
      (star_11_27_middle first second third body)
      (star_11_27_right first second third body))) := by
    rw [star_11_27_middle_right]
    exact star_4_2 negation disjunction
      (star_11_27_right first second third body)
  have line3 := conjoin negation disjunction _ _ line1 line2
  exact line3

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

private def keepHeadRenaming (sort : RSort) : Renaming [sort] [sort, sort]
  | _, .zero => .zero
  | _, .succ v => nomatch v

private def secondHeadRenaming (sort : RSort) : Renaming [sort] [sort, sort]
  | _, .zero => .succ .zero
  | _, .succ v => nomatch v

private def Formula.sometimesHeadSaturated
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  Formula.neg negation
    (Formula.alwaysHeadSaturated universal (Formula.neg negation body))

private def Formula.alwaysOuterSaturated
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real [sort] (bindOrder baseOrder sort)) :
    Formula signature real [] (bindOrder baseOrder sort) :=
  Eq.mp (congrArg (Formula signature real [])
    (bindOrder_idem baseOrder sort)) (.always universal body)

private theorem Term.closed_weaken_instantiate
    (term : Term signature real [] sort)
    (value : Term signature real [] binder) :
    term.weaken.substitute (instantiateSubstitution value) = term := by
  cases term with
  | real v => rfl
  | apparent v => cases v
  | symbol payload => rfl

private theorem Formula.keepHead_instantiate₂
    (formula : Formula signature real [sort] order)
    (left right : Term signature real [] sort) :
    (formula.rename (keepHeadRenaming sort)).instantiate₂ left right =
      formula.instantiate left := by
  unfold Formula.instantiate₂ Formula.instantiate
  rw [Formula.rename_substitute, Formula.substitute_substitute]
  apply Formula.substitute_of_pointwise
  intro targetSort v
  cases v with
  | zero =>
      change left.weaken.substitute (instantiateSubstitution right) = left
      exact Term.closed_weaken_instantiate left right
  | succ v => cases v

private def star_11_53_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort] (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (implication negation disjunction
      (phi.rename (keepHeadRenaming sort))
      (psi.rename (secondHeadRenaming sort)))

/- ✱11·53 is intentionally absent: the universal binary implication and
the implication between separately quantified members were conflated. -/

private def star_11_54_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort] (bindOrder baseOrder sort)) :=
  Formula.sometimes₂Saturated inner outer negation
    (sameConjunction negation disjunction
      (phi.rename (keepHeadRenaming sort))
      (psi.rename (secondHeadRenaming sort)))

/- ✱11·54 is intentionally absent: a joint existential conjunction and
the conjunction of two existentials are not definitionally identical. -/

private def star_11_55_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi : Formula signature real [sort] (bindOrder baseOrder sort))
    (psi : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :=
  Formula.sometimes₂Saturated inner outer negation
    (sameConjunction negation disjunction
      (phi.rename (keepHeadRenaming sort)) psi)

/- ✱11·55 is intentionally absent: nested and joint existential scopes
were replaced by a single normal form before proof. -/

private def star_11_56_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort] (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (sameConjunction negation disjunction
      (phi.rename (keepHeadRenaming sort))
      (psi.rename (secondHeadRenaming sort)))

/- ✱11·56 is intentionally absent: conjunction of separate universals and
universal closure of a conjunction require the printed derivation. -/

/- ✱11·57 is intentionally absent: adding a second quantified copy and
using idempotence is a proof step, not a definition. -/

/- ✱11·58 is intentionally absent: the two existential assertions differ
before ✱11·54 and idempotence are applied. -/

private def star_11_59_normalForm
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi : Formula signature real [sort] (bindOrder baseOrder sort)) :=
  Formula.alwaysHeadSaturated universal
    (implication negation disjunction phi psi)

/- ✱11·59 is intentionally absent: its unary and binary pointwise
implications were made identical before the four printed steps. -/

private def star_11_51_normalForm
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  let forallY := Formula.alwaysHeadSaturated universal body.swapHeads
  Formula.sometimesHeadSaturated universal negation forallY

/- ✱11·51 is intentionally absent: the alternating quantifier members
were collapsed instead of related by the printed transposition chain. -/

private def star_11_6_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi : Formula signature real [sort, sort] (bindOrder baseOrder sort))
    (psi chi : Formula signature real [sort] (bindOrder baseOrder sort)) :=
  Formula.sometimes₂Saturated inner outer negation
    (sameConjunction negation disjunction
      (sameConjunction negation disjunction phi
        (psi.rename (secondHeadRenaming sort)))
      (chi.rename (keepHeadRenaming sort)))

/- ✱11·6 is intentionally absent: the two nested existential orders and
the permuted conjuncts were represented by one formula. -/

private def star_11_62_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi : Formula signature real [sort] (bindOrder baseOrder sort))
    (psi chi : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (implication negation disjunction
      (sameConjunction negation disjunction
        (phi.rename (keepHeadRenaming sort)) psi) chi)

/- ✱11·62 is intentionally absent: the binary conjunctive antecedent and
the nested implications were not independently represented. -/

private def star_11_71_normalForm
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (phi psi chi theta : Formula signature real [sort]
      (bindOrder baseOrder sort)) :=
  Formula.always₂Saturated inner outer
    (implication negation disjunction
      (sameConjunction negation disjunction
        (phi.rename (keepHeadRenaming sort))
        (chi.rename (secondHeadRenaming sort)))
      (sameConjunction negation disjunction
        (psi.rename (keepHeadRenaming sort))
        (theta.rename (secondHeadRenaming sort))))

/- ✱11·71 is intentionally absent: its quantified premise and binary
consequent require the seven printed steps and cannot be reflexivity. -/

private theorem Formula.alwaysHeadSaturated_substitute
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real (sort :: source)
      (bindOrder baseOrder sort))
    (substitution : Substitution signature real source target) :
    (Formula.alwaysHeadSaturated universal body).substitute substitution =
      Formula.alwaysHeadSaturated universal
        (body.substitute (liftSubstitution substitution)) := by
  unfold Formula.alwaysHeadSaturated
  rw [Formula.substitute_cast, substitute_always]
  exact bindOrder_idem baseOrder sort

private theorem Formula.swapHeads_substitute_left
    (body : Formula signature real [sort, sort] order)
    (left : Term signature real [] sort) :
    body.swapHeads.substitute
        (liftSubstitution (instantiateSubstitution left)) =
      body.instantiate left.weaken := by
  rw [Formula.swapHeads_substitute]
  unfold Formula.instantiate
  apply Formula.substitute_of_pointwise
  intro targetSort v
  cases v with
  | zero => rfl
  | succ v =>
      cases v with
      | zero => rfl
      | succ v => cases v

private def star_11_26_forallYAtX
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort)) :
    Formula signature real [sort, sort] (bindOrder baseOrder sort) :=
  (Formula.alwaysHeadSaturated universal body.swapHeads).rename
    (keepHeadRenaming sort)

private theorem star_11_26_forallYAtX_instantiate₂
    (universal : signature.Universal sort (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort] (bindOrder baseOrder sort))
    (left right : Term signature real [] sort) :
    (star_11_26_forallYAtX universal body).instantiate₂ left right =
      Formula.alwaysHeadSaturated universal (body.instantiate left.weaken) := by
  unfold star_11_26_forallYAtX
  rw [Formula.keepHead_instantiate₂]
  unfold Formula.instantiate
  rw [Formula.alwaysHeadSaturated_substitute,
    Formula.swapHeads_substitute_left]
  unfold Formula.instantiate
  rfl

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
    unfold star_11_26_matrix
    rw [Formula.implication_instantiate₂,
      Formula.neg_instantiate₂,
      Formula.neg_instantiate₂,
      star_11_26_forallYAtX_instantiate₂]
    dsimp [bodyAtLeft, universalAtLeft, Formula.instantiate₂]
  exact Derivation.castAssertion matrixEq line2

def star_11_26_reading
    (inner : signature.Universal sort (bindOrder baseOrder sort))
    (outer : signature.Universal sort
      (bindOrder (bindOrder baseOrder sort) sort))
    (negation : signature.Negation (bindOrder baseOrder sort))
    (disjunction : signature.Disjunction (bindOrder baseOrder sort))
    (body : Formula signature real [sort, sort]
      (bindOrder baseOrder sort)) : Star11Reading signature real where
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

private def star_11_61_matrix
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height))
    (psi : Formula signature real [sort, sort] (Nat.succ sort.height)) :=
  implication negation disjunction
    (phi.rename (keepHeadRenaming sort)) psi

private def star_11_61_outerUniversal
    {signature : Signature} {sort : RSort}
    (universal : signature.Universal sort (Nat.succ sort.height)) :
    signature.Universal sort
      (bindOrder (Nat.succ sort.height) sort) :=
  Eq.mp (congrArg (signature.Universal sort)
    (star11_stableOrder sort).symm) universal

private def star_11_61_normalForm
    (inner outer : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height))
    (psi : Formula signature real [sort, sort] (Nat.succ sort.height)) :=
  Formula.always₂Saturated (baseOrder := 0) inner
    (star_11_61_outerUniversal outer)
    (star_11_26_matrix (baseOrder := 0) inner negation disjunction
      (star_11_61_matrix negation disjunction phi psi))

def star_11_61_reading
    (inner outer : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height))
    (psi : Formula signature real [sort, sort]
      (Nat.succ sort.height)) : Star11Reading signature real where
  printed := "⊢ :: (∃y) : φx .⊃ₓ .ψ(x, y) : ⊃ : φx .⊃ₓ .(∃y).ψ(x, y)"
  parsed := .assertion
    (star_11_61_normalForm inner outer negation disjunction phi psi)

private theorem Formula.star11FixSecond_shift
    (phi : Formula signature real [sort] (Nat.succ sort.height)) :
    Formula.star11FixSecond
        (phi.rename (fun v => .succ v)) =
      (phi.weakenReal.instantiate
        (.real (.zero : Var (sort :: real) sort))).rename
          (fun v => .succ v) := by
  unfold Formula.star11FixSecond
  rw [Formula.weakenReal_rename, Formula.rename_substitute]
  let emptySubstitution : Substitution signature (sort :: real) [] [sort] :=
    fun v => nomatch v
  have closedEq := Formula.closed_substitute
    (phi.weakenReal.instantiate
      (.real (.zero : Var (sort :: real) sort)))
    emptySubstitution (fun v => .succ v)
  rw [← closedEq]
  unfold Formula.instantiate
  rw [Formula.substitute_substitute]
  apply Formula.substitute_of_pointwise _ _ _ phi.weakenReal
  intro targetSort v
  cases v with
  | zero => rfl
  | succ v => cases v

namespace Star10For11

/-- The stable-order instance of printed ✱10·27 used at ✱11·61. -/
theorem star_10_27
    (universal : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi psi : Formula signature real [sort] (Nat.succ sort.height)) :
    Derivation (star_10_27_stable_reading universal negation disjunction
      phi psi).parsed := by
  have line1 := PM.RamifiedSyntax.star_10_27_stable universal negation
    disjunction phi psi
  exact line1

end Star10For11

/-! ✱11·61 suit ✱11·26, ✱10·37, puis ✱10·11·27. L'instance de
✱11·26 porte la matrice `φx ⊃ ψ(x,y)` ; les deux dernières citations
en donnent exactement la lecture à portée normalisée ci-dessus.
`demonstration_provenance: follows-printed`. -/
theorem star_11_61
    (innerExistential : signature.Existential sort (Nat.succ sort.height))
    (inner outer : signature.Universal sort (Nat.succ sort.height))
    (negation : signature.Negation (Nat.succ sort.height))
    (disjunction : signature.Disjunction (Nat.succ sort.height))
    (phi : Formula signature real [sort] (Nat.succ sort.height))
    (psi : Formula signature real [sort, sort] (Nat.succ sort.height)) :
    Derivation (.assertion
      (star_11_61_normalForm inner outer negation disjunction phi psi)) := by
  have line1 := star_11_26 (baseOrder := 0) inner
    (star_11_61_outerUniversal outer) negation disjunction
      (star_11_61_matrix negation disjunction phi psi)
  let matrixYX := implication negation disjunction
    (phi.rename (fun v => .succ v)) psi.swapHeads
  let leftAtX := Formula.star11SometimesStable inner negation matrixYX
  let rightAtX := implication negation disjunction phi
    (Formula.star11SometimesStable inner negation psi.swapHeads)
  let phiAtX := phi.weakenReal.instantiate
    (.real (.zero : Var (sort :: real) sort))
  let psiAtX := Formula.star11FixSecond psi.swapHeads
  have line2a := star_10_37 innerExistential inner negation disjunction
    phiAtX psiAtX (.real (.zero : Var (sort :: real) sort))
  unfold star_10_37_reading at line2a
  rw [star_10_37_left_normalize, star_10_37_right_normalize] at line2a
  unfold phiAtX psiAtX at line2a
  have line2b : Derivation (.assertion (star_4_01 negation disjunction
      (leftAtX.weakenReal.instantiate (.real .zero))
      (rightAtX.weakenReal.instantiate (.real .zero)))) := by
    unfold leftAtX rightAtX matrixYX
    rw [Formula.star11SometimesStable_weakenReal_instantiate,
      Formula.star11FixSecond_implication,
      Formula.star11FixSecond_shift,
      Formula.star11Implication_weakenReal_instantiate,
      Formula.star11SometimesStable_weakenReal_instantiate]
    exact line2a
  have line2c := detach negation disjunction _ _ line2b
    (star_3_26 negation disjunction
      (implication negation disjunction
        (leftAtX.weakenReal.instantiate (.real .zero))
        (rightAtX.weakenReal.instantiate (.real .zero)))
      (implication negation disjunction
        (rightAtX.weakenReal.instantiate (.real .zero))
        (leftAtX.weakenReal.instantiate (.real .zero))))
  have line2c' : Derivation (.assertion
      ((implication negation disjunction leftAtX rightAtX).weakenReal.instantiate
        (.real (.zero : Var (sort :: real) sort)))) := by
    rw [Formula.star11Implication_weakenReal_instantiate]
    exact line2c
  have line2d := star11_stableGeneralize outer
    (implication negation disjunction leftAtX rightAtX) line2c'
  have line2e := Star10For11.star_10_27 outer negation disjunction
    leftAtX rightAtX
  unfold star_10_27_stable_reading star_10_27_stable_left
    star_10_27_stable_right at line2e
  have line2 := detach negation disjunction _ _ line2d line2e
  have line3 := conjoin negation disjunction _ _ line1 line2
  have line4 := detach negation disjunction _ _ line3
    (star_3_26 negation disjunction
      (star_11_61_normalForm inner outer negation disjunction phi psi)
      (implication negation disjunction
        (Formula.star11AlwaysStable outer leftAtX)
        (Formula.star11AlwaysStable outer rightAtX)))
  exact line4

#print axioms star_11_01_unfold
#print axioms star_11_02_unfold
#print axioms star_11_03_unfold
#print axioms star_11_04_unfold
#print axioms star_11_05_unfold
#print axioms star_11_06_unfold
#print axioms star_11_07
#print axioms star_11_1
#print axioms star_11_11
#print axioms star_11_12_right_unfold
#print axioms star_11_12
#print axioms star_11_13
#print axioms star_11_14
#print axioms star_11_2
#print axioms star_11_25_left_unfold
#print axioms star_11_25
#print axioms star_11_26
#print axioms star_11_27_left_middle
#print axioms star_11_27_middle_right
#print axioms star_11_27
#print axioms star_11_3_left_unfold
#print axioms star_11_3
#print axioms star_11_311
#print axioms star_11_32
#print axioms star_11_33
#print axioms star_11_34
#print axioms star_11_35_right_unfold
#print axioms star_11_35
#print axioms star_11_36
#print axioms star_11_37
#print axioms star_11_371
#print axioms star_11_38
#print axioms star_11_39
#print axioms star_11_4
#print axioms star_11_401
#print axioms star_11_42
#print axioms star_11_43
#print axioms star_11_44
#print axioms star_11_46
#print axioms star_11_61

end PM.RamifiedSyntax
