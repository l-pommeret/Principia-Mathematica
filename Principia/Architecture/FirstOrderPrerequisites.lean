import Principia.Deduction.Ordered
import Principia.FirstEdition.Volume1.Star9
import Principia.FirstEdition.Volume1.Part1.SectionA.Star2

namespace PM.Architecture.FirstOrderPrerequisites

/-!
# Closed prerequisites for PM I ✱9

This is the first assertion layer beyond `Elementary`.  It deliberately has
only the two printed Pp constructors ✱9·1 and ✱9·11, plus the two printed
metalinguistic inference principles ✱9·12 and ✱9·13 at their first assigned
order.  In particular it is not an open `RuleBook` and it does not postulate
an all-orders transport principle.

The definitions ✱9·01–·08 are already kernel reductions in
`PM.FirstEdition.Volume1.Star9` and `PM.FirstOrder`; every implication below
is built with `OrderedFormula.firstImp`, whose disjunction bears the explicit
`.sameAssignedOrder` scope certificate.  Thus no bare cross-order connective
is admitted here.
-/

open PM.OrderedFormula

/-- A sealed description of the matrix operations licensed for one *fixed*
successor step.  It is private on purpose: clients cannot manufacture a
new family, choose an arbitrary order, or turn it into a free all-orders
generalization principle.  The sole value below is the audited first-order to
second-order instance used at ✱9·21, line (4). -/
private structure MatrixSyntaxAt (order : Nat) where
  Matrix : RealContext → BoundContext → Type
  renameReal : {Γ Ξ : RealContext} → {Δ : BoundContext} →
    Apparent.RealRenaming Γ Ξ → Matrix Γ Δ → Matrix Ξ Δ
  abstractHead : {Γ : RealContext} → {Δ : BoundContext} →
    Matrix (.elementaryProposition :: Γ) Δ →
      Matrix Γ (.elementaryProposition :: Δ)
  all : {Γ : RealContext} →
    Matrix Γ [.elementaryProposition] → OrderedFormula Γ (order + 1)

/-- The only installed `MatrixSyntaxAt` instance.  Its operations are the
capture-safe first-order operations of `Apparent.lean`; they are not a
semantic interpretation and they do not range over an arbitrary level. -/
private def firstOrderMatrixSyntaxAt : MatrixSyntaxAt 1 where
  Matrix := fun Γ Δ => FirstOrder Γ Δ
  renameReal := fun ρ proposition => FirstOrder.renameReal ρ proposition
  abstractHead := fun proposition => FirstOrder.abstractRealHead proposition
  all := fun body => OrderedFormula.alwaysFirstOrder body

/-- The public name is intentionally specific to the sole audited 1→2
transition.  It exposes no constructor indexed by an arbitrary order. -/
def firstOrderToSecondAll (body : FirstOrder Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  firstOrderMatrixSyntaxAt.all body

@[simp] theorem firstOrderToSecondAll_reduction
    (body : FirstOrder Γ [.elementaryProposition]) :
    firstOrderToSecondAll body = OrderedFormula.alwaysFirstOrder body := rfl

/-- Alpha-renaming a closed first-order proposition has no free apparent
variable to alter.  The empty renaming is explicit so later uses of the
printed `y` and `z` binders cannot silently invoke substitution. -/
def closedFirstOrderAlphaRenaming : Apparent.Renaming [] [] :=
  fun emptyVariable => nomatch emptyVariable

@[simp] theorem closedFirstOrder_alpha
    (body : Apparent Γ [.elementaryProposition]) :
    FirstOrder.rename closedFirstOrderAlphaRenaming (FirstOrder.always body) =
      FirstOrder.always body := by
  change Quantified.always
    (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) body) =
      Quantified.always body
  congr 1
  induction body with
  | constant name => rfl
  | real realVariable => rfl
  | bound boundVariable =>
      cases boundVariable with
      | zero => rfl
      | succ emptyBoundVariable => exact nomatch emptyBoundVariable
  | neg proposition ih =>
      change Apparent.neg
        (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) proposition) =
          Apparent.neg proposition
      rw [ih]
  | disj left right ihLeft ihRight =>
      change Apparent.disj
        (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) left)
        (Apparent.rename (Apparent.liftRenaming closedFirstOrderAlphaRenaming) right) =
          Apparent.disj left right
      rw [ihLeft, ihRight]

/-- Elementary implication in a one-place matrix.  It is only the printed
✱1·01 abbreviation at matrix level, never Lean implication. -/
def matrixImp (φ ψ : Apparent Γ Δ) : Apparent Γ Δ :=
  Apparent.disj (Apparent.neg φ) ψ

/-- The exact first Pp of ✱9, with `x` represented by the newly leading real
variable and `z` by the distinct apparent binder of `sometimes`.  The
existential conclusion is weakened back into the context in which `φx` is
displayed, so the printed occurrence of `x` remains free only in the premise.
-/
def star_9_1_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 1 :=
  .firstOrder
    (FirstOrder.impElementaryToFirst (Apparent.openHead φ)
      (FirstOrder.weakenReal (FirstOrder.sometimes φ)))

/-- A metalinguistic schema instance of ✱9·1 at an explicitly supplied real
value.  This is the same primitive proposition schema as `star_9_1_target`,
not an object-syntactic substitution rule: `Apparent.instantiate` records the
displayed value `φx`, while the existential consequent retains the function
`φ` itself. -/
def star_9_1_instance_target (φ : Apparent Γ [.elementaryProposition])
    (value : Elementary Γ) : OrderedFormula Γ 1 :=
  .firstOrder
    (FirstOrder.impElementaryToFirst
      (Apparent.elementaryValue φ value)
      (FirstOrder.sometimes φ))

/-- The exact second Pp of ✱9.  The two values `φx` and `φy` use two distinct
leading real variables; their common existential conclusion has neither as a
significant free variable.  This is why it is a separate closed constructor,
not an application of elementary disjunction elimination. -/
def star_9_11_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: .elementaryProposition :: Γ) 1 :=
  let lifted := Apparent.weakenReal (Apparent.weakenReal φ)
  let φx := Apparent.atReal lifted .zero
  let φy := Apparent.atReal lifted (.succ .zero)
  let conclusion := FirstOrder.weakenReal
    (FirstOrder.weakenReal (FirstOrder.sometimes φ))
  .firstOrder (FirstOrder.impElementaryToFirst (φx ∨ₚ φy) conclusion)

/-- Universal monotonicity, the exact target of ✱9·21.  The first binder has
the scope of the matrix implication `φx ⊃ ψx`; the conclusion is an assigned
first-order implication. -/
def star_9_21_target (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp
    (OrderedFormula.always (matrixImp φ ψ))
    (firstImp (OrderedFormula.always φ) (OrderedFormula.always ψ))

/-- The exact normalized matrix in line (4) of the printed proof of ✱9·3.
The outer `x` is the remaining matrix variable; the inner `y` is introduced
by `always`.  The implication is the syntax reduction `∼P ∨ q` via
✱9·05·01·04, not a new first-order connective or assertion. -/
def star_9_3_line4_matrix (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder Γ [.elementaryProposition] :=
  let inner : FirstOrder Γ [.elementaryProposition] :=
    FirstOrder.always (Apparent.rename Apparent.innerVariableRenaming φ)
  FirstOrder.impFirstToMatrix (FirstOrder.disjMatrixLeft φ inner) φ

/-- The normalized line (2) of the proof of ✱9·3.  The existential binder
scopes the whole implication `(φx∨φy)⊃φx`, as fixed by the leaf-161 scope
audit; it is not an implication with an existential antecedent. -/
def star_9_3_line2_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula (.elementaryProposition :: Γ) 1 :=
  .firstOrder
    (FirstOrder.sometimes
      (matrixImp (Apparent.openHeadOrBound φ)
        (Apparent.ofElementary (Apparent.openHead φ))))

/-- The outer `x` generalization of line (4), at the sole represented second
assigned order. -/
def star_9_3_line4_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  firstOrderToSecondAll (star_9_3_line4_matrix φ)

/-- The first-order identity cited by ✱9·25.  It is kept separate rather than
collapsed to Lean reflexivity: its printed proof is `Id.✱9·13·21`. -/
def star_9_23_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  firstImp (OrderedFormula.always φ) (OrderedFormula.always φ)

/-- The exact target of ✱9·25.  Its right side uses the certified ✱9·04
normalization `p ∨ (x).φx := (x).p ∨ φx`; the left side is the displayed
universal scope of that same matrix. -/
def star_9_25_target (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  firstImp
    (OrderedFormula.always (Apparent.ofElementary p ∨ₐ φ))
    (.firstOrder (FirstOrder.disjElementaryLeft p (FirstOrder.always φ)))

/-- Assertion at an explicitly assigned order.  Real-variable contexts remain
schematic PM contexts, never lists of Lean hypotheses. -/
inductive OrderedAssertion : {Γ : RealContext} → {order : Nat} →
    OrderedFormula Γ order → Prop where
  | elementary {p : Elementary Γ} : Derivation p →
      OrderedAssertion (.elementary p)
  /-- ✱9·1, a closed Pp constructor at its exact formula schema. -/
  | star_9_1 (φ : Apparent Γ [.elementaryProposition]) :
      OrderedAssertion (star_9_1_target φ)
  /-- The explicit metalinguistic instance form of the same ✱9·1 Pp schema.
  Its value parameter corresponds to PM's schematic instantiation convention;
  it introduces neither a new inference rule nor a target-specific oracle. -/
  | star_9_1_instance (φ : Apparent Γ [.elementaryProposition])
      (value : Elementary Γ) :
      OrderedAssertion (star_9_1_instance_target φ value)
  /-- ✱9·11, deliberately independent of ✱9·1 as required by the printed
  circularity warning concerning the first-order Taut analogue. -/
  | star_9_11 (φ : Apparent Γ [.elementaryProposition]) :
      OrderedAssertion (star_9_11_target φ)
  /-- ✱9·12 at the single currently assigned first order: detachment only
  where the antecedent and implication carry the same certified order-one
  scope.  This is not a cross-order modus ponens. -/
  | star_9_12 {p q : OrderedFormula Γ 1} :
      OrderedAssertion p → OrderedAssertion (firstImp p q) →
      OrderedAssertion q
  /-- The unique order-two specialization of the metalinguistic rule ✱9·12.
  On p. 137 PM says that the rule applies even when `p` and `q` are not
  elementary, and immediately states the corresponding case for functions
  that are not necessarily elementary.  This constructor is therefore a
  fixed inference specialization, not a new object-language Pp and not an
  order-polymorphic detachment rule. -/
  | star_9_12_second {p q : OrderedFormula Γ 2} :
      OrderedAssertion p → OrderedAssertion (secondImp p q) →
      OrderedAssertion q
  /-- The mixed elementary/first-order instance of ✱9·12.  Its implication
  shape is exactly the ✱9·06-certified definition `∼p ∨ (∃x).φx`; this is
  the branch used immediately after ✱9·1 in the printed demonstration of
  ✱9·3.  It is not a promotion rule and cannot detach arbitrary orders. -/
  | star_9_12_elementary_to_first {p : Elementary Γ} {q : FirstOrder Γ []} :
      OrderedAssertion (.elementary p) →
      OrderedAssertion (.firstOrder (FirstOrder.impElementaryToFirst p q)) →
      OrderedAssertion (.firstOrder q)
  /-- ✱9·13 from the displayed asserted elementary value with a leading real
  variable to the corresponding universally quantified first-order assertion.
  `openHead` fixes the exact real/apparent binding correspondence; arbitrary
  substitution is intentionally absent. -/
  | star_9_13 (φ : Apparent Γ [.elementaryProposition]) :
      OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.elementary (Apparent.openHead φ)) →
      OrderedAssertion (.firstOrder (FirstOrder.always φ))
  /-- The one assigned next-order instance of ✱9·13 required by line (3) of
  the printed proof of ✱9·3.  Its premise opens the *outer* apparent slot as
  a leading real variable while preserving the already-open inner binder;
  its conclusion immediately closes that same slot.  There is deliberately
  no constructor quantified over arbitrary proposition orders or matrix APIs. -/
  | star_9_13_first (φ : FirstOrder Γ [.elementaryProposition]) :
      OrderedAssertion (Γ := .elementaryProposition :: Γ)
        (.firstOrder (FirstOrder.openRealOuter φ)) →
      OrderedAssertion (firstOrderToSecondAll φ)

/-- Line (2) of the printed demonstration of ✱9·3.  The diagonal elementary
instance of ✱1·2 is the antecedent; the supplied instance of ✱9·1 has the
audited existential scope over the complete matrix implication, and the mixed
form of ✱9·12 performs exactly the displayed detachment. -/
def derive_star_9_3_line2 (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_3_line2_target φ) := by
  let χ : Apparent (.elementaryProposition :: Γ) [.elementaryProposition] :=
    matrixImp (Apparent.openHeadOrBound φ)
      (Apparent.ofElementary (Apparent.openHead φ))
  have line1 : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary ((Apparent.openHead φ ∨ₚ Apparent.openHead φ) ⊃ₚ
        Apparent.openHead φ)) :=
    .elementary (PM.Derivation.star_1_2 (Apparent.openHead φ))
  have lineOneInstance : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.firstOrder
        (FirstOrder.impElementaryToFirst
          ((Apparent.openHead φ ∨ₚ Apparent.openHead φ) ⊃ₚ Apparent.openHead φ)
          (FirstOrder.sometimes χ))) := by
    simpa [star_9_1_instance_target, χ, matrixImp, Apparent.openHeadOrBound,
      Apparent.elementaryValue, Apparent.weakenReal, Apparent.renameReal,
      Apparent.rename] using
      OrderedAssertion.star_9_1_instance χ (.var .zero)
  exact OrderedAssertion.star_9_12_elementary_to_first line1 lineOneInstance

/-- The matrix whose universal closure is line (3) of ✱9·3.  Closing exactly
the leading real slot expresses the printed outer `(x)` and changes no
apparent binder. -/
def star_9_3_line3_matrix (φ : Apparent Γ [.elementaryProposition]) :
    FirstOrder Γ [.elementaryProposition] :=
  FirstOrder.abstractRealOuter
    (FirstOrder.sometimes
      (matrixImp (Apparent.openHeadOrBound φ)
        (Apparent.ofElementary (Apparent.openHead φ))))

/-- The assigned second-order reading of line (3) of ✱9·3. -/
def star_9_3_line3_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 2 :=
  firstOrderToSecondAll (star_9_3_line3_matrix φ)

/-- The printed normalization `(3).(✱9·05·01·04)` is structural in the
certified syntax: it moves the existential disjunction outward, exchanges
its negation for the universal form, and then puts the fixed left matrix back
under that universal binder. -/
theorem star_9_3_line3_to_line4 (φ : Apparent Γ [.elementaryProposition]) :
    star_9_3_line3_matrix φ = star_9_3_line4_matrix φ := by
  simp only [star_9_3_line3_matrix, star_9_3_line4_matrix,
    FirstOrder.abstractRealOuter, FirstOrder.impFirstToMatrix,
    FirstOrder.disjMatrixLeft, FirstOrder.disjRightMatrix, FirstOrder.neg,
    Quantified.neg, matrixImp, Apparent.openHeadOrBound,
    Apparent.abstractRealOuter, Apparent.abstractRealOuter_ofElementary_openHead]
  rw [← Apparent.abstractRealOuter_weakenReal φ]

/-- Line (3) follows from line (2) by the fixed first-to-second-order instance
of ✱9·13; the reduction of `openRealHead` is structural. -/
def derive_star_9_3_line3 (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_3_line3_target φ) := by
  have line2 : OrderedAssertion
      (.firstOrder (FirstOrder.openRealOuter (star_9_3_line3_matrix φ))) := by
    simpa [star_9_3_line2_target, star_9_3_line3_matrix] using
      derive_star_9_3_line2 φ
  simpa [star_9_3_line3_target] using
    OrderedAssertion.star_9_13_first (star_9_3_line3_matrix φ) line2

/-- Line (4) of ✱9·3, retaining the printed definition chain as the explicit
syntax normalization established by `star_9_3_line3_to_line4`. -/
def derive_star_9_3_line4 (φ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (star_9_3_line4_target φ) := by
  change OrderedAssertion (firstOrderToSecondAll (star_9_3_line4_matrix φ))
  rw [← star_9_3_line3_to_line4 φ]
  exact derive_star_9_3_line3 φ

/-- Line (2) of the printed demonstration of ✱9·21.  With `z` the leading
real variable, `χ(y)` is `(φz ⊃ ψz) ⊃ (φy ⊃ ψz)`.  Its displayed instance at
`y = z` is the ✱2·08 identity from line (1), so the conclusion follows from
the exact ✱9·1 instance and mixed ✱9·12. -/
def derive_star_9_21_line2 (φ ψ : Apparent Γ [.elementaryProposition]) :
    OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.firstOrder (FirstOrder.sometimes
        (matrixImp
          (Apparent.ofElementary ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
          (matrixImp (Apparent.weakenReal φ)
            (Apparent.ofElementary (Apparent.openHead ψ)))))) := by
  let χ : Apparent (.elementaryProposition :: Γ) [.elementaryProposition] :=
    matrixImp
      (Apparent.ofElementary ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
      (matrixImp (Apparent.weakenReal φ)
        (Apparent.ofElementary (Apparent.openHead ψ)))
  have line1 : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary (((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ) ⊃ₚ
        ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))) :=
    .elementary (PM.FirstEdition.Volume1.Star2.star_2_08
      ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
  have lineOneInstance : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.firstOrder (FirstOrder.impElementaryToFirst
        (((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ) ⊃ₚ
          ((Apparent.openHead φ) ⊃ₚ Apparent.openHead ψ))
        (FirstOrder.sometimes χ))) := by
    simpa [star_9_1_instance_target, χ, matrixImp, Apparent.elementaryValue,
      Apparent.weakenReal, Apparent.renameReal, Apparent.rename] using
      OrderedAssertion.star_9_1_instance χ (.var .zero)
  exact OrderedAssertion.star_9_12_elementary_to_first line1 lineOneInstance


/-- The exact judgement sought for ✱9·21.  It is a target contract, not an
invented primitive: it becomes inhabited only by a derivation from the
printed demonstration and its audited citations. -/
abbrev Star_9_21Derivation (φ ψ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (star_9_21_target φ ψ)

/-- `Id.✱9·13·21` in the exact first-order form printed at ✱9·23.  The
elementary identity is passed explicitly and ✱9·21 remains an explicit
citation; no reflexivity shortcut or new general identity rule is introduced.
-/
def derive_star_9_23 (φ : Apparent Γ [.elementaryProposition])
    (elementaryId : OrderedAssertion (Γ := .elementaryProposition :: Γ)
      (.elementary (Apparent.openHead (matrixImp φ φ))))
    (monotonicity : Star_9_21Derivation φ φ) :
    OrderedAssertion (star_9_23_target φ) :=
  OrderedAssertion.star_9_12
    (OrderedAssertion.star_9_13 (matrixImp φ φ) elementaryId)
    monotonicity

/-- The exact judgement sought for ✱9·25. -/
abbrev Star_9_25Derivation (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : Prop :=
  OrderedAssertion (star_9_25_target p φ)

/-- ✱9·25 follows from the explicitly cited ✱9·23 instance and the certified
✱9·04 normalization.  The conversion is definitional only because the
historical citation stays an argument of this declaration. -/
def derive_star_9_25 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition])
    (identity : OrderedAssertion
      (star_9_23_target (Apparent.ofElementary p ∨ₐ φ))) :
    Star_9_25Derivation p φ :=
  identity

end PM.Architecture.FirstOrderPrerequisites
