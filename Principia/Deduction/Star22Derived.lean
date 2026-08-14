import Principia.Deduction.Star4Ramified
import Principia.Deduction.Star10Derived
import Principia.FirstEdition.Volume1.Star22Source
import Principia.Syntax.Printed

namespace PM.RamifiedSyntax

/- A T4 reading for the ramified heterogeneous claim syntax. -/
structure RamifiedReading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

/-! # Derived propositions of PM I, ✱22

The class-forming signs of this number are incomplete symbols.  The four
class-valued operations below therefore take a continuation and expand by
✱20·01; they do not manufacture class terms.  Membership is ✱20·02.
-/

/-- The vocabulary needed by one predicative class abstraction ✱20·01. -/
structure Star22ClassVocabulary (signature : Signature)
    (order scopeOrder : Nat) where
  existential : ExistentialVocabulary signature (classSort order 0)
    (max (bindOrder order .individual) scopeOrder)
  universal : signature.Universal .individual order
  equivalenceNegation : signature.Negation order
  equivalenceDisjunction : signature.Disjunction order
  leftNegation : signature.Negation (bindOrder order .individual)
  rightNegation : signature.Negation scopeOrder
  outerNegation : signature.Negation
    (max (bindOrder order .individual) scopeOrder)
  conjunctionDisjunction : signature.Disjunction
    (max (bindOrder order .individual) scopeOrder)

/-- ✱22·01: inclusion, expanded as universal pointwise implication. -/
def star_22_01
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    Formula signature real [] (bindOrder order .individual) :=
  .always universal
    (implication negation disjunction
      (star_20_02 alpha.weaken (.apparent .zero))
      (star_20_02 beta.weaken (.apparent .zero)))

theorem star_22_01_unfold
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0)) :
    star_22_01 universal negation disjunction alpha beta =
      .always universal
        (implication negation disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 beta.weaken (.apparent .zero))) := rfl

/-- ✱22·02: intersection, as the contextual abstraction ✱20·01. -/
def star_22_02 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (sameDisjunction disjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      (.neg negation (star_20_02 beta.weaken (.apparent .zero))))) continuation

/-- ✱22·03: union, as the contextual abstraction ✱20·01. -/
def star_22_03 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (sameDisjunction disjunction
      (star_20_02 alpha.weaken (.apparent .zero))
      (star_20_02 beta.weaken (.apparent .zero))) continuation

/-- ✱22·04: complement, as the contextual abstraction ✱20·01. -/
def star_22_04 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (alpha : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (star_20_02 alpha.weaken (.apparent .zero))) continuation

/-- ✱22·05: difference, with ✱22·02 and ✱22·04 fully eliminated. -/
def star_22_05 (vocabulary : Star22ClassVocabulary signature order scopeOrder)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta : Term signature real [] (classSort order 0))
    (continuation : Formula signature real [classSort order 0] scopeOrder) :=
  star_20_01 vocabulary.existential vocabulary.universal
    vocabulary.equivalenceNegation vocabulary.equivalenceDisjunction
    vocabulary.leftNegation vocabulary.rightNegation vocabulary.outerNegation
    vocabulary.conjunctionDisjunction
    (.neg negation (sameDisjunction disjunction
      (.neg negation (star_20_02 alpha.weaken (.apparent .zero)))
      (.neg negation (.neg negation
        (star_20_02 beta.weaken (.apparent .zero)))))) continuation

/-- Audited scope reading of ✱22·1. -/
def star_22_1_reading
    (universal : signature.Universal .individual order)
    (inclusionNegation : signature.Negation order)
    (inclusionDisjunction : signature.Disjunction order)
    (equivalenceNegation : signature.Negation (bindOrder order .individual))
    (equivalenceDisjunction : signature.Disjunction (bindOrder order .individual))
    (alpha beta : Term signature real [] (classSort order 0)) :
    ClaimReading signature real where
  printed := "⊢ : α ⊂ β .≡ : x ε α .⊃ₓ. x ε β"
  parsed := .assertion (star_4_01 equivalenceNegation equivalenceDisjunction
    (star_22_01 universal inclusionNegation inclusionDisjunction alpha beta)
    (star_22_01 universal inclusionNegation inclusionDisjunction alpha beta))

/-- ✱22·1, following PM's printed `[✱4·2.(✱22·01)]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_1
    (universal : signature.Universal .individual order)
    (inclusionNegation : signature.Negation order)
    (inclusionDisjunction : signature.Disjunction order)
    (equivalenceNegation : signature.Negation (bindOrder order .individual))
    (equivalenceDisjunction : signature.Disjunction (bindOrder order .individual))
    (alpha beta : Term signature real [] (classSort order 0)) :
    Derivation (star_22_1_reading universal inclusionNegation
      inclusionDisjunction equivalenceNegation equivalenceDisjunction alpha beta).parsed := by
  have line1 := star_22_01_unfold universal inclusionNegation
    inclusionDisjunction alpha beta
  have line2 := star_4_2 equivalenceNegation equivalenceDisjunction
    (star_22_01 universal inclusionNegation inclusionDisjunction alpha beta)
  rw [line1] at line2
  exact line2

/-- Audited scope reading of ✱22·42. -/
def star_22_42_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order 0)) :
    ClaimReading signature real where
  printed := "⊢ . α ⊂ α"
  parsed := .assertion (star_22_01 universal negation disjunction alpha alpha)

/-- ✱22·42, following PM's printed `[Id.*10·11]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_42
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha : Term signature real [] (classSort order 0)) :
    Derivation (star_22_42_reading universal negation disjunction alpha).parsed := by
  let body := star_20_02 alpha.weaken (.apparent .zero)
  let value : Term signature (.individual :: real) [] .individual :=
    .real (.zero : Var (.individual :: real) .individual)
  have line1 : Derivation (.assertion
      ((implication negation disjunction body body).weakenReal.instantiate value)) := by
    rw [implication_weakenReal, Formula.instantiate, implication_substitute]
    exact star_2_08 negation disjunction (body.weakenReal.instantiate value)
  have line2 := Derivation.star_10_11 universal
    (implication negation disjunction body body) line1
  exact line2

/-! ### The printed ✱10·3 route used by ✱22·44

The apparent variable in PM's formal implications has the whole assertion as
its real scope. Thus the instance needed below is the universal closure of
the pointwise `Syll` matrix. -/

private def apparentConjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction (.neg negation left) (.neg negation right))

private theorem apparentConjunction_weakenReal
    {fresh : RSort}
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (apparentConjunction negation disjunction left right).weakenReal
        (fresh := fresh) =
      apparentConjunction negation disjunction
        (left.weakenReal (fresh := fresh))
        (right.weakenReal (fresh := fresh)) := by
  unfold apparentConjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  rfl

private theorem apparentConjunction_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (apparentConjunction negation disjunction left right).substitute sigma =
      apparentConjunction negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold apparentConjunction
  change Formula.neg negation
    ((sameDisjunction disjunction (.neg negation left)
      (.neg negation right)).substitute sigma) = _
  rw [sameDisjunction_substitute]
  rfl

namespace Star10For22

/-- The exact full-scope reading of ✱10·3 used at ✱22·44. -/
def star_10_3_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [.individual] order) :
    ClaimReading signature real where
  printed := "✱10·3.  ⊢ : .(x).φx⊃ψx : (x).ψx⊃χx : ⊃ .(x).φx⊃χx"
  parsed := .assertion (.always universal
    (implication negation disjunction
      (apparentConjunction negation disjunction
        (implication negation disjunction phi psi)
        (implication negation disjunction psi chi))
      (implication negation disjunction phi chi)))

/-- Ramified realization of ✱10·3 in the full-scope normal form used by PM.
`demonstration_provenance: editorial-reconstruction`. -/
theorem star_10_3
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (phi psi chi : Formula signature real [.individual] order) :
    Derivation (star_10_3_reading universal negation disjunction
      phi psi chi).parsed := by
  let body := implication negation disjunction
    (apparentConjunction negation disjunction
      (implication negation disjunction phi psi)
      (implication negation disjunction psi chi))
    (implication negation disjunction phi chi)
  let value : Term signature (.individual :: real) [] .individual :=
    .real (.zero : Var (.individual :: real) .individual)
  have line1 : Derivation (.assertion
      (body.weakenReal.instantiate value)) := by
    unfold body
    rw [implication_weakenReal, apparentConjunction_weakenReal,
      Formula.instantiate, implication_substitute,
      apparentConjunction_substitute]
    unfold apparentConjunction
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    rw [implication_weakenReal, implication_substitute]
    exact star_3_33 negation disjunction
      (phi.weakenReal.substitute (instantiateSubstitution value))
      (psi.weakenReal.substitute (instantiateSubstitution value))
      (chi.weakenReal.substitute (instantiateSubstitution value))
  have line2 := Derivation.star_10_11 universal body line1
  exact line2

end Star10For22

/-- Audited full-scope reading of ✱22·44. -/
def star_22_44_reading
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta gamma : Term signature real [] (classSort order 0)) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : α ⊂ β . β ⊂ γ .⊃ . α ⊂ γ"
  parsed := .assertion (.always universal
    (implication negation disjunction
      (apparentConjunction negation disjunction
        (implication negation disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 beta.weaken (.apparent .zero)))
        (implication negation disjunction
          (star_20_02 beta.weaken (.apparent .zero))
          (star_20_02 gamma.weaken (.apparent .zero))))
      (implication negation disjunction
        (star_20_02 alpha.weaken (.apparent .zero))
        (star_20_02 gamma.weaken (.apparent .zero)))))
  scopeReading := "The three class variables have the scope of the displayed implication."

/-- Binding an individual does not raise an already positive matrix order. -/
private theorem bindOrder_succ_individual (order : Nat) :
    bindOrder (Nat.succ order) .individual = Nat.succ order := by
  cases order with
  | zero => rfl
  | succ order => rfl

/-- Inclusion at a positive order, with the computed binder order exposed. -/
private def star_22_01_successor
    (universal : signature.Universal .individual (Nat.succ order))
    (negation : signature.Negation (Nat.succ order))
    (disjunction : signature.Disjunction (Nat.succ order))
    (alpha beta : Term signature real [] (classSort (Nat.succ order) 0)) :
    Formula signature real [] (Nat.succ order) :=
  Eq.mp
    (congrArg (Formula signature real []) (bindOrder_succ_individual order))
    (star_22_01 universal negation disjunction alpha beta)

/-- Audited scope reading of ✱22·441. -/
def star_22_441_reading
    (universal : signature.Universal .individual (Nat.succ order))
    (negation : signature.Negation (Nat.succ order))
    (disjunction : signature.Disjunction (Nat.succ order))
    (alpha beta : Term signature real [] (classSort (Nat.succ order) 0))
    (x : Term signature real [] .individual) :
    RamifiedReading signature real where
  printed := PM.pmPrinted "⊢ : α ⊂ β . x ε α .⊃ . x ε β"
  parsed := .assertion
    (implication negation disjunction
      (conjunction negation disjunction
        (star_22_01_successor universal negation disjunction alpha beta)
        (star_20_02 alpha x))
      (star_20_02 beta x))
  scopeReading := "The inclusion and antecedent membership form the antecedent of the final implication."

/-- Transport a derivation along the computed equality of two ramified
formula orders.  This is only dependent transport in Lean's metalanguage. -/
private theorem castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

/-- Transport only along literal equality of object formulae. -/
private theorem castAssertionFormula
    {left right : Formula signature real [] order}
    (equality : left = right) :
    Derivation (.assertion right) → Derivation (.assertion left) := by
  cases equality
  exact fun derivation => derivation

/-- Instantiating the displayed membership matrix restores its closed class
argument and replaces exactly the displayed individual variable. -/
private theorem star_20_02_weaken_instantiate
    (predicate : Term signature real [] (classSort resultOrder 0))
    (x : Term signature real [] .individual) :
    (star_20_02 predicate.weaken
      (.apparent (.zero : Var [.individual] .individual))).substitute
        (instantiateSubstitution x) = star_20_02 predicate x := by
  cases predicate <;> rfl

/-- The pointwise implication matrix obtained by unfolding one inclusion. -/
private def star_22_441_body
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (alpha beta : Term signature real [] (classSort resultOrder 0)) :
    Formula signature real [.individual] resultOrder :=
  implication negation disjunction
    (star_20_02 alpha.weaken (.apparent .zero))
    (star_20_02 beta.weaken (.apparent .zero))

private theorem star_22_441_body_instantiate
    (negation : signature.Negation resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (alpha beta : Term signature real [] (classSort resultOrder 0))
    (x : Term signature real [] .individual) :
    (star_22_441_body negation disjunction alpha beta).instantiate x =
      implication negation disjunction
        (star_20_02 alpha x) (star_20_02 beta x) := by
  unfold star_22_441_body
  rw [Formula.instantiate, implication_substitute]
  rw [star_20_02_weaken_instantiate alpha x,
    star_20_02_weaken_instantiate beta x]

/-- Normalize the order casts forced by instantiating ✱22·01. -/
private theorem normalizeInclusionInstantiation
    {order : Nat}
    (universal : signature.Universal .individual order.succ)
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (alpha beta : Term signature real [] (classSort order.succ 0))
    (x : Term signature real [] .individual)
    (bindEq : bindOrder order.succ .individual = order.succ)
    (resultEq : max (bindOrder order.succ .individual) order.succ = order.succ)
    (line : Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) resultEq)
        (mixedImplication
          (Eq.mp (congrArg signature.Negation bindEq.symm) negation)
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          (.always universal (star_22_441_body negation disjunction alpha beta))
          ((star_22_441_body negation disjunction alpha beta).instantiate x))))) :
    ⊢ᵣ implication negation disjunction
      (star_22_01_successor universal negation disjunction alpha beta)
      ((star_22_441_body negation disjunction alpha beta).instantiate x) := by
  exact castAssertionFormula
    (by
      unfold star_22_01_successor star_22_01 star_22_441_body
      exact (mixedImplication_normalizeSameOrder bindEq rfl negation
        disjunction (.always universal
          (implication negation disjunction
            (star_20_02 alpha.weaken (.apparent .zero))
            (star_20_02 beta.weaken (.apparent .zero))))
        ((implication negation disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 beta.weaken (.apparent .zero))).instantiate x)).symm)
    line

/-- The propositional `Imp` presentation used after ✱10·1. -/
private theorem implicationPresentation
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (line1 : ⊢ᵣ implication negation disjunction p
      (implication negation disjunction q r)) :
    ⊢ᵣ implication negation disjunction
      (conjunction negation disjunction p q) r := by
  have line2 := star_3_31 negation disjunction p q r
  have line3 := Derivation.star_9_12_same negation disjunction line1 line2
  exact line3

/-- ✱22·44, exactly the printed `[✱10·3]` instance.
`demonstration_provenance: follows-printed`. -/
theorem star_22_44
    (universal : signature.Universal .individual order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (alpha beta gamma : Term signature real [] (classSort order 0)) :
    Derivation (.assertion (.always universal
      (implication negation disjunction
        (apparentConjunction negation disjunction
          (implication negation disjunction
            (star_20_02 alpha.weaken (.apparent .zero))
            (star_20_02 beta.weaken (.apparent .zero)))
          (implication negation disjunction
            (star_20_02 beta.weaken (.apparent .zero))
            (star_20_02 gamma.weaken (.apparent .zero))))
        (implication negation disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 gamma.weaken (.apparent .zero)))))) := by
  have line1 : Derivation (.assertion (.always universal
      (implication negation disjunction
        (apparentConjunction negation disjunction
          (implication negation disjunction
            (star_20_02 alpha.weaken (.apparent .zero))
            (star_20_02 beta.weaken (.apparent .zero)))
          (implication negation disjunction
            (star_20_02 beta.weaken (.apparent .zero))
            (star_20_02 gamma.weaken (.apparent .zero))))
        (implication negation disjunction
          (star_20_02 alpha.weaken (.apparent .zero))
          (star_20_02 gamma.weaken (.apparent .zero)))))) :=
    Star10For22.star_10_3 universal negation disjunction _ _ _
  exact line1

/-- ✱22·441, following PM's printed `[✱10·1.Imp]` route.
`demonstration_provenance: follows-printed`. -/
theorem star_22_441
    {order : Nat}
    (universal : signature.Universal .individual order.succ)
    (negation : signature.Negation order.succ)
    (disjunction : signature.Disjunction order.succ)
    (alpha beta : Term signature real [] (classSort order.succ 0))
    (x : Term signature real [] .individual) :
    Derivation (.assertion
      (implication negation disjunction
        (conjunction negation disjunction
          (star_22_01_successor universal negation disjunction alpha beta)
          (star_20_02 alpha x))
        (star_20_02 beta x))) := by
  let body := star_22_441_body negation disjunction alpha beta
  have bindEq : bindOrder order.succ .individual = order.succ := by
    exact bindOrder_succ_individual order
  have resultEq :
      max (bindOrder order.succ .individual) order.succ = order.succ :=
    natMaxCongr bindEq rfl
  have line1Raw := star_10_1 universal
    (Eq.mp (congrArg signature.Negation bindEq.symm) negation)
    (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction) body x
  have line1Cast := castAssertionOrder resultEq _ line1Raw
  have line1 : ⊢ᵣ implication negation disjunction
      (star_22_01_successor universal negation disjunction alpha beta)
      (body.instantiate x) :=
    normalizeInclusionInstantiation universal negation disjunction alpha beta x
      bindEq resultEq line1Cast
  rw [star_22_441_body_instantiate negation disjunction alpha beta x] at line1
  have line2 : Derivation (.assertion
      (implication negation disjunction
        (conjunction negation disjunction
          (star_22_01_successor universal negation disjunction alpha beta)
          (star_20_02 alpha x))
        (star_20_02 beta x))) :=
    implicationPresentation negation disjunction _ _ _ line1
  exact line2

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_22_441
#print axioms PM.RamifiedSyntax.star_22_44
#print axioms PM.RamifiedSyntax.star_22_42
#print axioms PM.RamifiedSyntax.star_22_1
#print axioms PM.RamifiedSyntax.star_22_01_unfold
