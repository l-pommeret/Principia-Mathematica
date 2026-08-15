import Principia.Deduction.Star4Ramified

namespace PM.RamifiedSyntax

/-!
# Scope bridge D: the ✱10·28 route

This file tests the route through the propositions surrounding ✱10·23 and
✱10·35 without identifying independently constructed scope trees.  Two
neighbouring propositions, ✱10·24 and ✱10·26, are direct instances of the
primitive ramified calculus.  The next required step, ✱10·21, already meets
the missing scope conversion: its printed members have different root
constructors.
-/

/-- The exact printed AST of ✱10·24, `φy ⊃ (∃x).φx`. -/
def scopeD_star_10_24_formula
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Formula signature real []
      (max matrixOrder (bindOrder matrixOrder argument)) :=
  mixedImplication negation disjunction
    (body.instantiate value) (star_10_01 existential body)

/-- ✱10·24.  Unfolding ✱10·01 makes this exactly primitive ✱9·1. -/
theorem scopeD_star_10_24
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (negation : signature.Negation matrixOrder)
    (disjunction : signature.Disjunction
      (max matrixOrder (bindOrder matrixOrder argument)))
    (body : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    ⊢ᵣ scopeD_star_10_24_formula existential negation disjunction body value := by
  have line1 := Derivation.star_9_1 existential negation disjunction body value
  exact line1

/-- The exact printed AST of ✱10·26,
`(z).(φz ⊃ ψz) ⊃ (φx ⊃ ψx)`. -/
def scopeD_star_10_26_formula
    (universal : signature.Universal argument matrixOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi psi : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    Formula signature real []
      (max (bindOrder matrixOrder argument) matrixOrder) :=
  mixedImplication outerNegation outerDisjunction
    (.always universal
      (implication matrixNegation matrixDisjunction phi psi))
    ((implication matrixNegation matrixDisjunction phi psi).instantiate value)

/-- ✱10·26.  This is primitive ✱10·1 at the implication matrix. -/
theorem scopeD_star_10_26
    (universal : signature.Universal argument matrixOrder)
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction matrixOrder)
    (outerNegation : signature.Negation (bindOrder matrixOrder argument))
    (outerDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) matrixOrder))
    (phi psi : Formula signature real [argument] matrixOrder)
    (value : Term signature real [] argument) :
    ⊢ᵣ scopeD_star_10_26_formula universal matrixNegation
      matrixDisjunction outerNegation outerDisjunction phi psi value := by
  have line1 := Derivation.star_10_1 universal outerNegation outerDisjunction
    (implication matrixNegation matrixDisjunction phi psi) value
  exact line1

/-! ## Exact obstruction met by the ✱10·28 route

The printed members of ✱10·21 are built independently below.  The left
member is `(x).(p ⊃ φx)` and therefore has root `Formula.always`; the right
member is `p ⊃ (x).φx` and therefore has root `Formula.disj` after
unfolding `mixedImplication`.  The order cast on the right does not change
that root.
-/

private def Formula.scopeDCast
    (formula : Formula signature real apparent sourceOrder) :
    {targetOrder : Nat} → sourceOrder = targetOrder →
      Formula signature real apparent targetOrder
  | _, rfl => formula

private inductive Formula.ScopeDRoot where
  | proposition
  | apply
  | neg
  | disj
  | always
  | incompleteScope
  | descriptionScope

private def Formula.scopeDRoot :
    Formula signature real apparent order → Formula.ScopeDRoot
  | .proposition _ => .proposition
  | .apply _ _ => .apply
  | .neg _ _ => .neg
  | .disj _ _ _ => .disj
  | .always _ _ => .always
  | .incompleteScope _ _ _ _ _ _ _ => .incompleteScope
  | .descriptionScope _ _ _ _ _ => .descriptionScope

private theorem Formula.scopeDRoot_scopeDCast
    (formula : Formula signature real apparent sourceOrder)
    (equality : sourceOrder = targetOrder) :
    (formula.scopeDCast equality).scopeDRoot = formula.scopeDRoot := by
  cases equality
  rfl

/-- The independently built left member `(x).(p ⊃ φx)` of ✱10·21. -/
def scopeD_star_10_21_left
    (universal : signature.Universal argument (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .always universal
    (mixedImplication fixedNegation matrixDisjunction
      (p.rename (fun v => .succ v)) phi)

/-- The independently built right member `p ⊃ (x).φx` of ✱10·21. -/
def scopeD_star_10_21_right
    (universal : signature.Universal argument matrixOrder)
    (fixedNegation : signature.Negation fixedOrder)
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  Formula.scopeDCast
    (mixedImplication fixedNegation outerDisjunction p
      (.always universal phi))
    (bindOrderMaxLeft fixedOrder matrixOrder argument)

/-- A kernel-visible audit that ✱10·21 cannot be closed by reflexivity or an
assigned-order cast.  This is not a non-derivability claim: it records the
precise scope-conversion theorem that a genuine derivation must supply. -/
theorem scopeD_star_10_21_tree_mismatch
    (scopeUniversal : signature.Universal argument
      (max fixedOrder matrixOrder))
    (matrixUniversal : signature.Universal argument matrixOrder)
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    scopeD_star_10_21_left scopeUniversal fixedNegation matrixDisjunction
        p phi ≠
      scopeD_star_10_21_right matrixUniversal fixedNegation
        outerDisjunction p phi := by
  intro equality
  have rootEquality := congrArg Formula.scopeDRoot equality
  unfold scopeD_star_10_21_left scopeD_star_10_21_right at rootEquality
  rw [Formula.scopeDRoot_scopeDCast] at rootEquality
  unfold mixedImplication at rootEquality
  cases rootEquality

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.scopeD_star_10_24
#print axioms PM.RamifiedSyntax.scopeD_star_10_26
#print axioms PM.RamifiedSyntax.scopeD_star_10_21_tree_mismatch
