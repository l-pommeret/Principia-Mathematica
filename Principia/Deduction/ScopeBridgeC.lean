import Principia.Deduction.Star10Derived

namespace PM.RamifiedSyntax

/-!
# Scope bridge C: audit from PM's printed demonstrations

This file deliberately does not certify `star_10_23` or `star_10_35`.
It records the derivable prefix of the printed demonstrations and stops at
the first missing scope rewrite.  In particular, no two independently built
members are identified by choosing a common definition.
-/

/-! ## ✱10·23, first printed demonstration

PM starts with ✱4·2 on the scoped matrix `(x).(∼φx ∨ p)`.  That exact
reflexive seed is derivable. -/

theorem scopeBridgeC_star_10_23_reflexive_seed
    (universal : signature.Universal argument (max matrixOrder fixedOrder))
    (matrixNegation : signature.Negation matrixOrder)
    (matrixDisjunction : signature.Disjunction
      (max matrixOrder fixedOrder))
    (outerNegation : signature.Negation
      (bindOrder (max matrixOrder fixedOrder) argument))
    (outerDisjunction : signature.Disjunction
      (bindOrder (max matrixOrder fixedOrder) argument))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    let member := star_10_23_left
      (matrixOrder := matrixOrder) (fixedOrder := fixedOrder)
      universal matrixNegation matrixDisjunction phi p
    ⊢ᵣ star_4_01 outerNegation outerDisjunction member member := by
  dsimp
  have line0 := star_4_2 outerNegation outerDisjunction
    (star_10_23_left
      (matrixOrder := matrixOrder) (fixedOrder := fixedOrder)
      universal matrixNegation matrixDisjunction phi p)
  exact line0

/- The next printed operation is `(✱9·03)` on just one member of the
equivalence.  It would have to replace the root

    Formula.always universal
      (Formula.disj matrixDisjunction
        (Formula.neg matrixNegation phi) (p.rename ...))

by an independently built tree whose root is

    Formula.disj implicationDisjunction
      (Formula.always existential.universal
        (Formula.neg existential.matrixNegation phi)) p

(plus transport across the proved equality of assigned-order indices).
`star_9_03_unfold` and `star_9_03_fold` expose only the first tree.  They do
not state this rewrite, so the first displayed line of ✱10·23 cannot be
continued from `scopeBridgeC_star_10_23_reflexive_seed`.
-/

/-- The uncast constructor tree required after the first use of `(✱9·03)`
in PM's first demonstration of ✱10·23.  This is a target definition only,
not evidence that the preceding `Formula.always` rewrites to it. -/
def scopeBridgeC_star_10_23_after_9_03
    (existential : ExistentialVocabulary signature argument matrixOrder)
    (implicationDisjunction : signature.Disjunction
      (max (bindOrder matrixOrder argument) fixedOrder))
    (phi : Formula signature real [argument] matrixOrder)
    (p : Formula signature real [] fixedOrder) :
    Formula signature real []
      (max (bindOrder matrixOrder argument) fixedOrder) :=
  .disj implicationDisjunction
    (.always existential.universal
      (.neg existential.matrixNegation phi)) p

/-! ## ✱10·21 and ✱10·11 in the alternate demonstration

`star_10_11` is exported by `Star10Derived`.  There is no ramified
`star_10_21` there.  Nor is the missing item a smaller escape hatch:
✱10·21 is the `∼p/p` instance of ✱10·2 and needs ✱9·04 to connect the two
constructor trees below. -/

def scopeBridgeC_star_10_21_left
    (universal : signature.Universal argument (max fixedOrder matrixOrder))
    (fixedNegation : signature.Negation fixedOrder)
    (matrixDisjunction : signature.Disjunction
      (max fixedOrder matrixOrder))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (bindOrder (max fixedOrder matrixOrder) argument) :=
  .always universal
    (.disj matrixDisjunction
      ((Formula.neg fixedNegation p).rename (fun v => .succ v) :
        Formula signature real [argument] fixedOrder) phi)

def scopeBridgeC_star_10_21_right
    (universal : signature.Universal argument matrixOrder)
    (fixedNegation : signature.Negation fixedOrder)
    (outerDisjunction : signature.Disjunction
      (max fixedOrder (bindOrder matrixOrder argument)))
    (p : Formula signature real [] fixedOrder)
    (phi : Formula signature real [argument] matrixOrder) :
    Formula signature real []
      (max fixedOrder (bindOrder matrixOrder argument)) :=
  .disj outerDisjunction (.neg fixedNegation p) (.always universal phi)

/-! ## ✱10·35, derivable prefix

The following specialization keeps a single assigned order and a single
logical vocabulary.  It is enough to check, without any order coercion, that
PM's first two printed steps really are available: ✱3·26 followed by
✱10·11.  The audit then stops at the next citation, `[✱10·23]`.
-/

/-- The contextual form of PM's eliminable conjunction definition ✱3·01.
The existing `conjunction` has the same body but is restricted to formulae
with no apparent variables. -/
def scopeBridgeC_conjunction
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    Formula signature real apparent order :=
  .neg negation
    (sameDisjunction disjunction
      (.neg negation left) (.neg negation right))

theorem scopeBridgeC_conjunction_weakenReal
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real apparent order) :
    (scopeBridgeC_conjunction negation disjunction left right).weakenReal
        (fresh := fresh) =
      scopeBridgeC_conjunction negation disjunction
        left.weakenReal right.weakenReal := by
  unfold scopeBridgeC_conjunction
  change Formula.neg negation
      ((sameDisjunction disjunction
        (Formula.neg negation left) (Formula.neg negation right)).weakenReal) = _
  rw [sameDisjunction_weakenReal]
  rfl

theorem scopeBridgeC_conjunction_substitute
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left right : Formula signature real source order)
    (sigma : Substitution signature real source target) :
    (scopeBridgeC_conjunction negation disjunction left right).substitute sigma =
      scopeBridgeC_conjunction negation disjunction
        (left.substitute sigma) (right.substitute sigma) := by
  unfold scopeBridgeC_conjunction
  change Formula.neg negation
      ((sameDisjunction disjunction
        (Formula.neg negation left) (Formula.neg negation right)).substitute sigma) = _
  rw [sameDisjunction_substitute]
  rfl

def scopeBridgeC_star_10_35_projection_matrix
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order)
    (phi : Formula signature real [argument] order) :
    Formula signature real [argument] order :=
  implication negation disjunction
    (scopeBridgeC_conjunction negation disjunction
      (p.rename (fun v => .succ v) :
        Formula signature real [argument] order) phi)
    (p.rename (fun v => .succ v) :
      Formula signature real [argument] order)

/-- First printed step of ✱10·35: `p . φx ⊃ p` (✱3·26), instantiated
at the fresh real variable required by ✱10·11. -/
theorem scopeBridgeC_star_10_35_line1
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order)
    (phi : Formula signature real [argument] order) :
    ⊢ᵣ (scopeBridgeC_star_10_35_projection_matrix
      negation disjunction p phi).weakenReal.instantiate
        (.real (.zero : Var (argument :: real) argument)) := by
  let value : Term signature (argument :: real) [] argument :=
    .real (.zero : Var (argument :: real) argument)
  have projection :
      ⊢ᵣ implication negation disjunction
        (conjunction negation disjunction p.weakenReal
          (phi.weakenReal.instantiate value)) p.weakenReal :=
    star_3_26 negation disjunction p.weakenReal
      (phi.weakenReal.instantiate value)
  apply Derivation.castAssertion _ projection
  unfold scopeBridgeC_star_10_35_projection_matrix conjunction
  rw [implication_weakenReal, scopeBridgeC_conjunction_weakenReal,
    Formula.instantiate, implication_substitute,
    scopeBridgeC_conjunction_substitute,
    Formula.closed_weakenReal_instantiateSubstitution]
  unfold scopeBridgeC_conjunction
  rfl

/-- Second printed step of ✱10·35: generalization by the existing ✱10·11. -/
theorem scopeBridgeC_star_10_35_line2
    (universal : signature.Universal argument order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order)
    (phi : Formula signature real [argument] order) :
    ⊢ᵣ .always universal
      (scopeBridgeC_star_10_35_projection_matrix
        negation disjunction p phi) := by
  have line1 := scopeBridgeC_star_10_35_line1
    negation disjunction p phi
  have line2 := star_10_11 universal
    (scopeBridgeC_star_10_35_projection_matrix
      negation disjunction p phi) line1
  exact line2

/- The next printed step is

    [✱10·23]  ⊃⊢ : (∃x).p.φx ⊃ p                         (1)

It cannot yet be written from the exported ramified theorems because
`star_10_23` is absent.  The available `star_10_23_left` and
`star_10_23_right` are only the two formula members; neither is a
`Derivation` connecting them.  This is the first unavailable line of the
printed ✱10·35 demonstration, not a claim of non-derivability.
-/

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.scopeBridgeC_star_10_23_reflexive_seed
#print axioms PM.RamifiedSyntax.scopeBridgeC_star_10_35_line1
#print axioms PM.RamifiedSyntax.scopeBridgeC_star_10_35_line2
