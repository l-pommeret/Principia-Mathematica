import Principia.Deduction.Star3Ramified
import Principia.FirstEdition.Volume1.Part1.SectionA.Star4

/-!
# PM I, first edition, ✱4 in the ramified calculus

The propositions in this file live in `PM.RamifiedSyntax.Derivation` and use
the unconditional ramified reconstructions of ✱2 and ✱3.
-/

namespace PM.RamifiedSyntax

private theorem star4_castAssertionOrder
    (equality : sourceOrder = targetOrder)
    (formula : Formula signature real [] sourceOrder) :
    Derivation (.assertion formula) →
      Derivation (.assertion
        (Eq.mp (congrArg (Formula signature real []) equality) formula)) := by
  cases equality
  exact fun derivation => derivation

private theorem star4_detach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons head tail => exact Derivation.star_1_11_same negation disjunction

/-- ✱4·01 (Df): mutual implication is equivalence. -/
def star_4_01
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    Formula signature real [] order :=
  conjunction negation disjunction
    (implication negation disjunction p q)
    (implication negation disjunction q p)

private theorem star4_join
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (hpq : ⊢ᵣ implication negation disjunction p q)
    (hqp : ⊢ᵣ implication negation disjunction q p) :
    ⊢ᵣ star_4_01 negation disjunction p q :=
  star4_detach negation disjunction _ _ hqp
    (star4_detach negation disjunction _ _ hpq
      (star_3_2 negation disjunction
        (implication negation disjunction p q)
        (implication negation disjunction q p)))

private theorem star4_pair
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order)
    (hp : ⊢ᵣ p) (hq : ⊢ᵣ q) :
    ⊢ᵣ conjunction negation disjunction p q :=
  star4_detach negation disjunction _ _ hq
    (star4_detach negation disjunction _ _ hp
      (star_3_2 negation disjunction p q))

private theorem star4_compose
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (hpq : ⊢ᵣ implication negation disjunction p q)
    (hqr : ⊢ᵣ implication negation disjunction q r) :
    ⊢ᵣ implication negation disjunction p r :=
  star4_detach negation disjunction _ _ hpq
    (star4_detach negation disjunction _ _ hqr
      (star_2_05 negation disjunction p q r))

private theorem star4_duplicate
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction p (conjunction negation disjunction p p) :=
  star4_detach negation disjunction _ _
    (star_3_2 negation disjunction p p)
    (star_2_43 negation disjunction p (conjunction negation disjunction p p))

private theorem star4_joinUnder
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order)
    (hpq : ⊢ᵣ implication negation disjunction p q)
    (hpr : ⊢ᵣ implication negation disjunction p r) :
    ⊢ᵣ implication negation disjunction p (conjunction negation disjunction q r) :=
  star4_compose negation disjunction _ _ _ (star4_duplicate negation disjunction p)
    (star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _ hpr
        (star4_detach negation disjunction _ _ hpq
          (star_3_2 negation disjunction
            (implication negation disjunction p q)
            (implication negation disjunction p r))))
      (star_3_47 negation disjunction p p q r))

theorem star_4_01_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    star_4_01 negation disjunction p q =
      conjunction negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction q p) := rfl

/-- ✱4·02 (Df): the unbracketed equivalence chain abbreviates the
conjunction of its two adjacent equivalences. -/
def star_4_02
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Formula signature real [] order :=
  conjunction negation disjunction
    (star_4_01 negation disjunction p q)
    (star_4_01 negation disjunction q r)

theorem star_4_02_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    star_4_02 negation disjunction p q r =
      conjunction negation disjunction
        (star_4_01 negation disjunction p q)
        (star_4_01 negation disjunction q r) := rfl

/-- ✱4·1, `Transp . ✱3·2`, in both directions. -/
theorem star_4_1
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction (Formula.neg negation q) (Formula.neg negation p)) :=
  star4_detach negation disjunction _ _ (star_2_17 negation disjunction p q)
    (star4_detach negation disjunction _ _ (star_2_16 negation disjunction p q)
      (star_3_2 negation disjunction
        (implication negation disjunction
          (implication negation disjunction p q)
          (implication negation disjunction (Formula.neg negation q) (Formula.neg negation p)))
        (implication negation disjunction
          (implication negation disjunction (Formula.neg negation q) (Formula.neg negation p))
          (implication negation disjunction p q))))

/-- ✱4·13, double negation in both directions, packaged by ✱3·2. -/
theorem star_4_13
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction p (Formula.neg negation (Formula.neg negation p)) :=
  star4_detach negation disjunction _ _ (star_2_14 negation disjunction p)
    (star4_detach negation disjunction _ _ (star_2_12 negation disjunction p)
      (star_3_2 negation disjunction
        (implication negation disjunction p (Formula.neg negation (Formula.neg negation p)))
        (implication negation disjunction (Formula.neg negation (Formula.neg negation p)) p)))

/-- ✱4·21, commutation of the two implication factors. -/
theorem star_4_21
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (star_4_01 negation disjunction p q) (star_4_01 negation disjunction q p) :=
  star4_detach negation disjunction _ _
    (star_3_22 negation disjunction
      (implication negation disjunction q p) (implication negation disjunction p q))
    (star4_detach negation disjunction _ _
      (star_3_22 negation disjunction
        (implication negation disjunction p q) (implication negation disjunction q p))
      (star_3_2 negation disjunction
        (implication negation disjunction (star_4_01 negation disjunction p q)
          (star_4_01 negation disjunction q p))
        (implication negation disjunction (star_4_01 negation disjunction q p)
          (star_4_01 negation disjunction p q))))

/-- ✱4·3, the two instances of ✱3·22 cited by PM. -/
theorem star_4_3
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (conjunction negation disjunction p q) (conjunction negation disjunction q p) :=
  star4_detach negation disjunction _ _ (star_3_22 negation disjunction q p)
    (star4_detach negation disjunction _ _ (star_3_22 negation disjunction p q)
      (star_3_2 negation disjunction
        (implication negation disjunction (conjunction negation disjunction p q)
          (conjunction negation disjunction q p))
        (implication negation disjunction (conjunction negation disjunction q p)
          (conjunction negation disjunction p q))))

/-- ✱4·33, `Assoc` in each direction, packaged by ✱3·2. -/
theorem star_4_33
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (sameDisjunction disjunction (sameDisjunction disjunction p q) r)
      (sameDisjunction disjunction p (sameDisjunction disjunction q r)) :=
  star4_detach negation disjunction _ _ (star_2_31 negation disjunction p q r)
    (star4_detach negation disjunction _ _ (star_2_32 negation disjunction p q r)
      (star_3_2 negation disjunction
        (implication negation disjunction
          (sameDisjunction disjunction (sameDisjunction disjunction p q) r)
          (sameDisjunction disjunction p (sameDisjunction disjunction q r)))
        (implication negation disjunction
          (sameDisjunction disjunction p (sameDisjunction disjunction q r))
          (sameDisjunction disjunction (sameDisjunction disjunction p q) r))))

/-- ✱4·34 (Df): the unbracketed conjunction abbreviates the
left-associated form. -/
def star_4_34
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Formula signature real [] order :=
  conjunction negation disjunction (conjunction negation disjunction p q) r

theorem star_4_34_unfold
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    star_4_34 negation disjunction p q r =
      conjunction negation disjunction (conjunction negation disjunction p q) r := rfl

/-- ✱4·5, reflexivity after unfolding the definition of conjunction. -/
theorem star_4_5
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (conjunction negation disjunction p q)
      (Formula.neg negation
        (sameDisjunction disjunction (Formula.neg negation p) (Formula.neg negation q))) :=
  star4_join negation disjunction _ _
    (star_2_08 negation disjunction (conjunction negation disjunction p q))
    (star_2_08 negation disjunction (conjunction negation disjunction p q))

/-- ✱4·8, `Abs` and `Simp`, packaged as an equivalence. -/
theorem star_4_8
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (implication negation disjunction p (Formula.neg negation p))
      (Formula.neg negation p) :=
  star4_join negation disjunction _ _
    (star_2_01 negation disjunction p)
    (star_2_02 negation disjunction p (Formula.neg negation p))

/-- ✱4·81, the dual `Taut`/`Simp` equivalence. -/
theorem star_4_81
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (implication negation disjunction (Formula.neg negation p) p) p :=
  star4_join negation disjunction _ _
    (star_2_18 negation disjunction p)
    (star_2_02 negation disjunction (Formula.neg negation p) p)

/-- ✱4·24, idempotence of conjunction. -/
theorem star_4_24
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction p (conjunction negation disjunction p p) :=
  star4_join negation disjunction _ _
    (star4_detach negation disjunction _ _ (star_3_2 negation disjunction p p)
      (star_2_43 negation disjunction p (conjunction negation disjunction p p)))
    (star_3_26 negation disjunction p p)

/-- ✱4·25, idempotence of disjunction (`Add . Taut`). -/
theorem star_4_25
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction p (sameDisjunction disjunction p p) :=
  star4_join negation disjunction _ _
    (Derivation.star_1_3_same negation disjunction p p)
    (Derivation.star_1_2 negation disjunction p)

/-- ✱4·22, transitivity of equivalence, following PM's cited chain. -/
theorem star_4_22
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction
      (conjunction negation disjunction (star_4_01 negation disjunction p q)
        (star_4_01 negation disjunction q r))
      (star_4_01 negation disjunction p r) := by
  let zz := conjunction negation disjunction (star_4_01 negation disjunction p q)
    (star_4_01 negation disjunction q r)
  have z1 : ⊢ᵣ implication negation disjunction zz
      (conjunction negation disjunction (implication negation disjunction p q)
        (implication negation disjunction q r)) :=
    star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _
        (star_3_26 negation disjunction (implication negation disjunction q r)
          (implication negation disjunction r q))
        (star4_detach negation disjunction _ _
          (star_3_26 negation disjunction (implication negation disjunction p q)
            (implication negation disjunction q p))
          (star_3_2 negation disjunction
            (implication negation disjunction (star_4_01 negation disjunction p q)
              (implication negation disjunction p q))
            (implication negation disjunction (star_4_01 negation disjunction q r)
              (implication negation disjunction q r)))))
      (star_3_47 negation disjunction (star_4_01 negation disjunction p q)
        (star_4_01 negation disjunction q r) (implication negation disjunction p q)
        (implication negation disjunction q r))
  have zA : ⊢ᵣ implication negation disjunction zz
      (implication negation disjunction p r) :=
    star4_detach negation disjunction _ _ (star_3_33 negation disjunction p q r)
      (star4_detach negation disjunction _ _ z1
        (star_2_06 negation disjunction zz
          (conjunction negation disjunction (implication negation disjunction p q)
            (implication negation disjunction q r))
          (implication negation disjunction p r)))
  have w1 : ⊢ᵣ implication negation disjunction zz
      (conjunction negation disjunction (implication negation disjunction q p)
        (implication negation disjunction r q)) :=
    star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _
        (star_3_27 negation disjunction (implication negation disjunction q r)
          (implication negation disjunction r q))
        (star4_detach negation disjunction _ _
          (star_3_27 negation disjunction (implication negation disjunction p q)
            (implication negation disjunction q p))
          (star_3_2 negation disjunction
            (implication negation disjunction (star_4_01 negation disjunction p q)
              (implication negation disjunction q p))
            (implication negation disjunction (star_4_01 negation disjunction q r)
              (implication negation disjunction r q)))))
      (star_3_47 negation disjunction (star_4_01 negation disjunction p q)
        (star_4_01 negation disjunction q r) (implication negation disjunction q p)
        (implication negation disjunction r q))
  have w2 : ⊢ᵣ implication negation disjunction zz
      (conjunction negation disjunction (implication negation disjunction r q)
        (implication negation disjunction q p)) :=
    star4_detach negation disjunction _ _
      (star_3_22 negation disjunction (implication negation disjunction q p)
        (implication negation disjunction r q))
      (star4_detach negation disjunction _ _ w1
        (star_2_06 negation disjunction zz _ _))
  have zB : ⊢ᵣ implication negation disjunction zz
      (implication negation disjunction r p) :=
    star4_detach negation disjunction _ _ (star_3_33 negation disjunction r q p)
      (star4_detach negation disjunction _ _ w2
        (star_2_06 negation disjunction zz _ _))
  exact star4_detach negation disjunction _ _
    (star4_detach negation disjunction _ _ zB
      (star4_detach negation disjunction _ _ zA
        (star_3_2 negation disjunction
          (implication negation disjunction zz (implication negation disjunction p r))
          (implication negation disjunction zz (implication negation disjunction r p)))))
    (star_3_43 negation disjunction zz (implication negation disjunction p r)
      (implication negation disjunction r p))

/-- ✱4·2.  This is PM's printed `Id . ✱3·2` proof. -/
theorem star_4_2
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction p p := by
  have line1 := star_2_08 negation disjunction p
  exact star4_join negation disjunction p p line1 line1

/-- ✱4·31, PM's printed `Perm` proof in both directions, packaged by ✱3·2. -/
theorem star_4_31
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (sameDisjunction disjunction p q)
      (sameDisjunction disjunction q p) := by
  have line1 := Derivation.star_1_4_same negation disjunction p q
  have line2 := Derivation.star_1_4_same negation disjunction q p
  exact star4_join negation disjunction _ _ line1 line2

/-- ✱4·71, following PM's numbered implication/equivalence chain. -/
theorem star_4_71
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (implication negation disjunction p q)
      (star_4_01 negation disjunction p (conjunction negation disjunction p q)) := by
  let a := implication negation disjunction p (conjunction negation disjunction p q)
  have line1 : ⊢ᵣ implication negation disjunction a
      (star_4_01 negation disjunction p (conjunction negation disjunction p q)) :=
    star4_joinUnder negation disjunction _ _ _
      (star_2_08 negation disjunction a)
      (star4_detach negation disjunction _ _
        (star_3_26 negation disjunction p q)
        (star_2_02 negation disjunction a
          (implication negation disjunction (conjunction negation disjunction p q) p)))
  have line2 : ⊢ᵣ implication negation disjunction
      (star_4_01 negation disjunction p (conjunction negation disjunction p q)) a :=
    star_3_26 negation disjunction a
      (implication negation disjunction (conjunction negation disjunction p q) p)
  have line3 : ⊢ᵣ star_4_01 negation disjunction a
      (star_4_01 negation disjunction p (conjunction negation disjunction p q)) :=
    star4_join negation disjunction _ _ line1 line2
  have line4forward : ⊢ᵣ implication negation disjunction
      (implication negation disjunction p q) a :=
    star4_detach negation disjunction _ _
      (star_3_2 negation disjunction p q)
      (star_2_77 negation disjunction p q (conjunction negation disjunction p q))
  have line4backward : ⊢ᵣ implication negation disjunction a
      (implication negation disjunction p q) :=
    star4_compose negation disjunction _ _ _ (star_2_08 negation disjunction a)
      (star4_detach negation disjunction _ _
        (star_3_27 negation disjunction p q)
        (star_2_05 negation disjunction p (conjunction negation disjunction p q) q))
  have line4 : ⊢ᵣ star_4_01 negation disjunction
      (implication negation disjunction p q) a :=
    star4_join negation disjunction _ _ line4forward line4backward
  exact star4_detach negation disjunction _ _
    (star4_detach negation disjunction _ _ line3
      (star4_detach negation disjunction _ _ line4
        (star_3_2 negation disjunction
          (star_4_01 negation disjunction (implication negation disjunction p q) a)
          (star_4_01 negation disjunction a
            (star_4_01 negation disjunction p (conjunction negation disjunction p q))))))
    (star_4_22 negation disjunction (implication negation disjunction p q) a
      (star_4_01 negation disjunction p (conjunction negation disjunction p q)))

/-- ✱4·73, PM's `Simp . ✱4·71` proof. -/
theorem star_4_73
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction q
      (star_4_01 negation disjunction p (conjunction negation disjunction p q)) := by
  have line1 : ⊢ᵣ implication negation disjunction q
      (implication negation disjunction p q) :=
    star_2_02 negation disjunction p q
  have line2 : ⊢ᵣ implication negation disjunction
      (implication negation disjunction p q)
      (star_4_01 negation disjunction p (conjunction negation disjunction p q)) :=
    star4_detach negation disjunction _ _ (star_4_71 negation disjunction p q)
      (star_3_26 negation disjunction _ _)
  exact star4_compose negation disjunction _ _ _ line1 line2

/-- ✱4·38, substitution of equivalents in a conjunction. -/
theorem star_4_38
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r s : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction
      (conjunction negation disjunction (star_4_01 negation disjunction p r)
        (star_4_01 negation disjunction q s))
      (star_4_01 negation disjunction (conjunction negation disjunction p q)
        (conjunction negation disjunction r s)) := by
  let h := conjunction negation disjunction (star_4_01 negation disjunction p r)
    (star_4_01 negation disjunction q s)
  have hp := star_3_26 negation disjunction
    (star_4_01 negation disjunction p r) (star_4_01 negation disjunction q s)
  have hq := star_3_27 negation disjunction
    (star_4_01 negation disjunction p r) (star_4_01 negation disjunction q s)
  have hpr := star4_compose negation disjunction _ _ _ hp
    (star_3_26 negation disjunction (implication negation disjunction p r)
      (implication negation disjunction r p))
  have hrp := star4_compose negation disjunction _ _ _ hp
    (star_3_27 negation disjunction (implication negation disjunction p r)
      (implication negation disjunction r p))
  have hqs := star4_compose negation disjunction _ _ _ hq
    (star_3_26 negation disjunction (implication negation disjunction q s)
      (implication negation disjunction s q))
  have hsq := star4_compose negation disjunction _ _ _ hq
    (star_3_27 negation disjunction (implication negation disjunction q s)
      (implication negation disjunction s q))
  have forward := star4_compose negation disjunction _ _ _
    (star4_joinUnder negation disjunction h _ _ hpr hqs)
    (star_3_47 negation disjunction p q r s)
  have backward := star4_compose negation disjunction _ _ _
    (star4_joinUnder negation disjunction h _ _ hrp hsq)
    (star_3_47 negation disjunction r s p q)
  exact star4_joinUnder negation disjunction h _ _ forward backward

/-- ✱4·76, the equivalence between paired implications and implication to a pair. -/
theorem star_4_76
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (conjunction negation disjunction (implication negation disjunction p q)
        (implication negation disjunction p r))
      (implication negation disjunction p (conjunction negation disjunction q r)) := by
  let a := conjunction negation disjunction (implication negation disjunction p q)
    (implication negation disjunction p r)
  let b := implication negation disjunction p (conjunction negation disjunction q r)
  have duplicate := star4_duplicate negation disjunction p
  have underA := star4_detach negation disjunction _ _ duplicate
    (star_2_02 negation disjunction a
      (implication negation disjunction p (conjunction negation disjunction p p)))
  have lifted := star4_detach negation disjunction _ _ underA
    (star_2_83 negation disjunction a p (conjunction negation disjunction p p)
      (conjunction negation disjunction q r))
  have forward : ⊢ᵣ implication negation disjunction a b :=
    star4_detach negation disjunction _ _ (star_3_47 negation disjunction p p q r) lifted
  have bb : ⊢ᵣ implication negation disjunction b b := star_2_08 negation disjunction b
  have qpart : ⊢ᵣ implication negation disjunction b
      (implication negation disjunction p q) :=
    star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _ (star_3_26 negation disjunction q r)
        (star_2_02 negation disjunction b
          (implication negation disjunction (conjunction negation disjunction q r) q)))
      (star4_detach negation disjunction _ _ bb
        (star_2_83 negation disjunction b p (conjunction negation disjunction q r) q))
  have rpart : ⊢ᵣ implication negation disjunction b
      (implication negation disjunction p r) :=
    star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _ (star_3_27 negation disjunction q r)
        (star_2_02 negation disjunction b
          (implication negation disjunction (conjunction negation disjunction q r) r)))
      (star4_detach negation disjunction _ _ bb
        (star_2_83 negation disjunction b p (conjunction negation disjunction q r) r))
  have backward : ⊢ᵣ implication negation disjunction b a :=
    star4_joinUnder negation disjunction b _ _ qpart rpart
  exact star4_join negation disjunction a b forward backward

/-- ✱4·12, the reciprocal negated equivalences. -/
theorem star_4_12
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (star_4_01 negation disjunction p (Formula.neg negation q))
      (star_4_01 negation disjunction q (Formula.neg negation p)) := by
  have a1 := star_2_03 negation disjunction p q
  have a2 := star_2_15 negation disjunction q p
  have haPair := star4_detach negation disjunction _ _ a2
    (star4_detach negation disjunction _ _ a1
      (star_3_2 negation disjunction
        (implication negation disjunction (implication negation disjunction p (Formula.neg negation q))
          (implication negation disjunction q (Formula.neg negation p)))
        (implication negation disjunction (implication negation disjunction (Formula.neg negation q) p)
          (implication negation disjunction (Formula.neg negation p) q))))
  have forward := star4_detach negation disjunction _ _ haPair
    (star_3_47 negation disjunction
      (implication negation disjunction p (Formula.neg negation q))
      (implication negation disjunction (Formula.neg negation q) p)
      (implication negation disjunction q (Formula.neg negation p))
      (implication negation disjunction (Formula.neg negation p) q))
  have b1 := star_2_03 negation disjunction q p
  have b2 := star_2_15 negation disjunction p q
  have hbPair := star4_detach negation disjunction _ _ b2
    (star4_detach negation disjunction _ _ b1
      (star_3_2 negation disjunction
        (implication negation disjunction (implication negation disjunction q (Formula.neg negation p))
          (implication negation disjunction p (Formula.neg negation q)))
        (implication negation disjunction (implication negation disjunction (Formula.neg negation p) q)
          (implication negation disjunction (Formula.neg negation q) p))))
  have backward := star4_detach negation disjunction _ _ hbPair
    (star_3_47 negation disjunction
      (implication negation disjunction q (Formula.neg negation p))
      (implication negation disjunction (Formula.neg negation p) q)
      (implication negation disjunction p (Formula.neg negation q))
      (implication negation disjunction (Formula.neg negation q) p))
  exact star4_join negation disjunction _ _ forward backward

private def star4_reading
    (printed : String) (formula : Formula signature real [] order) :
    ClaimReading signature real where
  printed := printed
  parsed := .assertion formula

/-- Audited scope reading of ✱4·36. -/
def star_4_36_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :=
  star4_reading "✱4·36.  ⊢ :. p ≡ q . ⊃ : p . r . ≡ . q . r"
    (implication negation disjunction (star_4_01 negation disjunction p q)
      (star_4_01 negation disjunction
        (conjunction negation disjunction p r)
        (conjunction negation disjunction q r)))

/-- ✱4·36, following PM's printed `Fact . ✱3·47` route. -/
theorem star_4_36
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction (star_4_01 negation disjunction p q)
      (star_4_01 negation disjunction
        (conjunction negation disjunction p r)
        (conjunction negation disjunction q r)) := by
  let e := star_4_01 negation disjunction p q
  have line1 : ⊢ᵣ implication negation disjunction e
      (implication negation disjunction
        (conjunction negation disjunction p r)
        (conjunction negation disjunction q r)) :=
    star4_compose negation disjunction _ _ _
      (star4_joinUnder negation disjunction e _ _
        (star_3_26 negation disjunction
          (implication negation disjunction p q)
          (implication negation disjunction q p))
        (star4_detach negation disjunction _ _
          (star_2_08 negation disjunction r)
          (star_2_02 negation disjunction e
            (implication negation disjunction r r))))
      (star_3_47 negation disjunction p r q r)
  have line2 : ⊢ᵣ implication negation disjunction e
      (implication negation disjunction
        (conjunction negation disjunction q r)
        (conjunction negation disjunction p r)) :=
    star4_compose negation disjunction _ _ _
      (star4_joinUnder negation disjunction e _ _
        (star_3_27 negation disjunction
          (implication negation disjunction p q)
          (implication negation disjunction q p))
        (star4_detach negation disjunction _ _
          (star_2_08 negation disjunction r)
          (star_2_02 negation disjunction e
            (implication negation disjunction r r))))
      (star_3_47 negation disjunction q r p r)
  exact star4_joinUnder negation disjunction e _ _ line1 line2

/-- Audited scope reading of ✱4·37. -/
def star_4_37_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :=
  star4_reading "✱4·37.  ⊢ :. p ≡ q . ⊃ : p ∨ r . ≡ . q ∨ r"
    (implication negation disjunction (star_4_01 negation disjunction p q)
      (star_4_01 negation disjunction
        (sameDisjunction disjunction p r) (sameDisjunction disjunction q r)))

/-- ✱4·37, following PM's printed `Sum . ✱3·47` route. -/
theorem star_4_37
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction (star_4_01 negation disjunction p q)
      (star_4_01 negation disjunction
        (sameDisjunction disjunction p r) (sameDisjunction disjunction q r)) := by
  let e := star_4_01 negation disjunction p q
  have line1 :
      ⊢ᵣ implication negation disjunction e
        (implication negation disjunction p q) :=
    star_3_26 negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction q p)
  let pairEq := natMaxSelf order
  let consequentEq := natMaxCongr pairEq pairEq
  let resultEq := natMaxCongr pairEq consequentEq
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation pairEq.symm) negation
  let consequentDisjunction :=
    Eq.mp (congrArg signature.Disjunction consequentEq.symm) disjunction
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction
  let antecedent := mixedImplication negation pairDisjunction p q
  let leftSum := Formula.disj pairDisjunction r p
  let rightSum := Formula.disj pairDisjunction r q
  let consequence := mixedImplication pairNegation consequentDisjunction
    leftSum rightSum
  let rawSum := mixedImplication pairNegation outerDisjunction
    antecedent consequence
  have line2a : Derivation (.assertion rawSum) :=
    Derivation.star_1_6 negation pairDisjunction pairNegation pairNegation
      pairDisjunction pairDisjunction consequentDisjunction outerDisjunction
      r p q
  have line2b : Derivation (.assertion
      (Eq.mp (congrArg (Formula signature real []) resultEq) rawSum)) :=
    star4_castAssertionOrder resultEq rawSum line2a
  have line2 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction p q)
        (implication negation disjunction
          (sameDisjunction disjunction r p)
          (sameDisjunction disjunction r q)) :=
    Derivation.castAssertion
      (star_1_6_normalizeSameOrder negation disjunction r p q).symm line2b
  have line3 := star4_compose negation disjunction _ _ _ line1 line2
  have line4 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction
          (sameDisjunction disjunction r p)
          (sameDisjunction disjunction r q))
        (implication negation disjunction
          (sameDisjunction disjunction p r)
          (sameDisjunction disjunction r q)) :=
    star4_detach negation disjunction _ _
      (Derivation.star_1_4_same negation disjunction p r)
      (star_2_06 negation disjunction
        (sameDisjunction disjunction p r)
        (sameDisjunction disjunction r p)
        (sameDisjunction disjunction r q))
  have line5 :
      ⊢ᵣ implication negation disjunction
        (implication negation disjunction
          (sameDisjunction disjunction p r)
          (sameDisjunction disjunction r q))
        (implication negation disjunction
          (sameDisjunction disjunction p r)
          (sameDisjunction disjunction q r)) :=
    star4_detach negation disjunction _ _
      (Derivation.star_1_4_same negation disjunction r q)
      (star_2_05 negation disjunction
        (sameDisjunction disjunction p r)
        (sameDisjunction disjunction r q)
        (sameDisjunction disjunction q r))
  have line6 := star4_compose negation disjunction _ _ _
    (star4_compose negation disjunction _ _ _ line3 line4) line5
  have line7 :
      ⊢ᵣ implication negation disjunction e
        (conjunction negation disjunction
          (implication negation disjunction q p)
          (implication negation disjunction p q)) :=
    star_3_22 negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction q p)
  have line8 :
      ⊢ᵣ implication negation disjunction e
        (conjunction negation disjunction
          (implication negation disjunction q p)
          (implication negation disjunction r r)) :=
    star4_joinUnder negation disjunction e _ _
      (star4_compose negation disjunction _ _ _ line7
        (star_3_26 negation disjunction
          (implication negation disjunction q p)
          (implication negation disjunction p q)))
      (star4_detach negation disjunction _ _
        (star_2_08 negation disjunction r)
        (star_2_02 negation disjunction e
          (implication negation disjunction r r)))
  have line9 := star4_compose negation disjunction _ _ _ line8
    (star_3_48 negation disjunction q r p r)
  exact star4_joinUnder negation disjunction e _ _ line6 line9

/-- Audited scope reading of ✱4·39. -/
def star_4_39_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r s : Formula signature real [] order) :=
  star4_reading "✱4·39.  ⊢ :. p ≡ r . q ≡ s . ⊃ : p ∨ q . ≡ . r ∨ s   [✱3·48·47 . ✱4·32 . ✱3·22]"
    (implication negation disjunction
      (conjunction negation disjunction (star_4_01 negation disjunction p r)
        (star_4_01 negation disjunction q s))
      (star_4_01 negation disjunction
        (sameDisjunction disjunction p q) (sameDisjunction disjunction r s)))

/-- ✱4·39, following PM's printed `✱3·48 . ✱4·32 . ✱3·22` route. -/
theorem star_4_39
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r s : Formula signature real [] order) :
    ⊢ᵣ implication negation disjunction
      (conjunction negation disjunction (star_4_01 negation disjunction p r)
        (star_4_01 negation disjunction q s))
      (star_4_01 negation disjunction
        (sameDisjunction disjunction p q) (sameDisjunction disjunction r s)) := by
  let h := conjunction negation disjunction (star_4_01 negation disjunction p r)
    (star_4_01 negation disjunction q s)
  have line1 := star4_compose negation disjunction _ _ _
    (star4_joinUnder negation disjunction h _ _
      (star4_compose negation disjunction _ _ _
        (star_3_26 negation disjunction _ _) (star_3_26 negation disjunction _ _))
      (star4_compose negation disjunction _ _ _
        (star_3_27 negation disjunction _ _) (star_3_26 negation disjunction _ _)))
    (star_3_48 negation disjunction p q r s)
  have line2 := star4_compose negation disjunction _ _ _
    (star4_joinUnder negation disjunction h _ _
      (star4_compose negation disjunction _ _ _
        (star_3_26 negation disjunction _ _) (star_3_27 negation disjunction _ _))
      (star4_compose negation disjunction _ _ _
        (star_3_27 negation disjunction _ _) (star_3_27 negation disjunction _ _)))
    (star_3_48 negation disjunction r s p q)
  exact star4_joinUnder negation disjunction h _ _ line1 line2

/-- Audited scope reading of ✱4·45. -/
def star_4_45_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :=
  star4_reading "✱4·45.  ⊢ : p . ≡ . p . p ∨ q   [✱3·26 . ✱2·2]"
    (star_4_01 negation disjunction p
      (conjunction negation disjunction p (sameDisjunction disjunction p q)))

/-- ✱4·45, exactly PM's `✱3·26 . ✱2·2` justification. -/
theorem star_4_45
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction p
      (conjunction negation disjunction p (sameDisjunction disjunction p q)) := by
  have line1 : ⊢ᵣ implication negation disjunction p
      (conjunction negation disjunction p (sameDisjunction disjunction p q)) :=
    star4_joinUnder negation disjunction p _ _
      (star_2_08 negation disjunction p)
      (star_2_2 negation disjunction p q)
  have line2 := star_3_26 negation disjunction p (sameDisjunction disjunction p q)
  exact star4_join negation disjunction _ _ line1 line2

/-- Audited scope reading of ✱4·44. -/
def star_4_44_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :=
  star4_reading "✱4·44.  ⊢ : p . ≡ : p . ∨ . p . q"
    (star_4_01 negation disjunction p
      (sameDisjunction disjunction p (conjunction negation disjunction p q)))

/-- ✱4·44, following PM's two numbered lines. -/
theorem star_4_44
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction p
      (sameDisjunction disjunction p (conjunction negation disjunction p q)) := by
  have line1 : ⊢ᵣ implication negation disjunction p
      (sameDisjunction disjunction p (conjunction negation disjunction p q)) :=
    star_2_2 negation disjunction p (conjunction negation disjunction p q)
  have line2 : ⊢ᵣ implication negation disjunction
      (sameDisjunction disjunction p (conjunction negation disjunction p q)) p :=
    star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _
        (star_3_26 negation disjunction p q)
        (star4_detach negation disjunction _ _
          (star_2_08 negation disjunction p)
          (star_3_2 negation disjunction
            (implication negation disjunction p p)
            (implication negation disjunction (conjunction negation disjunction p q) p))))
      (star_3_44 negation disjunction p p (conjunction negation disjunction p q))
  exact star4_join negation disjunction _ _ line1 line2

/-! The following propositions complete the directly reusable part of PM's
printed ✱4 chain.  The names `line1`, ... retain the order of the displayed
or bracketed PM justification. -/

section

variable {signature : Signature} {real : Context} {order : Nat}
variable (negation : signature.Negation order)
variable (disjunction : signature.Disjunction order)

local prefix:max "∼ᵣ" => Formula.neg negation
local infixr:55 " ∨ᵣ " => sameDisjunction disjunction
local infixr:54 " ⊃ᵣ " => implication negation disjunction
local infixr:56 " ∧ᵣ " => conjunction negation disjunction
local infixr:53 " ≡ᵣ " => star_4_01 negation disjunction

def star_4_51_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·51.  ⊢ : ∼(p . q) . ≡ . ∼p ∨ ∼q"
    ((∼ᵣ (p ∧ᵣ q)) ≡ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_51 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ (p ∧ᵣ q)) ≡ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))) := by
  let c := p ∧ᵣ q
  let x := (∼ᵣ p) ∨ᵣ (∼ᵣ q)
  have line1 : ⊢ᵣ (c ≡ᵣ (∼ᵣ x)) :=
    star_4_5 negation disjunction p q
  have line2 : ⊢ᵣ (x ≡ᵣ (∼ᵣ c)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_12 negation disjunction c x)
        (star_3_26 negation disjunction
          ((c ≡ᵣ (∼ᵣ x)) ⊃ᵣ (x ≡ᵣ (∼ᵣ c)))
          ((x ≡ᵣ (∼ᵣ c)) ⊃ᵣ (c ≡ᵣ (∼ᵣ x)))))
  exact star4_detach negation disjunction _ _ line2
    (star_3_22 negation disjunction
      (x ⊃ᵣ (∼ᵣ c)) ((∼ᵣ c) ⊃ᵣ x))

def star_4_72_reading
    (p q : Formula signature real [] order) :=
  star4_reading "✱4·72.  ⊢ : p ⊃ q . ≡ : q . ≡ . p ∨ q"
    ((p ⊃ᵣ q) ≡ᵣ (q ≡ᵣ (p ∨ᵣ q)))

theorem star_4_72
    (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ≡ᵣ (q ≡ᵣ (p ∨ᵣ q))) := by
  let a := p ⊃ᵣ q
  have line1 : ⊢ᵣ (a ⊃ᵣ (q ⊃ᵣ (p ∨ᵣ q))) :=
    star4_detach negation disjunction _ _
      (Derivation.star_1_3_same negation disjunction p q)
      (star_2_02 negation disjunction a (q ⊃ᵣ (p ∨ᵣ q)))
  have line2 : ⊢ᵣ (a ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) :=
    star4_compose negation disjunction _ _ _
      (star4_joinUnder negation disjunction a _ _
        (star_2_08 negation disjunction a)
        (star4_detach negation disjunction _ _ (star_2_08 negation disjunction q)
          (star_2_02 negation disjunction a (q ⊃ᵣ q))))
      (star_3_44 negation disjunction q p q)
  have line3 : ⊢ᵣ (a ⊃ᵣ (q ≡ᵣ (p ∨ᵣ q))) :=
    star4_joinUnder negation disjunction a _ _ line1 line2
  have line4 : ⊢ᵣ ((q ≡ᵣ (p ∨ᵣ q)) ⊃ᵣ a) :=
    star4_compose negation disjunction _ _ _
      (star_3_27 negation disjunction (q ⊃ᵣ (p ∨ᵣ q)) ((p ∨ᵣ q) ⊃ᵣ q))
      (star4_detach negation disjunction _ _ (star_2_2 negation disjunction p q)
        (star_2_06 negation disjunction p (p ∨ᵣ q) q))
  exact star4_join negation disjunction _ _ line3 line4

def star_4_82_reading
    (p q : Formula signature real [] order) :=
  star4_reading "✱4·82.  ⊢ : p ⊃ q . p ⊃ ∼q . ≡ . ∼p"
    (((p ⊃ᵣ q) ∧ᵣ (p ⊃ᵣ ∼ᵣ q)) ≡ᵣ ∼ᵣ p)

theorem star_4_82
    (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ∧ᵣ (p ⊃ᵣ ∼ᵣ q)) ≡ᵣ ∼ᵣ p) := by
  let e := (p ⊃ᵣ q) ∧ᵣ (p ⊃ᵣ ∼ᵣ q)
  have line1 : ⊢ᵣ (e ⊃ᵣ ∼ᵣ p) :=
    star4_detach negation disjunction _ _ (star_2_65 negation disjunction p q)
      (star_3_31 negation disjunction (p ⊃ᵣ q) (p ⊃ᵣ ∼ᵣ q) (∼ᵣ p))
  have line2 : ⊢ᵣ ((∼ᵣ p) ⊃ᵣ e) :=
    star4_joinUnder negation disjunction (∼ᵣ p) _ _
      (star_2_21 negation disjunction p q)
      (star_2_21 negation disjunction p (∼ᵣ q))
  exact star4_join negation disjunction _ _ line1 line2

def star_4_83_reading
    (p q : Formula signature real [] order) :=
  star4_reading "✱4·83.  ⊢ : p ⊃ q . ∼p ⊃ q . ≡ . q"
    (((p ⊃ᵣ q) ∧ᵣ ((∼ᵣ p) ⊃ᵣ q)) ≡ᵣ q)

theorem star_4_83
    (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ∧ᵣ ((∼ᵣ p) ⊃ᵣ q)) ≡ᵣ q) := by
  let e := (p ⊃ᵣ q) ∧ᵣ ((∼ᵣ p) ⊃ᵣ q)
  have line1 : ⊢ᵣ (e ⊃ᵣ q) :=
    star4_detach negation disjunction _ _ (star_2_61 negation disjunction p q)
      (star_3_31 negation disjunction (p ⊃ᵣ q) ((∼ᵣ p) ⊃ᵣ q) q)
  have line2 : ⊢ᵣ (q ⊃ᵣ e) :=
    star4_joinUnder negation disjunction q _ _
      (star_2_02 negation disjunction p q)
      (star_2_02 negation disjunction (∼ᵣ p) q)
  exact star4_join negation disjunction _ _ line1 line2

def star_4_84_reading
    (p q r : Formula signature real [] order) :=
  star4_reading "✱4·84.  ⊢ :. p ≡ q . ⊃ : p ⊃ r . ≡ . q ⊃ r"
    ((p ≡ᵣ q) ⊃ᵣ ((p ⊃ᵣ r) ≡ᵣ (q ⊃ᵣ r)))

theorem star_4_84
    (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ≡ᵣ q) ⊃ᵣ ((p ⊃ᵣ r) ≡ᵣ (q ⊃ᵣ r))) := by
  let e := p ≡ᵣ q
  have line1 := star4_compose negation disjunction _ _ _
    (star_3_27 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ p))
    (star_2_06 negation disjunction q p r)
  have line2 := star4_compose negation disjunction _ _ _
    (star_3_26 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ p))
    (star_2_06 negation disjunction p q r)
  exact star4_joinUnder negation disjunction e _ _ line1 line2

def star_4_85_reading
    (p q r : Formula signature real [] order) :=
  star4_reading "✱4·85.  ⊢ :. p ≡ q . ⊃ : r ⊃ p . ≡ . r ⊃ q   [✱2·05 . ✱3·47]"
    ((p ≡ᵣ q) ⊃ᵣ ((r ⊃ᵣ p) ≡ᵣ (r ⊃ᵣ q)))

theorem star_4_85
    (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ≡ᵣ q) ⊃ᵣ ((r ⊃ᵣ p) ≡ᵣ (r ⊃ᵣ q))) := by
  let e := p ≡ᵣ q
  have line1 := star4_compose negation disjunction _ _ _
    (star_3_26 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ p))
    (star_2_05 negation disjunction r p q)
  have line2 := star4_compose negation disjunction _ _ _
    (star_3_27 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ p))
    (star_2_05 negation disjunction r q p)
  exact star4_joinUnder negation disjunction e _ _ line1 line2

def star_4_4_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·4.  ⊢ : p . q ∨ r . ≡ : p . q . ∨ . p . r"
    ((p ∧ᵣ (q ∨ᵣ r)) ≡ᵣ ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_4 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∧ᵣ (q ∨ᵣ r)) ≡ᵣ ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r))) := by
  have line1 : ⊢ᵣ (p ⊃ᵣ ((q ∨ᵣ r) ⊃ᵣ ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r)))) :=
    star4_compose negation disjunction _ _ _
      (star4_joinUnder negation disjunction p _ _
        (star_3_2 negation disjunction p q) (star_3_2 negation disjunction p r))
      (star_3_48 negation disjunction q r (p ∧ᵣ q) (p ∧ᵣ r))
  have line2 : ⊢ᵣ ((p ∧ᵣ (q ∨ᵣ r)) ⊃ᵣ ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r))) :=
    star4_detach negation disjunction _ _ line1
      (star_3_31 negation disjunction p (q ∨ᵣ r) ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r)))
  have line3 : ⊢ᵣ (((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r)) ⊃ᵣ p) :=
    star4_detach negation disjunction _ _
      (star4_pair negation disjunction _ _
        (star_3_26 negation disjunction p q) (star_3_26 negation disjunction p r))
      (star_3_44 negation disjunction p (p ∧ᵣ q) (p ∧ᵣ r))
  have line4 : ⊢ᵣ (((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r)) ⊃ᵣ (q ∨ᵣ r)) :=
    star4_detach negation disjunction _ _
      (star4_pair negation disjunction _ _
        (star4_compose negation disjunction _ _ _ (star_3_27 negation disjunction p q)
          (star_2_2 negation disjunction q r))
        (star4_compose negation disjunction _ _ _ (star_3_27 negation disjunction p r)
          (Derivation.star_1_3_same negation disjunction q r)))
      (star_3_44 negation disjunction (q ∨ᵣ r) (p ∧ᵣ q) (p ∧ᵣ r))
  have line5 := star4_joinUnder negation disjunction ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ r)) _ _ line3 line4
  exact star4_join negation disjunction _ _ line2 line5

def star_4_41_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·41.  ⊢ : p . ∨ . q . r . ≡ . p ∨ q . p ∨ r"
    ((p ∨ᵣ (q ∧ᵣ r)) ≡ᵣ ((p ∨ᵣ q) ∧ᵣ (p ∨ᵣ r)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_41 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (q ∧ᵣ r)) ≡ᵣ ((p ∨ᵣ q) ∧ᵣ (p ∨ᵣ r))) := by
  let a := (p ∨ᵣ q) ∧ᵣ (p ∨ᵣ r)
  have line1 := star4_detach negation disjunction _ _ (star_3_26 negation disjunction q r)
    (Derivation.star_1_6_same negation disjunction p (q ∧ᵣ r) q)
  have line2 := star4_detach negation disjunction _ _ (star_3_27 negation disjunction q r)
    (Derivation.star_1_6_same negation disjunction p (q ∧ᵣ r) r)
  have line3 := star4_joinUnder negation disjunction (p ∨ᵣ (q ∧ᵣ r)) _ _ line1 line2
  have toQ := star4_compose negation disjunction _ _ _ (star_3_26 negation disjunction (p ∨ᵣ q) (p ∨ᵣ r))
    (star_2_53 negation disjunction p q)
  have toR := star4_compose negation disjunction _ _ _ (star_3_27 negation disjunction (p ∨ᵣ q) (p ∨ᵣ r))
    (star_2_53 negation disjunction p r)
  have line4a := star4_joinUnder negation disjunction a _ _ toQ toR
  have line4b := star4_compose negation disjunction _ _ _ line4a
    (star_3_43 negation disjunction (∼ᵣ p) q r)
  have line4 := star4_compose negation disjunction _ _ _ line4b
    (star_2_54 negation disjunction p (q ∧ᵣ r))
  exact star4_join negation disjunction _ _ line3 line4

def star_4_7_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·7.  ⊢ : p ⊃ q . ≡ : p . ⊃ . p . q"
    ((p ⊃ᵣ q) ≡ᵣ (p ⊃ᵣ (p ∧ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_7 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ≡ᵣ (p ⊃ᵣ (p ∧ᵣ q))) := by
  have line1 := star4_detach negation disjunction _ _ (star_3_27 negation disjunction p q)
    (star_2_05 negation disjunction p (p ∧ᵣ q) q)
  have line2 := star4_detach negation disjunction _ _ (star_3_2 negation disjunction p q)
    (star_2_77 negation disjunction p q (p ∧ᵣ q))
  exact star4_join negation disjunction _ _ line2 line1

def star_4_74_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·74.  ⊢ :. ∼p . ⊃ : q . ≡ . p ∨ q   [✱2·21 . ✱4·72]"
    ((∼ᵣ p) ⊃ᵣ (q ≡ᵣ (p ∨ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_74 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p) ⊃ᵣ (q ≡ᵣ (p ∨ᵣ q))) := by
  have line1 := star_2_21 negation disjunction p q
  have line2 := star4_detach negation disjunction _ _ (star_4_72 negation disjunction p q)
    (star_3_26 negation disjunction _ _)
  exact star4_compose negation disjunction _ _ _ line1 line2

def star_4_77_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·77.  ⊢ :. q ⊃ p . r ⊃ p . ≡ : q ∨ r . ⊃ . p   [✱3·44 . Add . ✱2·2]"
    (((q ⊃ᵣ p) ∧ᵣ (r ⊃ᵣ p)) ≡ᵣ ((q ∨ᵣ r) ⊃ᵣ p))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_77 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((q ⊃ᵣ p) ∧ᵣ (r ⊃ᵣ p)) ≡ᵣ ((q ∨ᵣ r) ⊃ᵣ p)) := by
  let g := (q ∨ᵣ r) ⊃ᵣ p
  have line1 := star_3_44 negation disjunction p q r
  have qadd := star_2_2 negation disjunction q r
  have radd := star4_compose negation disjunction _ _ _ (star_2_2 negation disjunction r q)
    (Derivation.star_1_4_same negation disjunction r q)
  have qbranch := star4_detach negation disjunction _ _ qadd
    (star_2_06 negation disjunction q (q ∨ᵣ r) p)
  have rbranch := star4_detach negation disjunction _ _ radd
    (star_2_06 negation disjunction r (q ∨ᵣ r) p)
  have line2 := star4_joinUnder negation disjunction g _ _ qbranch rbranch
  exact star4_join negation disjunction _ _ line1 line2

def star_4_6_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·6.  ⊢ : p ⊃ q . ≡ . ∼p ∨ q   [✱4·2 . (✱1·01)]"
    ((p ⊃ᵣ q) ≡ᵣ ((∼ᵣ p) ∨ᵣ q))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_6 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ≡ᵣ ((∼ᵣ p) ∨ᵣ q)) := by
  have line1 := star_4_2 negation disjunction (p ⊃ᵣ q)
  exact line1

def star_4_11_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·11.  ⊢ : p ≡ q . ≡ . ∼p ≡ ∼q   [✱2·16·17 . ✱3·47·22]"
    ((p ≡ᵣ q) ≡ᵣ ((∼ᵣ p) ≡ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_11 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ≡ᵣ q) ≡ᵣ ((∼ᵣ p) ≡ᵣ (∼ᵣ q))) := by
  let e := p ≡ᵣ q
  let n := (∼ᵣ p) ≡ᵣ (∼ᵣ q)
  have line1a := star4_compose negation disjunction _ _ _
    (star_3_26 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ p))
    (star_2_16 negation disjunction p q)
  have line1b := star4_compose negation disjunction _ _ _
    (star_3_27 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ p))
    (star_2_16 negation disjunction q p)
  have line1 : ⊢ᵣ (e ⊃ᵣ n) := star4_joinUnder negation disjunction e _ _ line1b line1a
  have line2a := star4_compose negation disjunction _ _ _
    (star_3_26 negation disjunction ((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ((∼ᵣ q) ⊃ᵣ (∼ᵣ p)))
    (star_2_17 negation disjunction q p)
  have line2b := star4_compose negation disjunction _ _ _
    (star_3_27 negation disjunction ((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ((∼ᵣ q) ⊃ᵣ (∼ᵣ p)))
    (star_2_17 negation disjunction p q)
  have line2 : ⊢ᵣ (n ⊃ᵣ e) := star4_joinUnder negation disjunction n _ _ line2b line2a
  exact star4_join negation disjunction _ _ line1 line2

def star_4_52_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·52.  ⊢ : p . ∼q . ≡ . ∼(∼p ∨ q)"
    ((p ∧ᵣ (∼ᵣ q)) ≡ᵣ (∼ᵣ ((∼ᵣ p) ∨ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_52 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∧ᵣ (∼ᵣ q)) ≡ᵣ (∼ᵣ ((∼ᵣ p) ∨ᵣ q))) := by
  let a := p ∧ᵣ (∼ᵣ q)
  let b := ∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ (∼ᵣ q)))
  let c := ∼ᵣ ((∼ᵣ p) ∨ᵣ q)
  have line1 : ⊢ᵣ (a ≡ᵣ b) :=
    star_4_5 negation disjunction p (∼ᵣ q)
  have line2 : ⊢ᵣ (q ≡ᵣ (∼ᵣ (∼ᵣ q))) :=
    star_4_13 negation disjunction q
  have line3 : ⊢ᵣ ((∼ᵣ (∼ᵣ q)) ≡ᵣ q) :=
    star4_detach negation disjunction _ _ line2
      (star_3_22 negation disjunction
        (q ⊃ᵣ (∼ᵣ (∼ᵣ q))) ((∼ᵣ (∼ᵣ q)) ⊃ᵣ q))
  have line4 : ⊢ᵣ ((∼ᵣ p) ≡ᵣ (∼ᵣ p)) :=
    star_4_2 negation disjunction (∼ᵣ p)
  have line5 : ⊢ᵣ (((∼ᵣ p) ≡ᵣ (∼ᵣ p)) ∧ᵣ
      ((∼ᵣ (∼ᵣ q)) ≡ᵣ q)) :=
    star4_pair negation disjunction _ _ line4 line3
  have line6 : ⊢ᵣ (((∼ᵣ p) ∨ᵣ (∼ᵣ (∼ᵣ q))) ≡ᵣ ((∼ᵣ p) ∨ᵣ q)) :=
    star4_detach negation disjunction _ _ line5
      (star_4_39 negation disjunction (∼ᵣ p) (∼ᵣ (∼ᵣ q)) (∼ᵣ p) q)
  have line7 : ⊢ᵣ (b ≡ᵣ c) :=
    star4_detach negation disjunction _ _ line6
      (star4_detach negation disjunction _ _
        (star_4_11 negation disjunction
          ((∼ᵣ p) ∨ᵣ (∼ᵣ (∼ᵣ q))) ((∼ᵣ p) ∨ᵣ q))
        (star_3_26 negation disjunction _ _))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line1 line7)
    (star_4_22 negation disjunction a b c)

def star_4_53_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·53.  ⊢ : ∼(p . ∼q) . ≡ . ∼p ∨ q"
    ((∼ᵣ (p ∧ᵣ (∼ᵣ q))) ≡ᵣ ((∼ᵣ p) ∨ᵣ q))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_53 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ (p ∧ᵣ (∼ᵣ q))) ≡ᵣ ((∼ᵣ p) ∨ᵣ q)) := by
  let c := p ∧ᵣ (∼ᵣ q)
  let x := (∼ᵣ p) ∨ᵣ q
  have line1 : ⊢ᵣ (c ≡ᵣ (∼ᵣ x)) :=
    star_4_52 negation disjunction p q
  have line2 : ⊢ᵣ (x ≡ᵣ (∼ᵣ c)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_12 negation disjunction c x)
        (star_3_26 negation disjunction _ _))
  exact star4_detach negation disjunction _ _ line2
    (star_3_22 negation disjunction
      (x ⊃ᵣ (∼ᵣ c)) ((∼ᵣ c) ⊃ᵣ x))

def star_4_54_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·54.  ⊢ : ∼p . q . ≡ . ∼(p ∨ ∼q)"
    (((∼ᵣ p) ∧ᵣ q) ≡ᵣ (∼ᵣ (p ∨ᵣ (∼ᵣ q))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_54 (p q : Formula signature real [] order) :
    ⊢ᵣ (((∼ᵣ p) ∧ᵣ q) ≡ᵣ (∼ᵣ (p ∨ᵣ (∼ᵣ q)))) := by
  let a := (∼ᵣ p) ∧ᵣ q
  let b := ∼ᵣ ((∼ᵣ (∼ᵣ p)) ∨ᵣ (∼ᵣ q))
  let c := ∼ᵣ (p ∨ᵣ (∼ᵣ q))
  have line1 : ⊢ᵣ (a ≡ᵣ b) :=
    star_4_5 negation disjunction (∼ᵣ p) q
  have line2 : ⊢ᵣ (p ≡ᵣ (∼ᵣ (∼ᵣ p))) :=
    star_4_13 negation disjunction p
  have line3 : ⊢ᵣ ((∼ᵣ (∼ᵣ p)) ≡ᵣ p) :=
    star4_detach negation disjunction _ _ line2
      (star_3_22 negation disjunction
        (p ⊃ᵣ (∼ᵣ (∼ᵣ p))) ((∼ᵣ (∼ᵣ p)) ⊃ᵣ p))
  have line4 : ⊢ᵣ ((∼ᵣ q) ≡ᵣ (∼ᵣ q)) :=
    star_4_2 negation disjunction (∼ᵣ q)
  have line5 : ⊢ᵣ (((∼ᵣ (∼ᵣ p)) ≡ᵣ p) ∧ᵣ
      ((∼ᵣ q) ≡ᵣ (∼ᵣ q))) :=
    star4_pair negation disjunction _ _ line3 line4
  have line6 : ⊢ᵣ (((∼ᵣ (∼ᵣ p)) ∨ᵣ (∼ᵣ q)) ≡ᵣ (p ∨ᵣ (∼ᵣ q))) :=
    star4_detach negation disjunction _ _ line5
      (star_4_39 negation disjunction (∼ᵣ (∼ᵣ p)) (∼ᵣ q) p (∼ᵣ q))
  have line7 : ⊢ᵣ (b ≡ᵣ c) :=
    star4_detach negation disjunction _ _ line6
      (star4_detach negation disjunction _ _
        (star_4_11 negation disjunction
          ((∼ᵣ (∼ᵣ p)) ∨ᵣ (∼ᵣ q)) (p ∨ᵣ (∼ᵣ q)))
        (star_3_26 negation disjunction _ _))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line1 line7)
    (star_4_22 negation disjunction a b c)

def star_4_55_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·55.  ⊢ : ∼(∼p . q) . ≡ . p ∨ ∼q"
    ((∼ᵣ ((∼ᵣ p) ∧ᵣ q)) ≡ᵣ (p ∨ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_55 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ ((∼ᵣ p) ∧ᵣ q)) ≡ᵣ (p ∨ᵣ (∼ᵣ q))) := by
  let c := (∼ᵣ p) ∧ᵣ q
  let x := p ∨ᵣ (∼ᵣ q)
  have line1 : ⊢ᵣ (c ≡ᵣ (∼ᵣ x)) :=
    star_4_54 negation disjunction p q
  have line2 : ⊢ᵣ (x ≡ᵣ (∼ᵣ c)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_12 negation disjunction c x)
        (star_3_26 negation disjunction _ _))
  exact star4_detach negation disjunction _ _ line2
    (star_3_22 negation disjunction
      (x ⊃ᵣ (∼ᵣ c)) ((∼ᵣ c) ⊃ᵣ x))

def star_4_56_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·56.  ⊢ : ∼p . ∼q . ≡ . ∼(p ∨ q)"
    (((∼ᵣ p) ∧ᵣ (∼ᵣ q)) ≡ᵣ (∼ᵣ (p ∨ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_56 (p q : Formula signature real [] order) :
    ⊢ᵣ (((∼ᵣ p) ∧ᵣ (∼ᵣ q)) ≡ᵣ (∼ᵣ (p ∨ᵣ q))) := by
  let a := (∼ᵣ p) ∧ᵣ (∼ᵣ q)
  let b := ∼ᵣ (p ∨ᵣ (∼ᵣ (∼ᵣ q)))
  let c := ∼ᵣ (p ∨ᵣ q)
  have line1 : ⊢ᵣ (a ≡ᵣ b) :=
    star_4_54 negation disjunction p (∼ᵣ q)
  have line2 : ⊢ᵣ (q ≡ᵣ (∼ᵣ (∼ᵣ q))) :=
    star_4_13 negation disjunction q
  have line3 : ⊢ᵣ ((∼ᵣ (∼ᵣ q)) ≡ᵣ q) :=
    star4_detach negation disjunction _ _ line2
      (star_3_22 negation disjunction
        (q ⊃ᵣ (∼ᵣ (∼ᵣ q))) ((∼ᵣ (∼ᵣ q)) ⊃ᵣ q))
  have line4 : ⊢ᵣ (p ≡ᵣ p) :=
    star_4_2 negation disjunction p
  have line5 : ⊢ᵣ ((p ≡ᵣ p) ∧ᵣ ((∼ᵣ (∼ᵣ q)) ≡ᵣ q)) :=
    star4_pair negation disjunction _ _ line4 line3
  have line6 : ⊢ᵣ ((p ∨ᵣ (∼ᵣ (∼ᵣ q))) ≡ᵣ (p ∨ᵣ q)) :=
    star4_detach negation disjunction _ _ line5
      (star_4_39 negation disjunction p (∼ᵣ (∼ᵣ q)) p q)
  have line7 : ⊢ᵣ (b ≡ᵣ c) :=
    star4_detach negation disjunction _ _ line6
      (star4_detach negation disjunction _ _
        (star_4_11 negation disjunction (p ∨ᵣ (∼ᵣ (∼ᵣ q))) (p ∨ᵣ q))
        (star_3_26 negation disjunction _ _))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line1 line7)
    (star_4_22 negation disjunction a b c)

def star_4_57_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·57.  ⊢ : ∼(∼p . ∼q) . ≡ . p ∨ q"
    ((∼ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q))) ≡ᵣ (p ∨ᵣ q))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_57 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q))) ≡ᵣ (p ∨ᵣ q)) := by
  let c := (∼ᵣ p) ∧ᵣ (∼ᵣ q)
  let x := p ∨ᵣ q
  have line1 : ⊢ᵣ (c ≡ᵣ (∼ᵣ x)) :=
    star_4_56 negation disjunction p q
  have line2 : ⊢ᵣ (x ≡ᵣ (∼ᵣ c)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_12 negation disjunction c x)
        (star_3_26 negation disjunction _ _))
  exact star4_detach negation disjunction _ _ line2
    (star_3_22 negation disjunction
      (x ⊃ᵣ (∼ᵣ c)) ((∼ᵣ c) ⊃ᵣ x))

def star_4_61_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·61.  ⊢ : ∼(p ⊃ q) . ≡ . p . ∼q   [✱4·6·11·52]"
    ((∼ᵣ (p ⊃ᵣ q)) ≡ᵣ (p ∧ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_61 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ (p ⊃ᵣ q)) ≡ᵣ (p ∧ᵣ (∼ᵣ q))) := by
  let a := p ⊃ᵣ q
  let b := (∼ᵣ p) ∨ᵣ q
  let c := p ∧ᵣ (∼ᵣ q)
  have line1 : ⊢ᵣ (a ≡ᵣ b) :=
    star_4_6 negation disjunction p q
  have line2 : ⊢ᵣ ((∼ᵣ a) ≡ᵣ (∼ᵣ b)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_11 negation disjunction a b)
        (star_3_26 negation disjunction _ _))
  have line3 : ⊢ᵣ (c ≡ᵣ (∼ᵣ b)) :=
    star_4_52 negation disjunction p q
  have line4 : ⊢ᵣ ((∼ᵣ b) ≡ᵣ c) :=
    star4_detach negation disjunction _ _ line3
      (star_3_22 negation disjunction
        (c ⊃ᵣ (∼ᵣ b)) ((∼ᵣ b) ⊃ᵣ c))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line2 line4)
    (star_4_22 negation disjunction (∼ᵣ a) (∼ᵣ b) c)

def star_4_62_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·62.  ⊢ : p ⊃ ∼q . ≡ . ∼p ∨ ∼q"
    ((p ⊃ᵣ (∼ᵣ q)) ≡ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_62 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (∼ᵣ q)) ≡ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))) := by
  have line1 := star_4_6 negation disjunction p (∼ᵣ q)
  exact line1

def star_4_63_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·63.  ⊢ : ∼(p ⊃ ∼q) . ≡ . p . q"
    ((∼ᵣ (p ⊃ᵣ (∼ᵣ q))) ≡ᵣ (p ∧ᵣ q))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_63 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ (p ⊃ᵣ (∼ᵣ q))) ≡ᵣ (p ∧ᵣ q)) := by
  let a := p ⊃ᵣ (∼ᵣ q)
  let b := (∼ᵣ p) ∨ᵣ (∼ᵣ q)
  let c := p ∧ᵣ q
  have line1 : ⊢ᵣ (a ≡ᵣ b) :=
    star_4_62 negation disjunction p q
  have line2 : ⊢ᵣ ((∼ᵣ a) ≡ᵣ (∼ᵣ b)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_11 negation disjunction a b)
        (star_3_26 negation disjunction _ _))
  have line3 : ⊢ᵣ (c ≡ᵣ (∼ᵣ b)) :=
    star_4_5 negation disjunction p q
  have line4 : ⊢ᵣ ((∼ᵣ b) ≡ᵣ c) :=
    star4_detach negation disjunction _ _ line3
      (star_3_22 negation disjunction
        (c ⊃ᵣ (∼ᵣ b)) ((∼ᵣ b) ⊃ᵣ c))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line2 line4)
    (star_4_22 negation disjunction (∼ᵣ a) (∼ᵣ b) c)

def star_4_64_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·64.  ⊢ : ∼p ⊃ q . ≡ . p ∨ q   [✱2·53·54]"
    (((∼ᵣ p) ⊃ᵣ q) ≡ᵣ (p ∨ᵣ q))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_64 (p q : Formula signature real [] order) :
    ⊢ᵣ (((∼ᵣ p) ⊃ᵣ q) ≡ᵣ (p ∨ᵣ q)) := by
  have line1 : ⊢ᵣ (((∼ᵣ p) ⊃ᵣ q) ⊃ᵣ (p ∨ᵣ q)) :=
    star_2_54 negation disjunction p q
  have line2 : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((∼ᵣ p) ⊃ᵣ q)) :=
    star_2_53 negation disjunction p q
  exact star4_join negation disjunction _ _ line1 line2

def star_4_65_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·65.  ⊢ : ∼(∼p ⊃ q) . ≡ . ∼p . ∼q   [✱4·64·11·56]"
    ((∼ᵣ ((∼ᵣ p) ⊃ᵣ q)) ≡ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_65 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ ((∼ᵣ p) ⊃ᵣ q)) ≡ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q))) := by
  let a := (∼ᵣ p) ⊃ᵣ q
  let b := p ∨ᵣ q
  let c := (∼ᵣ p) ∧ᵣ (∼ᵣ q)
  have line1 : ⊢ᵣ (a ≡ᵣ b) :=
    star_4_64 negation disjunction p q
  have line2 : ⊢ᵣ ((∼ᵣ a) ≡ᵣ (∼ᵣ b)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_11 negation disjunction a b)
        (star_3_26 negation disjunction _ _))
  have line3 : ⊢ᵣ (c ≡ᵣ (∼ᵣ b)) :=
    star_4_56 negation disjunction p q
  have line4 : ⊢ᵣ ((∼ᵣ b) ≡ᵣ c) :=
    star4_detach negation disjunction _ _ line3
      (star_3_22 negation disjunction
        (c ⊃ᵣ (∼ᵣ b)) ((∼ᵣ b) ⊃ᵣ c))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line2 line4)
    (star_4_22 negation disjunction (∼ᵣ a) (∼ᵣ b) c)

def star_4_66_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·66.  ⊢ : ∼p ⊃ ∼q . ≡ . p ∨ ∼q   [✱4·64 ∼q/q]"
    (((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ≡ᵣ (p ∨ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_66 (p q : Formula signature real [] order) :
    ⊢ᵣ (((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ≡ᵣ (p ∨ᵣ (∼ᵣ q))) := by
  have line1 := star_4_64 negation disjunction p (∼ᵣ q)
  exact line1

def star_4_67_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·67.  ⊢ : ∼(∼p ⊃ ∼q) . ≡ . ∼p . q   [✱4·66·11·54]"
    ((∼ᵣ ((∼ᵣ p) ⊃ᵣ (∼ᵣ q))) ≡ᵣ ((∼ᵣ p) ∧ᵣ q))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_67 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ ((∼ᵣ p) ⊃ᵣ (∼ᵣ q))) ≡ᵣ ((∼ᵣ p) ∧ᵣ q)) := by
  let a := (∼ᵣ p) ⊃ᵣ (∼ᵣ q)
  let b := p ∨ᵣ (∼ᵣ q)
  let c := (∼ᵣ p) ∧ᵣ q
  have line1 : ⊢ᵣ (a ≡ᵣ b) :=
    star_4_66 negation disjunction p q
  have line2 : ⊢ᵣ ((∼ᵣ a) ≡ᵣ (∼ᵣ b)) :=
    star4_detach negation disjunction _ _ line1
      (star4_detach negation disjunction _ _
        (star_4_11 negation disjunction a b)
        (star_3_26 negation disjunction _ _))
  have line3 : ⊢ᵣ (c ≡ᵣ (∼ᵣ b)) :=
    star_4_54 negation disjunction p q
  have line4 : ⊢ᵣ ((∼ᵣ b) ≡ᵣ c) :=
    star4_detach negation disjunction _ _ line3
      (star_3_22 negation disjunction
        (c ⊃ᵣ (∼ᵣ b)) ((∼ᵣ b) ⊃ᵣ c))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line2 line4)
    (star_4_22 negation disjunction (∼ᵣ a) (∼ᵣ b) c)

def star_4_42_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·42.  ⊢ : p . ≡ : p . q . ∨ . p . ∼q"
    (p ≡ᵣ ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ (∼ᵣ q))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_42 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ≡ᵣ ((p ∧ᵣ q) ∨ᵣ (p ∧ᵣ (∼ᵣ q)))) := by
  have line1a := star4_detach negation disjunction _ _ (star_2_11 negation disjunction q)
    (star_3_21 negation disjunction p (q ∨ᵣ (∼ᵣ q)))
  have line1 := star4_compose negation disjunction _ _ _ line1a
    (star4_detach negation disjunction _ _ (star_4_4 negation disjunction p q (∼ᵣ q))
      (star_3_26 negation disjunction _ _))
  have line2 := star4_detach negation disjunction _ _
      (star4_pair negation disjunction _ _ (star_3_26 negation disjunction p q)
      (star_3_26 negation disjunction p (∼ᵣ q)))
    (star_3_44 negation disjunction p (p ∧ᵣ q) (p ∧ᵣ (∼ᵣ q)))
  exact star4_join negation disjunction _ _ line1 line2

def star_4_43_reading (p q : Formula signature real [] order) :=
  star4_reading "✱4·43.  ⊢ : p . ≡ : p ∨ q . p ∨ ∼q"
    (p ≡ᵣ ((p ∨ᵣ q) ∧ᵣ (p ∨ᵣ (∼ᵣ q))))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_43 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ≡ᵣ ((p ∨ᵣ q) ∧ᵣ (p ∨ᵣ (∼ᵣ q)))) := by
  have line1 := star4_joinUnder negation disjunction p _ _
    (star_2_2 negation disjunction p q) (star_2_2 negation disjunction p (∼ᵣ q))
  have branches := star4_joinUnder negation disjunction
    ((p ∨ᵣ q) ∧ᵣ (p ∨ᵣ (∼ᵣ q))) _ _
    (star4_compose negation disjunction _ _ _ (star_3_26 negation disjunction _ _)
      (star_2_53 negation disjunction p q))
    (star4_compose negation disjunction _ _ _ (star_3_27 negation disjunction _ _)
      (star_2_53 negation disjunction p (∼ᵣ q)))
  have contradiction := star4_detach negation disjunction _ _ (star_2_65 negation disjunction (∼ᵣ p) q)
    (star_3_31 negation disjunction ((∼ᵣ p) ⊃ᵣ q) ((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) (∼ᵣ (∼ᵣ p)))
  have line2 := star4_compose negation disjunction _ _ _ branches contradiction
  have line2' := star4_compose negation disjunction _ _ _ line2 (star_2_14 negation disjunction p)
  exact star4_join negation disjunction _ _ line1 line2'

def star_4_32_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·32.  ⊢ : (p . q) . r . ≡ . p . (q . r)"
    (((p ∧ᵣ q) ∧ᵣ r) ≡ᵣ (p ∧ᵣ (q ∧ᵣ r)))

/-- `demonstration_provenance: editorial-reconstruction`. -/
theorem star_4_32 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ∧ᵣ q) ∧ᵣ r) ≡ᵣ (p ∧ᵣ (q ∧ᵣ r))) := by
  let a := (p ∧ᵣ q) ∧ᵣ r
  let b := p ∧ᵣ (q ∧ᵣ r)
  have line1p := star4_compose negation disjunction _ _ _
    (star_3_26 negation disjunction (p ∧ᵣ q) r) (star_3_26 negation disjunction p q)
  have line1q := star4_compose negation disjunction _ _ _
    (star_3_26 negation disjunction (p ∧ᵣ q) r) (star_3_27 negation disjunction p q)
  have line1r := star_3_27 negation disjunction (p ∧ᵣ q) r
  have line1qr := star4_joinUnder negation disjunction a _ _ line1q line1r
  have line1 := star4_joinUnder negation disjunction a _ _ line1p line1qr
  have line2p := star_3_26 negation disjunction p (q ∧ᵣ r)
  have line2q := star4_compose negation disjunction _ _ _
    (star_3_27 negation disjunction p (q ∧ᵣ r)) (star_3_26 negation disjunction q r)
  have line2r := star4_compose negation disjunction _ _ _
    (star_3_27 negation disjunction p (q ∧ᵣ r)) (star_3_27 negation disjunction q r)
  have line2pq := star4_joinUnder negation disjunction b _ _ line2p line2q
  have line2 := star4_joinUnder negation disjunction b _ _ line2pq line2r
  exact star4_join negation disjunction _ _ line1 line2

def star_4_86_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·86.  ⊢ :. p ≡ q . ⊃ : p ≡ r . ≡ . q ≡ r   [✱4·21·22]"
    ((p ≡ᵣ q) ⊃ᵣ ((p ≡ᵣ r) ≡ᵣ (q ≡ᵣ r)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_86 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ≡ᵣ q) ⊃ᵣ ((p ≡ᵣ r) ≡ᵣ (q ≡ᵣ r))) := by
  let e := p ≡ᵣ q
  let a := p ≡ᵣ r
  let b := q ≡ᵣ r
  have line1pair := star4_joinUnder negation disjunction (e ∧ᵣ a) _ _
    (star4_compose negation disjunction _ _ _ (star_3_26 negation disjunction e a)
      (star4_detach negation disjunction _ _ (star_4_21 negation disjunction p q)
        (star_3_26 negation disjunction _ _)))
    (star_3_27 negation disjunction e a)
  have line1raw := star4_compose negation disjunction _ _ _ line1pair
    (star_4_22 negation disjunction q p r)
  have line1 := star4_detach negation disjunction _ _ line1raw
    (star_3_3 negation disjunction e a b)
  have line2pair := star4_joinUnder negation disjunction (e ∧ᵣ b) _ _
    (star_3_26 negation disjunction e b) (star_3_27 negation disjunction e b)
  have line2raw := star4_compose negation disjunction _ _ _ line2pair
    (star_4_22 negation disjunction p q r)
  have line2 := star4_detach negation disjunction _ _ line2raw
    (star_3_3 negation disjunction e b a)
  exact star4_joinUnder negation disjunction e _ _ line1 line2

private def star4_equivChain4
    (n : signature.Negation order) (d : signature.Disjunction order)
    (a b c z : Formula signature real [] order) :=
  conjunction n d
    (conjunction n d (star_4_01 n d a b) (star_4_01 n d b c))
    (star_4_01 n d c z)

def star_4_87_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·87.  ⊢ : p . q . ⊃ . r : ≡ : p . ⊃ . q ⊃ r : ≡ : q . ⊃ . p ⊃ r : ≡ : q . p . ⊃ . r   [Exp . Comm . Imp]"
    (star4_equivChain4 negation disjunction ((p ∧ᵣ q) ⊃ᵣ r)
      (p ⊃ᵣ (q ⊃ᵣ r)) (q ⊃ᵣ (p ⊃ᵣ r)) ((q ∧ᵣ p) ⊃ᵣ r))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_87 (p q r : Formula signature real [] order) :
    ⊢ᵣ star4_equivChain4 negation disjunction ((p ∧ᵣ q) ⊃ᵣ r)
      (p ⊃ᵣ (q ⊃ᵣ r)) (q ⊃ᵣ (p ⊃ᵣ r)) ((q ∧ᵣ p) ⊃ᵣ r) := by
  have line1 := star4_join negation disjunction _ _
    (star_3_3 negation disjunction p q r) (star_3_31 negation disjunction p q r)
  have line2 := star4_join negation disjunction _ _
    (star_2_04 negation disjunction p q r) (star_2_04 negation disjunction q p r)
  have line3 := star4_join negation disjunction _ _
    (star_3_31 negation disjunction q p r) (star_3_3 negation disjunction q p r)
  exact star4_pair negation disjunction _ _
    (star4_pair negation disjunction _ _ line1 line2) line3

def star_4_14_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·14.  ⊢ :. p . q . ⊃ . r : ≡ : p . ∼r . ⊃ . ∼q"
    (((p ∧ᵣ q) ⊃ᵣ r) ≡ᵣ ((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_14 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ∧ᵣ q) ⊃ᵣ r) ≡ᵣ ((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q))) := by
  have line1 : ⊢ᵣ (((p ∧ᵣ q) ⊃ᵣ r) ⊃ᵣ ((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q))) :=
    star_3_37 negation disjunction p q r
  have line2 : ⊢ᵣ (q ⊃ᵣ (∼ᵣ (∼ᵣ q))) :=
    star4_detach negation disjunction _ _ (star_4_13 negation disjunction q)
      (star_3_26 negation disjunction
        (q ⊃ᵣ (∼ᵣ (∼ᵣ q))) ((∼ᵣ (∼ᵣ q)) ⊃ᵣ q))
  have line3 : ⊢ᵣ ((∼ᵣ (∼ᵣ r)) ⊃ᵣ r) :=
    star4_detach negation disjunction _ _ (star_4_13 negation disjunction r)
      (star_3_27 negation disjunction
        (r ⊃ᵣ (∼ᵣ (∼ᵣ r))) ((∼ᵣ (∼ᵣ r)) ⊃ᵣ r))
  have line4 : ⊢ᵣ ((p ∧ᵣ q) ⊃ᵣ (p ∧ᵣ (∼ᵣ (∼ᵣ q)))) :=
    star4_compose negation disjunction _ _ _
      (star_3_22 negation disjunction p q)
      (star4_compose negation disjunction _ _ _
        (star4_detach negation disjunction _ _ line2
          (star_3_45 negation disjunction q (∼ᵣ (∼ᵣ q)) p))
        (star_3_22 negation disjunction (∼ᵣ (∼ᵣ q)) p))
  have line5 :
      ⊢ᵣ (((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q)) ⊃ᵣ
        ((p ∧ᵣ (∼ᵣ (∼ᵣ q))) ⊃ᵣ (∼ᵣ (∼ᵣ r)))) :=
    star_3_37 negation disjunction p (∼ᵣ r) (∼ᵣ q)
  have line6 :
      ⊢ᵣ (((p ∧ᵣ (∼ᵣ (∼ᵣ q))) ⊃ᵣ (∼ᵣ (∼ᵣ r))) ⊃ᵣ
        ((p ∧ᵣ q) ⊃ᵣ (∼ᵣ (∼ᵣ r)))) :=
    star4_detach negation disjunction _ _ line4
      (star_2_06 negation disjunction
        (p ∧ᵣ q) (p ∧ᵣ (∼ᵣ (∼ᵣ q))) (∼ᵣ (∼ᵣ r)))
  have line7 :
      ⊢ᵣ (((p ∧ᵣ q) ⊃ᵣ (∼ᵣ (∼ᵣ r))) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r)) :=
    star4_detach negation disjunction _ _ line3
      (star_2_05 negation disjunction (p ∧ᵣ q) (∼ᵣ (∼ᵣ r)) r)
  have line8 :
      ⊢ᵣ (((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q)) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r)) :=
    star4_compose negation disjunction _ _ _ line5
      (star4_compose negation disjunction _ _ _ line6 line7)
  exact star4_pair negation disjunction _ _ line1 line8

def star_4_15_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·15.  ⊢ :. p . q . ⊃ . ∼r : ≡ : q . r . ⊃ . ∼p"
    (((p ∧ᵣ q) ⊃ᵣ (∼ᵣ r)) ≡ᵣ ((q ∧ᵣ r) ⊃ᵣ (∼ᵣ p)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_15 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ∧ᵣ q) ⊃ᵣ (∼ᵣ r)) ≡ᵣ ((q ∧ᵣ r) ⊃ᵣ (∼ᵣ p))) := by
  have line1 := star_4_14 negation disjunction q p (∼ᵣ r)
  have line2 := star4_detach negation disjunction _ _ line1
    (star_3_26 negation disjunction _ _)
  have line3 := star4_detach negation disjunction _ _ line1
    (star_3_27 negation disjunction _ _)
  have line4 : ⊢ᵣ (r ⊃ᵣ (∼ᵣ (∼ᵣ r))) :=
    star4_detach negation disjunction _ _ (star_4_13 negation disjunction r)
      (star_3_26 negation disjunction
        (r ⊃ᵣ (∼ᵣ (∼ᵣ r))) ((∼ᵣ (∼ᵣ r)) ⊃ᵣ r))
  have line5 : ⊢ᵣ ((∼ᵣ (∼ᵣ r)) ⊃ᵣ r) :=
    star4_detach negation disjunction _ _ (star_4_13 negation disjunction r)
      (star_3_27 negation disjunction
        (r ⊃ᵣ (∼ᵣ (∼ᵣ r))) ((∼ᵣ (∼ᵣ r)) ⊃ᵣ r))
  have line6 : ⊢ᵣ ((q ∧ᵣ r) ⊃ᵣ (q ∧ᵣ (∼ᵣ (∼ᵣ r)))) :=
    star4_compose negation disjunction _ _ _
      (star_3_22 negation disjunction q r)
      (star4_compose negation disjunction _ _ _
        (star4_detach negation disjunction _ _ line4
          (star_3_45 negation disjunction r (∼ᵣ (∼ᵣ r)) q))
        (star_3_22 negation disjunction (∼ᵣ (∼ᵣ r)) q))
  have line7 : ⊢ᵣ ((q ∧ᵣ (∼ᵣ (∼ᵣ r))) ⊃ᵣ (q ∧ᵣ r)) :=
    star4_compose negation disjunction _ _ _
      (star_3_22 negation disjunction q (∼ᵣ (∼ᵣ r)))
      (star4_compose negation disjunction _ _ _
        (star4_detach negation disjunction _ _ line5
          (star_3_45 negation disjunction (∼ᵣ (∼ᵣ r)) r q))
        (star_3_22 negation disjunction r q))
  have line8 :
      ⊢ᵣ (((p ∧ᵣ q) ⊃ᵣ (∼ᵣ r)) ⊃ᵣ ((q ∧ᵣ p) ⊃ᵣ (∼ᵣ r))) :=
    star4_detach negation disjunction _ _ (star_3_22 negation disjunction q p)
      (star_2_06 negation disjunction (q ∧ᵣ p) (p ∧ᵣ q) (∼ᵣ r))
  have line9 :
      ⊢ᵣ (((q ∧ᵣ p) ⊃ᵣ (∼ᵣ r)) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ (∼ᵣ r))) :=
    star4_detach negation disjunction _ _ (star_3_22 negation disjunction p q)
      (star_2_06 negation disjunction (p ∧ᵣ q) (q ∧ᵣ p) (∼ᵣ r))
  have line10 :
      ⊢ᵣ (((q ∧ᵣ (∼ᵣ (∼ᵣ r))) ⊃ᵣ (∼ᵣ p)) ⊃ᵣ
        ((q ∧ᵣ r) ⊃ᵣ (∼ᵣ p))) :=
    star4_detach negation disjunction _ _ line6
      (star_2_06 negation disjunction
        (q ∧ᵣ r) (q ∧ᵣ (∼ᵣ (∼ᵣ r))) (∼ᵣ p))
  have line11 :
      ⊢ᵣ (((q ∧ᵣ r) ⊃ᵣ (∼ᵣ p)) ⊃ᵣ
        ((q ∧ᵣ (∼ᵣ (∼ᵣ r))) ⊃ᵣ (∼ᵣ p))) :=
    star4_detach negation disjunction _ _ line7
      (star_2_06 negation disjunction
        (q ∧ᵣ (∼ᵣ (∼ᵣ r))) (q ∧ᵣ r) (∼ᵣ p))
  have line12 := star4_compose negation disjunction _ _ _
    (star4_compose negation disjunction _ _ _ line8 line2) line10
  have line13 := star4_compose negation disjunction _ _ _
    (star4_compose negation disjunction _ _ _ line11 line3) line9
  exact star4_pair negation disjunction _ _ line12 line13

def star_4_78_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·78.  ⊢ : p ⊃ q . ∨ . p ⊃ r . ≡ : p . ⊃ . q ∨ r"
    (((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r)) ≡ᵣ (p ⊃ᵣ (q ∨ᵣ r)))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_78 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r)) ≡ᵣ (p ⊃ᵣ (q ∨ᵣ r))) := by
  have line1 :
      ⊢ᵣ (((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r)) ≡ᵣ
        (((∼ᵣ p) ∨ᵣ q) ∨ᵣ ((∼ᵣ p) ∨ᵣ r))) :=
    star_4_2 negation disjunction ((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r))
  have line2 :
      ⊢ᵣ ((((∼ᵣ p) ∨ᵣ q) ∨ᵣ ((∼ᵣ p) ∨ᵣ r)) ≡ᵣ
        ((((∼ᵣ p) ∨ᵣ q) ∨ᵣ (∼ᵣ p)) ∨ᵣ r)) :=
    star4_detach negation disjunction _ _
      (star_4_33 negation disjunction ((∼ᵣ p) ∨ᵣ q) (∼ᵣ p) r)
      (star4_detach negation disjunction _ _
        (star_4_21 negation disjunction
          ((((∼ᵣ p) ∨ᵣ q) ∨ᵣ (∼ᵣ p)) ∨ᵣ r)
          (((∼ᵣ p) ∨ᵣ q) ∨ᵣ ((∼ᵣ p) ∨ᵣ r)))
        (star_3_26 negation disjunction _ _))
  have line3 :
      ⊢ᵣ (((((∼ᵣ p) ∨ᵣ q) ∨ᵣ (∼ᵣ p)) ∨ᵣ r) ≡ᵣ
        (((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)) ∨ᵣ r)) :=
    star4_detach negation disjunction _ _
      (star_4_31 negation disjunction ((∼ᵣ p) ∨ᵣ q) (∼ᵣ p))
      (star_4_37 negation disjunction
        (((∼ᵣ p) ∨ᵣ q) ∨ᵣ (∼ᵣ p))
        ((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)) r)
  have line4a :
      ⊢ᵣ ((((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)) ∨ᵣ r) ≡ᵣ
        ((((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ q) ∨ᵣ r)) :=
    star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _
        (star_4_33 negation disjunction (∼ᵣ p) (∼ᵣ p) q)
        (star4_detach negation disjunction _ _
          (star_4_21 negation disjunction
            (((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ q)
            ((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)))
          (star_3_26 negation disjunction _ _)))
      (star_4_37 negation disjunction
        ((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q))
        (((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ q) r)
  have line4b :
      ⊢ᵣ (((((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ q) ∨ᵣ r) ≡ᵣ
        (((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ (q ∨ᵣ r))) :=
    star_4_33 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ p)) q r
  have line4 :
      ⊢ᵣ ((((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)) ∨ᵣ r) ≡ᵣ
        (((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ (q ∨ᵣ r))) :=
    star4_detach negation disjunction _ _
      (star4_pair negation disjunction _ _ line4a line4b)
      (star_4_22 negation disjunction
        (((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)) ∨ᵣ r)
        ((((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ q) ∨ᵣ r)
        (((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ (q ∨ᵣ r)))
  have line5 :
      ⊢ᵣ ((((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ (q ∨ᵣ r)) ≡ᵣ
        ((∼ᵣ p) ∨ᵣ (q ∨ᵣ r))) :=
    star4_detach negation disjunction _ _
      (star4_detach negation disjunction _ _
        (star_4_25 negation disjunction (∼ᵣ p))
        (star4_detach negation disjunction _ _
          (star_4_21 negation disjunction
            (∼ᵣ p) ((∼ᵣ p) ∨ᵣ (∼ᵣ p)))
          (star_3_26 negation disjunction _ _)))
      (star_4_37 negation disjunction
        ((∼ᵣ p) ∨ᵣ (∼ᵣ p)) (∼ᵣ p) (q ∨ᵣ r))
  have line6 :
      ⊢ᵣ (((∼ᵣ p) ∨ᵣ (q ∨ᵣ r)) ≡ᵣ (p ⊃ᵣ (q ∨ᵣ r))) :=
    star_4_2 negation disjunction ((∼ᵣ p) ∨ᵣ (q ∨ᵣ r))
  have chain12 := star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line1 line2)
    (star_4_22 negation disjunction
      ((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r))
      (((∼ᵣ p) ∨ᵣ q) ∨ᵣ ((∼ᵣ p) ∨ᵣ r))
      ((((∼ᵣ p) ∨ᵣ q) ∨ᵣ (∼ᵣ p)) ∨ᵣ r))
  have chain13 := star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ chain12 line3)
    (star_4_22 negation disjunction
      ((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r))
      ((((∼ᵣ p) ∨ᵣ q) ∨ᵣ (∼ᵣ p)) ∨ᵣ r)
      (((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)) ∨ᵣ r))
  have chain14 := star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ chain13 line4)
    (star_4_22 negation disjunction
      ((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r))
      (((∼ᵣ p) ∨ᵣ ((∼ᵣ p) ∨ᵣ q)) ∨ᵣ r)
      (((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ (q ∨ᵣ r)))
  have chain15 := star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ chain14 line5)
    (star_4_22 negation disjunction
      ((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r))
      (((∼ᵣ p) ∨ᵣ (∼ᵣ p)) ∨ᵣ (q ∨ᵣ r))
      ((∼ᵣ p) ∨ᵣ (q ∨ᵣ r)))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ chain15 line6)
    (star_4_22 negation disjunction
      ((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ r))
      ((∼ᵣ p) ∨ᵣ (q ∨ᵣ r)) (p ⊃ᵣ (q ∨ᵣ r)))

def star_4_79_reading (p q r : Formula signature real [] order) :=
  star4_reading "✱4·79.  ⊢ : q ⊃ p . ∨ . r ⊃ p . ≡ : q . r . ⊃ . p"
    (((q ⊃ᵣ p) ∨ᵣ (r ⊃ᵣ p)) ≡ᵣ ((q ∧ᵣ r) ⊃ᵣ p))

/-- `demonstration_provenance: follows-printed`. -/
theorem star_4_79 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((q ⊃ᵣ p) ∨ᵣ (r ⊃ᵣ p)) ≡ᵣ ((q ∧ᵣ r) ⊃ᵣ p)) := by
  have line1 :
      ⊢ᵣ (((q ⊃ᵣ p) ∨ᵣ (r ⊃ᵣ p)) ≡ᵣ
        (((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ∨ᵣ ((∼ᵣ p) ⊃ᵣ (∼ᵣ r)))) :=
    star4_detach negation disjunction _ _
      (star4_pair negation disjunction _ _
        (star_4_1 negation disjunction q p)
        (star_4_1 negation disjunction r p))
      (star_4_39 negation disjunction
        (q ⊃ᵣ p) (r ⊃ᵣ p)
        ((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ((∼ᵣ p) ⊃ᵣ (∼ᵣ r)))
  have line2 :
      ⊢ᵣ ((((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ∨ᵣ ((∼ᵣ p) ⊃ᵣ (∼ᵣ r))) ≡ᵣ
        ((∼ᵣ p) ⊃ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r)))) :=
    star_4_78 negation disjunction (∼ᵣ p) (∼ᵣ q) (∼ᵣ r)
  have line3 :
      ⊢ᵣ (((∼ᵣ p) ⊃ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r))) ≡ᵣ
        ((∼ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r))) ⊃ᵣ p)) :=
    star4_pair negation disjunction _ _
      (star_2_15 negation disjunction p ((∼ᵣ q) ∨ᵣ (∼ᵣ r)))
      (star_2_15 negation disjunction ((∼ᵣ q) ∨ᵣ (∼ᵣ r)) p)
  have line4 :
      ⊢ᵣ ((∼ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r)) ⊃ᵣ p) ≡ᵣ
        ((q ∧ᵣ r) ⊃ᵣ p)) :=
    star_4_2 negation disjunction
      ((∼ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r))) ⊃ᵣ p)
  have chain12 := star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ line1 line2)
    (star_4_22 negation disjunction
      ((q ⊃ᵣ p) ∨ᵣ (r ⊃ᵣ p))
      (((∼ᵣ p) ⊃ᵣ (∼ᵣ q)) ∨ᵣ ((∼ᵣ p) ⊃ᵣ (∼ᵣ r)))
      ((∼ᵣ p) ⊃ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r))))
  have chain13 := star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ chain12 line3)
    (star_4_22 negation disjunction
      ((q ⊃ᵣ p) ∨ᵣ (r ⊃ᵣ p))
      ((∼ᵣ p) ⊃ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r)))
      (∼ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r)) ⊃ᵣ p))
  exact star4_detach negation disjunction _ _
    (star4_pair negation disjunction _ _ chain13 line4)
    (star_4_22 negation disjunction
      ((q ⊃ᵣ p) ∨ᵣ (r ⊃ᵣ p))
      (∼ᵣ ((∼ᵣ q) ∨ᵣ (∼ᵣ r)) ⊃ᵣ p)
      ((q ∧ᵣ r) ⊃ᵣ p))

end

#print axioms star_4_01_unfold
#print axioms star_4_02
#print axioms star_4_02_unfold
#print axioms star_4_1
#print axioms star_4_13
#print axioms star_4_21
#print axioms star_4_3
#print axioms star_4_33
#print axioms star_4_34
#print axioms star_4_34_unfold
#print axioms star_4_5
#print axioms star_4_8
#print axioms star_4_81
#print axioms star_4_24
#print axioms star_4_25
#print axioms star_4_22
#print axioms star_4_2
#print axioms star_4_31
#print axioms star_4_71
#print axioms star_4_73
#print axioms star_4_38
#print axioms star_4_76
#print axioms star_4_36
#print axioms star_4_37
#print axioms star_4_39
#print axioms star_4_45
#print axioms star_4_44
#print axioms star_4_72
#print axioms star_4_82
#print axioms star_4_83
#print axioms star_4_84
#print axioms star_4_85
#print axioms star_4_12
#print axioms star_4_51
#print axioms star_4_4
#print axioms star_4_41
#print axioms star_4_7
#print axioms star_4_74
#print axioms star_4_77
#print axioms star_4_6
#print axioms star_4_11
#print axioms star_4_52
#print axioms star_4_53
#print axioms star_4_54
#print axioms star_4_55
#print axioms star_4_56
#print axioms star_4_57
#print axioms star_4_61
#print axioms star_4_62
#print axioms star_4_63
#print axioms star_4_64
#print axioms star_4_65
#print axioms star_4_66
#print axioms star_4_67
#print axioms star_4_42
#print axioms star_4_43
#print axioms star_4_32
#print axioms star_4_86
#print axioms star_4_87
#print axioms star_4_14
#print axioms star_4_15
#print axioms star_4_78
#print axioms star_4_79

namespace MixedOrder

/-- ✱4·21 with independent orders for `p` and `q`. -/
def star_4_21_formula
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :=
  binaryInterpret negation disjunction p q
    (PM.Elementary.equiv
      (PM.Elementary.equiv binaryP binaryQ)
      (PM.Elementary.equiv binaryQ binaryP))

theorem star_4_21
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    ⊢ᵣ star_4_21_formula negation disjunction p q := by
  exact binaryTransport negation disjunction p q
    (PM.FirstEdition.Volume1.Star4.star_4_21 binaryP binaryQ)

#print axioms star_4_21

/-- ✱4·37 with independent orders for `p`, `q`, and `r`. -/
def star_4_37_formula
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder) :=
  ternaryInterpret negation disjunction p q r
    ((ternaryP ≡ₚ ternaryQ) ⊃ₚ
      ((ternaryP ∨ₚ ternaryR) ≡ₚ (ternaryQ ∨ₚ ternaryR)))

theorem star_4_37
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder) :
    ⊢ᵣ star_4_37_formula negation disjunction p q r := by
  exact ternaryTransport negation disjunction p q r
    (PM.FirstEdition.Volume1.Star4.star_4_37 ternaryP ternaryQ ternaryR)

#print axioms star_4_37

end MixedOrder

end PM.RamifiedSyntax
