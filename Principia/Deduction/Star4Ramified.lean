import Principia.Deduction.Star3Ramified

/-!
# PM I, first edition, ✱4 in the ramified calculus

The propositions in this file live in `PM.RamifiedSyntax.Derivation` and use
the unconditional ramified reconstructions of ✱2 and ✱3.
-/

namespace PM.RamifiedSyntax

private theorem star4_detach
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    (⊢ᵣ p) → (⊢ᵣ implication negation disjunction p q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1 negation disjunction
  | cons head tail => exact Derivation.star_1_11 negation disjunction

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
    (Derivation.star_1_3 negation disjunction p p)
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
    ⊢ᵣ star_4_01 negation disjunction p p :=
  let ramified_Id := star_2_08 negation disjunction p
  let ramified_star_3_2 := star_3_2 negation disjunction
    (implication negation disjunction p p)
    (implication negation disjunction p p)
  let line1 := Derivation.star_9_12 negation disjunction
    ramified_Id ramified_star_3_2
  Derivation.star_9_12 negation disjunction ramified_Id line1

/-- ✱4·31, PM's printed `Perm` proof in both directions, packaged by ✱3·2. -/
theorem star_4_31
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    ⊢ᵣ star_4_01 negation disjunction
      (sameDisjunction disjunction p q)
      (sameDisjunction disjunction q p) :=
  let line1 := Derivation.star_1_4 negation disjunction p q
  let line2 := Derivation.star_1_4 negation disjunction q p
  let ramified_star_3_2 := star_3_2 negation disjunction
    (implication negation disjunction
      (sameDisjunction disjunction p q)
      (sameDisjunction disjunction q p))
    (implication negation disjunction
      (sameDisjunction disjunction q p)
      (sameDisjunction disjunction p q))
  let line3 := Derivation.star_9_12 negation disjunction
    line1 ramified_star_3_2
  Derivation.star_9_12 negation disjunction line2 line3

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
  star4_reading "✱4·36.  ⊢ : p ≡ q . ⊃ : p . r . ≡ . q . r"
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
  star4_reading "✱4·37.  ⊢ : p ≡ q . ⊃ : p ∨ r . ≡ . q ∨ r"
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
  have line1 := star4_compose negation disjunction _ _ _
    (star4_joinUnder negation disjunction e _ _
      (star_3_26 negation disjunction
        (implication negation disjunction p q) (implication negation disjunction q p))
      (star4_detach negation disjunction _ _
        (star_2_08 negation disjunction r)
        (star_2_02 negation disjunction e (implication negation disjunction r r))))
    (star_3_48 negation disjunction p r q r)
  have line2 := star4_compose negation disjunction _ _ _
    (star4_joinUnder negation disjunction e _ _
      (star_3_27 negation disjunction
        (implication negation disjunction p q) (implication negation disjunction q p))
      (star4_detach negation disjunction _ _
        (star_2_08 negation disjunction r)
        (star_2_02 negation disjunction e (implication negation disjunction r r))))
    (star_3_48 negation disjunction q r p r)
  exact star4_joinUnder negation disjunction e _ _ line1 line2

/-- Audited scope reading of ✱4·39. -/
def star_4_39_reading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r s : Formula signature real [] order) :=
  star4_reading "✱4·39.  ⊢ : p ≡ r . q ≡ s . ⊃ : p ∨ q . ≡ . r ∨ s   [✱3·48 . ✱4·32 . ✱3·22]"
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

#print axioms star_4_01_unfold
#print axioms star_4_1
#print axioms star_4_13
#print axioms star_4_21
#print axioms star_4_3
#print axioms star_4_33
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
#print axioms star_4_12

end PM.RamifiedSyntax
