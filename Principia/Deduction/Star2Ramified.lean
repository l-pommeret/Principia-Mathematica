import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-! # Derived propositions of PM I, ✱2, in the ramified calculus

These are the propositional derivations of ✱2 transported verbatim from the
elementary calculus to `Formula`.  All formulae have a common ramified order;
the only rules used below are the six primitive propositions of ✱1.
-/

section

variable {signature : Signature} {real : Context} {order : Nat}
variable (negation : signature.Negation order)
variable (disjunction : signature.Disjunction order)

local prefix:max "∼ᵣ" => Formula.neg negation
local infixr:55 " ∨ᵣ " => sameDisjunction disjunction
local infixr:54 " ⊃ᵣ " => implication negation disjunction

/-- Detachment in an arbitrary real context, using exactly ✱1·1 or ✱1·11. -/
private theorem detach {p q : Formula signature real [] order} :
    (⊢ᵣ p) → (⊢ᵣ (p ⊃ᵣ q)) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons realSort real => exact Derivation.star_1_11_same negation disjunction

/-- ✱2·01 (`Abs`), the printed Taut instance. -/
theorem star_2_01 (p : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ ∼ᵣ p) ⊃ᵣ ∼ᵣ p) :=
  Derivation.star_1_2 negation disjunction (∼ᵣ p)

/-- ✱2·02, the printed Perm instance followed by detachment. -/
theorem star_2_02 (p q : Formula signature real [] order) :
    ⊢ᵣ (q ⊃ᵣ (p ⊃ᵣ q)) :=
  Derivation.star_1_3_same negation disjunction (∼ᵣ p) q

/-- ✱2·03, the printed Assoc instance followed by detachment. -/
theorem star_2_03 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ ∼ᵣ q) ⊃ᵣ (q ⊃ᵣ ∼ᵣ p)) :=
  Derivation.star_1_4_same negation disjunction (∼ᵣ p) (∼ᵣ q)

/-- ✱2·04 (`Comm`), exactly the printed Assoc instance. -/
theorem star_2_04 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ (q ⊃ᵣ (p ⊃ᵣ r))) :=
  Derivation.star_1_5_same negation disjunction (∼ᵣ p) (∼ᵣ q) r

/-- ✱2·05, exactly the printed Sum instance. -/
theorem star_2_05 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ r))) :=
  Derivation.star_1_6_same negation disjunction (∼ᵣ p) q r

/-- ✱2·06 (`Syll`), Comm applied to ✱2·05, then detachment. -/
theorem star_2_06 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((q ⊃ᵣ r) ⊃ᵣ (p ⊃ᵣ r))) :=
  detach negation disjunction (star_2_05 negation disjunction p q r)
    (star_2_04 negation disjunction (q ⊃ᵣ r) (p ⊃ᵣ q) (p ⊃ᵣ r))

/-- ✱2·07, the direct Add instance. -/
theorem star_2_07 (p : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ (p ∨ᵣ p)) :=
  Derivation.star_1_3_same negation disjunction p p

/-- ✱2·08 (`Id`), preserving the two printed detachments. -/
theorem star_2_08 (p : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ p) :=
  detach negation disjunction (star_2_07 negation disjunction p)
    (detach negation disjunction
      (Derivation.star_1_2 negation disjunction p)
      (star_2_05 negation disjunction p (p ∨ᵣ p) p))

/-- ✱2·1, the disjunctive reading of Id. -/
theorem star_2_1 (p : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ∨ᵣ p) :=
  star_2_08 negation disjunction p

/-- ✱2·11, Perm applied to ✱2·1. -/
theorem star_2_11 (p : Formula signature real [] order) :
    ⊢ᵣ (p ∨ᵣ ∼ᵣ p) :=
  detach negation disjunction (star_2_1 negation disjunction p)
    (Derivation.star_1_4_same negation disjunction (∼ᵣ p) p)

/-- ✱2·12, the displayed ✱2·11 instance. -/
theorem star_2_12 (p : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ ∼ᵣ (∼ᵣ p)) :=
  star_2_11 negation disjunction (∼ᵣ p)

/-- ✱2·13, Sum and the two printed detachments. -/
theorem star_2_13 (p : Formula signature real [] order) :
    ⊢ᵣ (p ∨ᵣ ∼ᵣ (∼ᵣ (∼ᵣ p))) := by
  have line1 := Derivation.star_1_6_same negation disjunction p (∼ᵣ p)
    (∼ᵣ (∼ᵣ (∼ᵣ p)))
  have line2 := detach negation disjunction
    (star_2_12 negation disjunction (∼ᵣ p)) line1
  exact detach negation disjunction (star_2_11 negation disjunction p) line2

/-- ✱2·14, Perm followed by detachment. -/
theorem star_2_14 (p : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (∼ᵣ p) ⊃ᵣ p) := by
  have line1 := Derivation.star_1_4_same negation disjunction p
    (∼ᵣ (∼ᵣ (∼ᵣ p)))
  exact detach negation disjunction (star_2_13 negation disjunction p) line1

/-- ✱2·15, the complete printed eleven-line sorites. -/
theorem star_2_15 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ (∼ᵣ q ⊃ᵣ p)) := by
  have line1 := star_2_05 negation disjunction (∼ᵣ p) q (∼ᵣ (∼ᵣ q))
  have line2 := star_2_12 negation disjunction q
  have line3 := detach negation disjunction line2 line1
  have line4 := star_2_03 negation disjunction (∼ᵣ p) (∼ᵣ q)
  have line5 := star_2_05 negation disjunction (∼ᵣ q) (∼ᵣ (∼ᵣ p)) p
  have line6 := detach negation disjunction (star_2_14 negation disjunction p) line5
  have line7 := star_2_05 negation disjunction (∼ᵣ p ⊃ᵣ q)
    (∼ᵣ p ⊃ᵣ ∼ᵣ (∼ᵣ q)) (∼ᵣ q ⊃ᵣ ∼ᵣ (∼ᵣ p))
  have line8 := detach negation disjunction line4 line7
  have line9 := detach negation disjunction line3 line8
  have line10 := star_2_05 negation disjunction (∼ᵣ p ⊃ᵣ q)
    (∼ᵣ q ⊃ᵣ ∼ᵣ (∼ᵣ p)) (∼ᵣ q ⊃ᵣ p)
  have line11 := detach negation disjunction line6 line10
  exact detach negation disjunction line9 line11

/-- ✱2·16 (`Transp`). -/
theorem star_2_16 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ (∼ᵣ q ⊃ᵣ ∼ᵣ p)) := by
  have line1 := detach negation disjunction (star_2_12 negation disjunction q)
    (star_2_05 negation disjunction p q (∼ᵣ (∼ᵣ q)))
  have line2 := star_2_03 negation disjunction p (∼ᵣ q)
  have syll := detach negation disjunction line1
    (star_2_06 negation disjunction (p ⊃ᵣ q)
      (p ⊃ᵣ ∼ᵣ (∼ᵣ q)) (∼ᵣ q ⊃ᵣ ∼ᵣ p))
  exact detach negation disjunction line2 syll

/-- ✱2·17, converse transposition. -/
theorem star_2_17 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ q ⊃ᵣ ∼ᵣ p) ⊃ᵣ (p ⊃ᵣ q)) := by
  have line1 := star_2_03 negation disjunction (∼ᵣ q) p
  have line2 := detach negation disjunction (star_2_14 negation disjunction q)
    (star_2_05 negation disjunction p (∼ᵣ (∼ᵣ q)) q)
  have syll := detach negation disjunction line1
    (star_2_06 negation disjunction (∼ᵣ q ⊃ᵣ ∼ᵣ p)
      (p ⊃ᵣ ∼ᵣ (∼ᵣ q)) (p ⊃ᵣ q))
  exact detach negation disjunction line2 syll

/-- ✱2·18, the complete printed four-line reductio complement. -/
theorem star_2_18 (p : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ p) ⊃ᵣ p) := by
  have line1 := detach negation disjunction (star_2_12 negation disjunction p)
    (star_2_05 negation disjunction (∼ᵣ p) p (∼ᵣ (∼ᵣ p)))
  have line2 := star_2_01 negation disjunction (∼ᵣ p)
  have syll1 := detach negation disjunction line1
    (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ p)
      (∼ᵣ p ⊃ᵣ ∼ᵣ (∼ᵣ p)) (∼ᵣ (∼ᵣ p)))
  have line3 := detach negation disjunction line2 syll1
  have line4 := star_2_14 negation disjunction p
  have syll2 := detach negation disjunction line3
    (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ p) (∼ᵣ (∼ᵣ p)) p)
  exact detach negation disjunction line4 syll2

/-- ✱2·2, Add, Perm, then Syll. -/
theorem star_2_2 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ (p ∨ᵣ q)) := by
  have line1 := Derivation.star_1_3_same negation disjunction q p
  have line2 := Derivation.star_1_4_same negation disjunction q p
  exact detach negation disjunction line1
    (detach negation disjunction line2
      (star_2_05 negation disjunction p (q ∨ᵣ p) (p ∨ᵣ q)))

/-- ✱2·21, the printed ✱2·2 substitution instance. -/
theorem star_2_21 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ⊃ᵣ (p ⊃ᵣ q)) :=
  star_2_2 negation disjunction (∼ᵣ p) q

theorem star_2_24 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := by
  have comm := star_2_04 negation disjunction (∼ᵣ p) p q
  exact detach negation disjunction (star_2_21 negation disjunction p q) comm


theorem star_2_25 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ∨ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := by
  have line1 : ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ∨ᵣ (p ∨ᵣ q)) := star_2_1 negation disjunction (p ∨ᵣ q)
  have assoc := Derivation.star_1_5_same negation disjunction (∼ᵣ (p ∨ᵣ q)) p q
  exact detach negation disjunction line1 assoc


theorem star_2_26 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ∨ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) :=
  star_2_25 negation disjunction (∼ᵣ p) q


theorem star_2_27 (p q : Formula signature real [] order) :
    ⊢ᵣ (p ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) :=
  star_2_26 negation disjunction p q


theorem star_2_3 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ r)) ⊃ᵣ (p ∨ᵣ (r ∨ᵣ q))) :=
  detach negation disjunction
    (Derivation.star_1_4_same negation disjunction q r)
    (Derivation.star_1_6_same negation disjunction p (q ∨ᵣ r) (r ∨ᵣ q))


theorem star_2_31 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ r)) :=
  detach negation disjunction
    (detach negation disjunction
      (star_2_3 negation disjunction p q r)
      (detach negation disjunction
        (Derivation.star_1_5_same negation disjunction p r q)
        (star_2_05 negation disjunction (p ∨ᵣ (q ∨ᵣ r)) (p ∨ᵣ (r ∨ᵣ q)) (r ∨ᵣ (p ∨ᵣ q)))))
    (detach negation disjunction
      (Derivation.star_1_4_same negation disjunction r (p ∨ᵣ q))
      (star_2_05 negation disjunction (p ∨ᵣ (q ∨ᵣ r)) (r ∨ᵣ (p ∨ᵣ q)) ((p ∨ᵣ q) ∨ᵣ r)))


theorem star_2_32 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ r))) :=
  detach negation disjunction
    (detach negation disjunction
      (Derivation.star_1_4_same negation disjunction (p ∨ᵣ q) r)
      (detach negation disjunction
        (Derivation.star_1_5_same negation disjunction r p q)
        (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (r ∨ᵣ (p ∨ᵣ q)) (p ∨ᵣ (r ∨ᵣ q)))))
    (detach negation disjunction
      (star_2_3 negation disjunction p r q)
      (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (p ∨ᵣ (r ∨ᵣ q)) (p ∨ᵣ (q ∨ᵣ r))))


theorem star_2_36 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p))) := by
  have perm : ⊢ᵣ ((p ∨ᵣ r) ⊃ᵣ (r ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p r
  have syll : ⊢ᵣ (((p ∨ᵣ r) ⊃ᵣ (r ∨ᵣ p)) ⊃ᵣ
      (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p)))) :=
    star_2_05 negation disjunction (p ∨ᵣ q) (p ∨ᵣ r) (r ∨ᵣ p)
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p))) :=
    detach negation disjunction perm syll
  have line2 : ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    Derivation.star_1_6_same negation disjunction p q r
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_05 negation disjunction (q ⊃ᵣ r) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ p))))


theorem star_2_37 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))) := by
  have permIn : ⊢ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ q)) := Derivation.star_1_4_same negation disjunction q p
  have syll : ⊢ᵣ (((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ q)) ⊃ᵣ
      (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r)))) :=
    star_2_06 negation disjunction (q ∨ᵣ p) (p ∨ᵣ q) (p ∨ᵣ r)
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction permIn syll
  have sumStep : ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    Derivation.star_1_6_same negation disjunction p q r
  exact detach negation disjunction sumStep
    (detach negation disjunction line1
      (star_2_05 negation disjunction (q ⊃ᵣ r) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))))


theorem star_2_38 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))) := by
  have permIn : ⊢ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ q)) := Derivation.star_1_4_same negation disjunction q p
  have permOut : ⊢ᵣ ((p ∨ᵣ r) ⊃ᵣ (r ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p r
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction permIn (star_2_06 negation disjunction (q ∨ᵣ p) (p ∨ᵣ q) (p ∨ᵣ r))
  have line2 : ⊢ᵣ (((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))) :=
    detach negation disjunction permOut (star_2_05 negation disjunction (q ∨ᵣ p) (p ∨ᵣ r) (r ∨ᵣ p))
  have line3 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))) :=
    detach negation disjunction line2
      (detach negation disjunction line1
        (star_2_06 negation disjunction ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))))
  have sumStep : ⊢ᵣ ((q ⊃ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    Derivation.star_1_6_same negation disjunction p q r
  exact detach negation disjunction sumStep
    (detach negation disjunction line3
      (star_2_05 negation disjunction (q ⊃ᵣ r) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ⊃ᵣ (r ∨ᵣ p))))


theorem star_2_41 (p q : Formula signature real [] order) :
    ⊢ᵣ ((q ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ q)) := by
  have assoc : ⊢ᵣ ((q ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ q))) := Derivation.star_1_5_same negation disjunction q p q
  have taut : ⊢ᵣ ((q ∨ᵣ q) ⊃ᵣ q) := Derivation.star_1_2 negation disjunction q
  have line2 : ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ q)) :=
    detach negation disjunction taut (Derivation.star_1_6_same negation disjunction p (q ∨ᵣ q) q)
  exact detach negation disjunction assoc
    (detach negation disjunction line2
      (star_2_05 negation disjunction (q ∨ᵣ (p ∨ᵣ q)) (p ∨ᵣ (q ∨ᵣ q)) (p ∨ᵣ q)))


theorem star_2_4 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ (p ∨ᵣ q)) := by
  have assoc : ⊢ᵣ ((p ∨ᵣ (p ∨ᵣ q)) ⊃ᵣ ((p ∨ᵣ p) ∨ᵣ q)) := star_2_31 negation disjunction p p q
  have taut : ⊢ᵣ ((p ∨ᵣ p) ⊃ᵣ p) := Derivation.star_1_2 negation disjunction p
  have lifted : ⊢ᵣ (((p ∨ᵣ p) ∨ᵣ q) ⊃ᵣ (p ∨ᵣ q)) :=
    detach negation disjunction taut (star_2_38 negation disjunction q (p ∨ᵣ p) p)
  exact detach negation disjunction assoc
    (detach negation disjunction lifted
      (star_2_05 negation disjunction (p ∨ᵣ (p ∨ᵣ q)) ((p ∨ᵣ p) ∨ᵣ q) (p ∨ᵣ q)))


theorem star_2_42 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ∨ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ q)) :=
  star_2_4 negation disjunction (∼ᵣ p) q


theorem star_2_43 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ q)) :=
  star_2_42 negation disjunction p q


theorem star_2_45 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ ∼ᵣ p) := by
  exact detach negation disjunction (star_2_2 negation disjunction p q) (star_2_16 negation disjunction p (p ∨ᵣ q))


theorem star_2_46 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ ∼ᵣ q) := by
  exact detach negation disjunction (Derivation.star_1_3_same negation disjunction p q)
    (star_2_16 negation disjunction q (p ∨ᵣ q))


theorem star_2_47 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ (∼ᵣ p ∨ᵣ q)) := by
  exact detach negation disjunction (star_2_45 negation disjunction p q)
    (detach negation disjunction (star_2_2 negation disjunction (∼ᵣ p) q)
      (star_2_05 negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ p) (∼ᵣ p ∨ᵣ q)))


theorem star_2_48 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ ∼ᵣ q)) := by
  exact detach negation disjunction (star_2_46 negation disjunction p q)
    (detach negation disjunction (Derivation.star_1_3_same negation disjunction p (∼ᵣ q))
      (star_2_05 negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ q) (p ∨ᵣ ∼ᵣ q)))


theorem star_2_49 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ∨ᵣ q) ⊃ᵣ (∼ᵣ p ∨ᵣ ∼ᵣ q)) := by
  exact detach negation disjunction (star_2_45 negation disjunction p q)
    (detach negation disjunction (star_2_2 negation disjunction (∼ᵣ p) (∼ᵣ q))
      (star_2_05 negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ p) (∼ᵣ p ∨ᵣ ∼ᵣ q)))


theorem star_2_5 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := by
  exact star_2_47 negation disjunction (∼ᵣ p) q


theorem star_2_51 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ ∼ᵣ q)) := by
  exact star_2_48 negation disjunction (∼ᵣ p) q


theorem star_2_52 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ ∼ᵣ q)) := by
  exact star_2_49 negation disjunction (∼ᵣ p) q


theorem star_2_521 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (q ⊃ᵣ p)) := by
  have line1 : ⊢ᵣ (∼ᵣ (p ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ ∼ᵣ q)) :=
    star_2_52 negation disjunction p q
  have line2 : ⊢ᵣ ((∼ᵣ p ⊃ᵣ ∼ᵣ q) ⊃ᵣ (q ⊃ᵣ p)) :=
    star_2_17 negation disjunction q p
  have syll := star_2_05 negation disjunction
    (∼ᵣ (p ⊃ᵣ q)) (∼ᵣ p ⊃ᵣ ∼ᵣ q) (q ⊃ᵣ p)
  exact detach negation disjunction line1
    (detach negation disjunction line2 syll)


theorem star_2_53 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := by
  have lift : ⊢ᵣ ((p ⊃ᵣ ∼ᵣ (∼ᵣ p)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (∼ᵣ (∼ᵣ p) ∨ᵣ q))) :=
    star_2_38 negation disjunction q p (∼ᵣ (∼ᵣ p))
  exact detach negation disjunction (star_2_12 negation disjunction p) lift


theorem star_2_54 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ (p ∨ᵣ q)) := by
  have lift : ⊢ᵣ ((∼ᵣ (∼ᵣ p) ⊃ᵣ p) ⊃ᵣ ((∼ᵣ (∼ᵣ p) ∨ᵣ q) ⊃ᵣ (p ∨ᵣ q))) :=
    star_2_38 negation disjunction q (∼ᵣ (∼ᵣ p)) p
  exact detach negation disjunction (star_2_14 negation disjunction p) lift


theorem star_2_55 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ p ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_53 negation disjunction p q) (star_2_04 negation disjunction (p ∨ᵣ q) (∼ᵣ p) q)


theorem star_2_56 (p q : Formula signature real [] order) :
    ⊢ᵣ (∼ᵣ q ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ p)) := by
  have inst : ⊢ᵣ (∼ᵣ q ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ p)) := star_2_55 negation disjunction q p
  have perm : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p q
  have syll : ⊢ᵣ (((q ∨ᵣ p) ⊃ᵣ p) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ p)) :=
    detach negation disjunction perm (star_2_06 negation disjunction (p ∨ᵣ q) (q ∨ᵣ p) p)
  have lift : ⊢ᵣ ((∼ᵣ q ⊃ᵣ ((q ∨ᵣ p) ⊃ᵣ p)) ⊃ᵣ (∼ᵣ q ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ p))) :=
    detach negation disjunction syll
      (star_2_05 negation disjunction (∼ᵣ q) ((q ∨ᵣ p) ⊃ᵣ p) ((p ∨ᵣ q) ⊃ᵣ p))
  exact detach negation disjunction inst lift


theorem star_2_6 (p q : Formula signature real [] order) :
    ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) := by
  have line1 : ⊢ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ ((∼ᵣ p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ q))) :=
    star_2_38 negation disjunction q (∼ᵣ p) q
  have line2 : ⊢ᵣ (((∼ᵣ p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ q)) ⊃ᵣ ((∼ᵣ p ∨ᵣ q) ⊃ᵣ q)) :=
    detach negation disjunction (Derivation.star_1_2 negation disjunction q)
      (star_2_05 negation disjunction (∼ᵣ p ∨ᵣ q) (q ∨ᵣ q) q)
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ q) ((∼ᵣ p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ q)) ((∼ᵣ p ∨ᵣ q) ⊃ᵣ q)))


theorem star_2_61 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_6 negation disjunction p q)
    (star_2_04 negation disjunction (∼ᵣ p ⊃ᵣ q) (p ⊃ᵣ q) q)


theorem star_2_62 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_6 negation disjunction p q)
    (detach negation disjunction (star_2_53 negation disjunction p q)
      (star_2_06 negation disjunction (p ∨ᵣ q) (∼ᵣ p ⊃ᵣ q) ((p ⊃ᵣ q) ⊃ᵣ q)))


theorem star_2_621 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := by
  exact detach negation disjunction (star_2_62 negation disjunction p q)
    (star_2_04 negation disjunction (p ∨ᵣ q) (p ⊃ᵣ q) q)


theorem star_2_63 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((∼ᵣ p ∨ᵣ q) ⊃ᵣ q)) := by
  -- [✱2·62], definitional reading only
  exact star_2_62 negation disjunction p q


theorem star_2_64 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ ∼ᵣ q) ⊃ᵣ p)) := by
  -- [✱2·63 (q,p)/(p,q).Perm]
  -- Perm in front of the outer antecedent, applied to ✱2·63 with `(q,p)/(p,q)`:
  have s : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((∼ᵣ q ∨ᵣ p) ⊃ᵣ p)) :=
    detach negation disjunction (star_2_63 negation disjunction q p)
      (detach negation disjunction (Derivation.star_1_4_same negation disjunction p q)
        (star_2_06 negation disjunction (p ∨ᵣ q) (q ∨ᵣ p) ((∼ᵣ q ∨ᵣ p) ⊃ᵣ p)))
  -- Perm in front of the inner antecedent:
  have t : ⊢ᵣ (((∼ᵣ q ∨ᵣ p) ⊃ᵣ p) ⊃ᵣ ((p ∨ᵣ ∼ᵣ q) ⊃ᵣ p)) :=
    detach negation disjunction (Derivation.star_1_4_same negation disjunction p (∼ᵣ q))
      (star_2_06 negation disjunction (p ∨ᵣ ∼ᵣ q) (∼ᵣ q ∨ᵣ p) p)
  exact detach negation disjunction t
    (detach negation disjunction s
      (star_2_06 negation disjunction (p ∨ᵣ q) ((∼ᵣ q ∨ᵣ p) ⊃ᵣ p) ((p ∨ᵣ ∼ᵣ q) ⊃ᵣ p)))


theorem star_2_65 (p q : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((p ⊃ᵣ ∼ᵣ q) ⊃ᵣ ∼ᵣ p)) := by
  -- [✱2·64 ∼p/p]
  exact star_2_64 negation disjunction (∼ᵣ p) q


theorem star_2_67 (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ q)) := by
  -- Preserve printed lines (1), (2), then final Syll.
  have line1 : ⊢ᵣ ((((p ∨ᵣ q) ⊃ᵣ q)) ⊃ᵣ ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q)) :=
    detach negation disjunction (star_2_54 negation disjunction p q)
      (star_2_06 negation disjunction (∼ᵣ p ⊃ᵣ q) (p ∨ᵣ q) q)
  have line2 : ⊢ᵣ (((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ q)) :=
    detach negation disjunction (star_2_24 negation disjunction p q)
      (star_2_06 negation disjunction p (∼ᵣ p ⊃ᵣ q) q)
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_06 negation disjunction ((p ∨ᵣ q) ⊃ᵣ q) ((∼ᵣ p ⊃ᵣ q) ⊃ᵣ q) (p ⊃ᵣ q)))


theorem star_2_68 (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ (p ∨ᵣ q)) := by
  -- [✱2·67 ∼p/p], then ✱2·54.
  have inst : ⊢ᵣ ((((∼ᵣ p) ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (∼ᵣ p ⊃ᵣ q)) := star_2_67 negation disjunction (∼ᵣ p) q
  exact detach negation disjunction (star_2_54 negation disjunction p q)
    (detach negation disjunction inst
      (star_2_06 negation disjunction ((p ⊃ᵣ q) ⊃ᵣ q) (∼ᵣ p ⊃ᵣ q) (p ∨ᵣ q)))


theorem star_2_69 (p q : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ ((q ⊃ᵣ p) ⊃ᵣ p)) := by
  -- [✱2·68.Perm.✱2·62 (q,p)/(p,q)].
  have perm : ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ q) ⊃ᵣ (q ∨ᵣ p)) :=
    detach negation disjunction (Derivation.star_1_4_same negation disjunction p q)
      (detach negation disjunction (star_2_68 negation disjunction p q)
        (star_2_06 negation disjunction ((p ⊃ᵣ q) ⊃ᵣ q) (p ∨ᵣ q) (q ∨ᵣ p)))
  exact detach negation disjunction (star_2_62 negation disjunction q p)
    (detach negation disjunction perm
      (star_2_06 negation disjunction ((p ⊃ᵣ q) ⊃ᵣ q) (q ∨ᵣ p) ((q ⊃ᵣ p) ⊃ᵣ p)))


theorem star_2_73 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))) := by
  have first : ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) := star_2_621 negation disjunction p q
  have second : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))) :=
    star_2_38 negation disjunction r (p ∨ᵣ q) q
  have syll :
      ⊢ᵣ ((((p ∨ᵣ q) ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))) ⊃ᵣ
          (((p ⊃ᵣ q) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ q)) ⊃ᵣ
            ((p ⊃ᵣ q) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))))) :=
    Derivation.star_1_6_same negation disjunction (∼ᵣ (p ⊃ᵣ q)) ((p ∨ᵣ q) ⊃ᵣ q)
      (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (q ∨ᵣ r))
  exact detach negation disjunction first (detach negation disjunction second syll)


theorem star_2_74 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ p) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) := by
  have line1 := star_2_73 negation disjunction q p r
  have line2 := star_2_32 negation disjunction p q r
  have line3 := Derivation.star_1_5_same negation disjunction p q r
  have line4 := star_2_31 negation disjunction q p r
  have line5 := detach negation disjunction line2
    (detach negation disjunction line3
      (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (p ∨ᵣ (q ∨ᵣ r)) (q ∨ᵣ (p ∨ᵣ r))))
  have line6 := detach negation disjunction line5
    (detach negation disjunction line4
      (star_2_05 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) (q ∨ᵣ (p ∨ᵣ r)) ((q ∨ᵣ p) ∨ᵣ r)))
  have line7 :
      ⊢ᵣ ((((q ∨ᵣ p) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction line6
      (star_2_06 negation disjunction ((p ∨ᵣ q) ∨ᵣ r) ((q ∨ᵣ p) ∨ᵣ r) (p ∨ᵣ r))
  have line8 := detach negation disjunction line1
    (detach negation disjunction line7
      (star_2_05 negation disjunction (q ⊃ᵣ p) (((q ∨ᵣ p) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))
        (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))))
  exact line8


theorem star_2_75 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ (p ∨ᵣ r))) := by
  have perm : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (q ∨ᵣ p)) := Derivation.star_1_4_same negation disjunction p q
  have fromDisj : ⊢ᵣ ((q ∨ᵣ p) ⊃ᵣ (∼ᵣ q ⊃ᵣ p)) := star_2_53 negation disjunction q p
  have hyp : ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (∼ᵣ q ⊃ᵣ p)) :=
    detach negation disjunction perm
      (detach negation disjunction fromDisj
        (Derivation.star_1_6_same negation disjunction (∼ᵣ (p ∨ᵣ q)) (q ∨ᵣ p) (∼ᵣ q ⊃ᵣ p)))
  have shifted :
      ⊢ᵣ ((∼ᵣ q ⊃ᵣ p) ⊃ᵣ (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) :=
    star_2_74 negation disjunction p (∼ᵣ q) r
  have curried :
      ⊢ᵣ ((p ∨ᵣ q) ⊃ᵣ (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction hyp
      (detach negation disjunction shifted
        (Derivation.star_1_6_same negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ q ⊃ᵣ p)
          (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ r))))
  have commuted :
      ⊢ᵣ (((p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction curried
      (Derivation.star_1_5_same negation disjunction (∼ᵣ (p ∨ᵣ q)) (∼ᵣ ((p ∨ᵣ ∼ᵣ q) ∨ᵣ r)) (p ∨ᵣ r))
  have assoc : ⊢ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∨ᵣ ∼ᵣ q) ∨ᵣ r)) :=
    star_2_31 negation disjunction p (∼ᵣ q) r
  have joined :
      ⊢ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) :=
    detach negation disjunction assoc
      (detach negation disjunction commuted
        (Derivation.star_1_6_same negation disjunction (∼ᵣ (p ∨ᵣ (q ⊃ᵣ r))) ((p ∨ᵣ ∼ᵣ q) ∨ᵣ r)
          ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))))
  exact detach negation disjunction joined
    (Derivation.star_1_5_same negation disjunction (∼ᵣ (p ∨ᵣ (q ⊃ᵣ r))) (∼ᵣ (p ∨ᵣ q)) (p ∨ᵣ r))


theorem star_2_76 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ∨ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r))) := by
  exact detach negation disjunction (star_2_75 negation disjunction p q r)
    (star_2_04 negation disjunction (p ∨ᵣ q) (p ∨ᵣ (q ⊃ᵣ r)) (p ∨ᵣ r))


theorem star_2_77 (p q r : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ r))) := by
  exact star_2_76 negation disjunction (∼ᵣ p) q r


theorem star_2_8 (q r s : Formula signature real [] order) :
    ⊢ᵣ ((q ∨ᵣ r) ⊃ᵣ ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s))) := by
  have perm : ⊢ᵣ ((q ∨ᵣ r) ⊃ᵣ (r ∨ᵣ q)) :=
    Derivation.star_1_4_same negation disjunction q r
  have permFlipped : ⊢ᵣ ((r ∨ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) :=
    detach negation disjunction perm
      (Derivation.star_1_4_same negation disjunction (∼ᵣ (q ∨ᵣ r)) (r ∨ᵣ q))
  have fiftyThree : ⊢ᵣ ((r ∨ᵣ q) ⊃ᵣ (∼ᵣ r ⊃ᵣ q)) := star_2_53 negation disjunction r q
  have sumFiftyThree :
      ⊢ᵣ (((r ∨ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) ⊃ᵣ ((∼ᵣ r ⊃ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r))) :=
    detach negation disjunction fiftyThree
      (star_2_38 negation disjunction (∼ᵣ (q ∨ᵣ r)) (r ∨ᵣ q) (∼ᵣ r ⊃ᵣ q))
  have line1 : ⊢ᵣ ((∼ᵣ r ⊃ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) :=
    detach negation disjunction permFlipped sumFiftyThree
  have line2 : ⊢ᵣ ((∼ᵣ r ⊃ᵣ q) ⊃ᵣ ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s))) :=
    star_2_38 negation disjunction s (∼ᵣ r) q
  have sumLine2 :
      ⊢ᵣ (((∼ᵣ r ⊃ᵣ q) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) ⊃ᵣ
        (((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)) ∨ᵣ ∼ᵣ (q ∨ᵣ r))) :=
    detach negation disjunction line2
      (star_2_38 negation disjunction (∼ᵣ (q ∨ᵣ r)) (∼ᵣ r ⊃ᵣ q) ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)))
  have line3 : ⊢ᵣ (((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)) ∨ᵣ ∼ᵣ (q ∨ᵣ r)) :=
    detach negation disjunction line1 sumLine2
  exact detach negation disjunction line3
    (Derivation.star_1_4_same negation disjunction
      ((∼ᵣ r ∨ᵣ s) ⊃ᵣ (q ∨ᵣ s)) (∼ᵣ (q ∨ᵣ r)))


theorem star_2_81 (p q r s : Formula signature real [] order) :
    ⊢ᵣ ((q ⊃ᵣ (r ⊃ᵣ s)) ⊃ᵣ
      ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))) := by
  have line1 :
      ⊢ᵣ ((q ⊃ᵣ (r ⊃ᵣ s)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ (r ⊃ᵣ s)))) :=
    Derivation.star_1_6_same negation disjunction p q (r ⊃ᵣ s)
  have line2 :
      ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ (r ⊃ᵣ s))) ⊃ᵣ
        ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))) :=
    detach negation disjunction (star_2_76 negation disjunction p r s)
      (star_2_05 negation disjunction (p ∨ᵣ q) (p ∨ᵣ (r ⊃ᵣ s)) ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))
  exact detach negation disjunction line2
    (detach negation disjunction line1
      (star_2_06 negation disjunction (q ⊃ᵣ (r ⊃ᵣ s)) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ (r ⊃ᵣ s)))
        ((p ∨ᵣ q) ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ (p ∨ᵣ s)))))


theorem star_2_82 (p q r s : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ s))) := by
  have compose : ∀ A B C : Formula signature real [] order, (⊢ᵣ (A ⊃ᵣ B)) →
      (⊢ᵣ (B ⊃ᵣ C)) → (⊢ᵣ (A ⊃ᵣ C)) := by
    intro A B C h₁ h₂
    exact detach negation disjunction h₁
      (detach negation disjunction h₂ (star_2_05 negation disjunction A B C))
  have printed :
      ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ r)) ⊃ᵣ
        ((p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ s)))) :=
    detach negation disjunction (star_2_8 negation disjunction q r s)
      (star_2_81 negation disjunction p (q ∨ᵣ r) (∼ᵣ r ∨ᵣ s) (q ∨ᵣ s))
  have antecedent : ⊢ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ r))) :=
    star_2_32 negation disjunction p q r
  have innerAntecedent :
      ⊢ᵣ (((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ (p ∨ᵣ (∼ᵣ r ∨ᵣ s))) :=
    star_2_32 negation disjunction p (∼ᵣ r) s
  have conclusion : ⊢ᵣ ((p ∨ᵣ (q ∨ᵣ s)) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ s)) :=
    star_2_31 negation disjunction p q s
  have inner :
      ⊢ᵣ (((p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ (p ∨ᵣ (q ∨ᵣ s))) ⊃ᵣ
        (((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((p ∨ᵣ q) ∨ᵣ s))) :=
    compose _ _ _
      (detach negation disjunction innerAntecedent
        (star_2_06 negation disjunction ((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) (p ∨ᵣ (∼ᵣ r ∨ᵣ s)) (p ∨ᵣ (q ∨ᵣ s))))
      (detach negation disjunction conclusion
        (star_2_05 negation disjunction ((p ∨ᵣ ∼ᵣ r) ∨ᵣ s) (p ∨ᵣ (q ∨ᵣ s)) ((p ∨ᵣ q) ∨ᵣ s)))
  exact compose _ _ _ (compose _ _ _ antecedent printed) inner


theorem star_2_83 (p q r s : Formula signature real [] order) :
    ⊢ᵣ ((p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ
      ((p ⊃ᵣ (r ⊃ᵣ s)) ⊃ᵣ (p ⊃ᵣ (q ⊃ᵣ s)))) := by
  have compose : ∀ A B C : Formula signature real [] order, (⊢ᵣ (A ⊃ᵣ B)) →
      (⊢ᵣ (B ⊃ᵣ C)) → (⊢ᵣ (A ⊃ᵣ C)) := by
    intro A B C h₁ h₂
    exact detach negation disjunction h₁
      (detach negation disjunction h₂ (star_2_05 negation disjunction A B C))
  have printed :
      ⊢ᵣ (((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ r) ⊃ᵣ
        (((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s))) :=
    star_2_82 negation disjunction (∼ᵣ p) (∼ᵣ q) r s
  have antecedent :
      ⊢ᵣ ((∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ r)) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ r)) :=
    star_2_31 negation disjunction (∼ᵣ p) (∼ᵣ q) r
  have innerAntecedent :
      ⊢ᵣ ((∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s)) :=
    star_2_31 negation disjunction (∼ᵣ p) (∼ᵣ r) s
  have conclusion :
      ⊢ᵣ (((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s) ⊃ᵣ (∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ s))) :=
    star_2_32 negation disjunction (∼ᵣ p) (∼ᵣ q) s
  have inner :
      ⊢ᵣ ((((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s) ⊃ᵣ ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s)) ⊃ᵣ
        ((∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ⊃ᵣ (∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ s)))) :=
    compose _ _ _
      (detach negation disjunction innerAntecedent
        (star_2_06 negation disjunction (∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ((∼ᵣ p ∨ᵣ ∼ᵣ r) ∨ᵣ s)
          ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s)))
      (detach negation disjunction conclusion
        (star_2_05 negation disjunction (∼ᵣ p ∨ᵣ (∼ᵣ r ∨ᵣ s)) ((∼ᵣ p ∨ᵣ ∼ᵣ q) ∨ᵣ s)
          (∼ᵣ p ∨ᵣ (∼ᵣ q ∨ᵣ s))))
  exact compose _ _ _ (compose _ _ _ antecedent printed) inner


theorem star_2_85 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (p ∨ᵣ (q ⊃ᵣ r))) := by
  have line1 : ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ r) ⊃ᵣ (q ⊃ᵣ r)) :=
    detach negation disjunction (Derivation.star_1_3_same negation disjunction p q) (star_2_06 negation disjunction q (p ∨ᵣ q) r)
  have fiftyFive : ⊢ᵣ (∼ᵣ p ⊃ᵣ ((p ∨ᵣ r) ⊃ᵣ r)) := star_2_55 negation disjunction p r
  have syll :
      ⊢ᵣ (((p ∨ᵣ r) ⊃ᵣ r) ⊃ᵣ
        (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ r))) :=
    star_2_05 negation disjunction (p ∨ᵣ q) (p ∨ᵣ r) r
  have half :
      ⊢ᵣ (∼ᵣ p ⊃ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ r))) :=
    detach negation disjunction syll
      (detach negation disjunction fiftyFive
        (star_2_06 negation disjunction (∼ᵣ p) ((p ∨ᵣ r) ⊃ᵣ r)
          (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ r))))
  have line1' : ⊢ᵣ (∼ᵣ p ⊃ᵣ (((p ∨ᵣ q) ⊃ᵣ r) ⊃ᵣ (q ⊃ᵣ r))) :=
    detach negation disjunction line1
      (Derivation.star_1_3_same negation disjunction (∼ᵣ (∼ᵣ p)) (((p ∨ᵣ q) ⊃ᵣ r) ⊃ᵣ (q ⊃ᵣ r)))
  have line2 :
      ⊢ᵣ (∼ᵣ p ⊃ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (q ⊃ᵣ r))) :=
    detach negation disjunction line1'
      (detach negation disjunction half
        (star_2_83 negation disjunction (∼ᵣ p) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ((p ∨ᵣ q) ⊃ᵣ r) (q ⊃ᵣ r)))
  have commuted :
      ⊢ᵣ (((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) ⊃ᵣ (∼ᵣ p ⊃ᵣ (q ⊃ᵣ r))) :=
    detach negation disjunction line2
      (star_2_04 negation disjunction (∼ᵣ p) ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) (q ⊃ᵣ r))
  exact detach negation disjunction (star_2_54 negation disjunction p (q ⊃ᵣ r))
    (detach negation disjunction commuted
      (star_2_06 negation disjunction ((p ∨ᵣ q) ⊃ᵣ (p ∨ᵣ r)) (∼ᵣ p ⊃ᵣ (q ⊃ᵣ r))
        (p ∨ᵣ (q ⊃ᵣ r))))


theorem star_2_86 (p q r : Formula signature real [] order) :
    ⊢ᵣ (((p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ (q ⊃ᵣ r))) :=
  star_2_85 negation disjunction (∼ᵣ p) q r



end

end PM.RamifiedSyntax

#print axioms PM.RamifiedSyntax.star_2_01
#print axioms PM.RamifiedSyntax.star_2_02
#print axioms PM.RamifiedSyntax.star_2_03
#print axioms PM.RamifiedSyntax.star_2_04
#print axioms PM.RamifiedSyntax.star_2_05
#print axioms PM.RamifiedSyntax.star_2_06
#print axioms PM.RamifiedSyntax.star_2_08
#print axioms PM.RamifiedSyntax.star_2_15
#print axioms PM.RamifiedSyntax.star_2_16
#print axioms PM.RamifiedSyntax.star_2_17
#print axioms PM.RamifiedSyntax.star_2_21
