import Principia.Deduction.Star2Ramified

namespace PM.RamifiedSyntax

/-! Ramified reconstruction of PM I, ✱3, from unconditional ramified ✱2 results. -/

abbrev RFormula (signature : Signature) (real : Context) (order : Nat) :=
  Formula signature real [] order

section

variable {signature : Signature} {real : Context} {order : Nat}
variable (negation : signature.Negation order)
variable (disjunction : signature.Disjunction order)

local prefix:75 "∼ᵣ " => Formula.neg negation
local infixl:65 " ∨ᵣ " => sameDisjunction disjunction
local infixr:60 " ⊃ᵣ " => implication negation disjunction

/-- ✱3·01. Logical product is an eliminable abbreviation. -/
def conjunction (p q : RFormula signature real order) :
    RFormula signature real order :=
  ∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))

local infixl:64 " ∧ᵣ " => conjunction negation disjunction

/-- ✱3·02. A chain is the product of its adjacent implications. -/
def implicationChain (p q r : RFormula signature real order) :
    RFormula signature real order :=
  (p ⊃ᵣ q) ∧ᵣ (q ⊃ᵣ r)

theorem star_3_01 (p q : RFormula signature real order) :
    p ∧ᵣ q = ∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) := rfl

theorem star_3_02 (p q r : RFormula signature real order) :
    implicationChain negation disjunction p q r = (p ⊃ᵣ q) ∧ᵣ (q ⊃ᵣ r) := rfl

def star_3_01_printed : String := "p . q .=. ∼(∼p ∨ ∼q)     Df"
def star_3_02_printed : String := "p ⊃ q ⊃ r .=. p ⊃ q . q ⊃ r     Df"

/-- Detachment at an arbitrary real context, using only ✱1·1/✱1·11. -/
private theorem detach (p q : RFormula signature real order) :
    (⊢ᵣ p) → (⊢ᵣ p ⊃ᵣ q) → (⊢ᵣ q) := by
  cases real with
  | nil => exact Derivation.star_1_1_same negation disjunction
  | cons head tail => exact Derivation.star_1_11_same negation disjunction

theorem star_3_1 (p q : RFormula signature real order) :
    ⊢ᵣ (p ∧ᵣ q) ⊃ᵣ (∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))) := by
  exact star_2_08 negation disjunction (p ∧ᵣ q)

theorem star_3_11 (p q : RFormula signature real order) :
    ⊢ᵣ (∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))) ⊃ᵣ (p ∧ᵣ q) := by
  exact star_2_08 negation disjunction (p ∧ᵣ q)

theorem star_3_12 (p q : RFormula signature real order) :
    ⊢ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) ∨ᵣ (p ∧ᵣ q) :=
  star_2_11 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ q))

theorem star_3_13 (p q : RFormula signature real order) :
    ⊢ᵣ (∼ᵣ (p ∧ᵣ q)) ⊃ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) :=
  detach negation disjunction _ _ (star_3_11 negation disjunction p q)
    (star_2_15 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) (p ∧ᵣ q))

theorem star_3_14 (p q : RFormula signature real order) :
    ⊢ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) ⊃ᵣ (∼ᵣ (p ∧ᵣ q)) := by
  have line1 := detach negation disjunction _ _
    (star_3_1 negation disjunction p q)
    (star_2_16 negation disjunction (p ∧ᵣ q) (∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))))
  have line2 := star_2_12 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ q))
  exact detach negation disjunction _ _ line2
    (detach negation disjunction _ _ line1
      (star_2_05 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ q))
        (∼ᵣ (∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)))) (∼ᵣ (p ∧ᵣ q))))

theorem star_3_2 (p q : RFormula signature real order) :
    ⊢ᵣ p ⊃ᵣ (q ⊃ᵣ (p ∧ᵣ q)) :=
  detach negation disjunction _ _ (star_3_12 negation disjunction p q)
    (star_2_32 negation disjunction (∼ᵣ p) (∼ᵣ q) (p ∧ᵣ q))

theorem star_3_21 (p q : RFormula signature real order) :
    ⊢ᵣ q ⊃ᵣ (p ⊃ᵣ (p ∧ᵣ q)) :=
  detach negation disjunction _ _ (star_3_2 negation disjunction p q)
    (star_2_04 negation disjunction p q (p ∧ᵣ q))

theorem star_3_22 (p q : RFormula signature real order) :
    ⊢ᵣ (p ∧ᵣ q) ⊃ᵣ (q ∧ᵣ p) := by
  have line1 := detach negation disjunction _ _
    (Derivation.star_1_4_same negation disjunction (∼ᵣ q) (∼ᵣ p))
    (detach negation disjunction _ _ (star_3_13 negation disjunction q p)
      (star_2_06 negation disjunction (∼ᵣ (q ∧ᵣ p)) ((∼ᵣ q) ∨ᵣ (∼ᵣ p))
        ((∼ᵣ p) ∨ᵣ (∼ᵣ q))))
  have line2 := detach negation disjunction _ _ line1
    (star_2_06 negation disjunction (∼ᵣ (q ∧ᵣ p)) ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) (∼ᵣ (p ∧ᵣ q)))
  have line3 := detach negation disjunction _ _
    (star_3_14 negation disjunction p q) line2
  exact detach negation disjunction _ _ line3 (star_2_17 negation disjunction (p ∧ᵣ q) (q ∧ᵣ p))

theorem star_3_24 (p : RFormula signature real order) : ⊢ᵣ ∼ᵣ (p ∧ᵣ (∼ᵣ p)) :=
  detach negation disjunction _ _ (star_2_11 negation disjunction (∼ᵣ p))
    (star_3_14 negation disjunction p (∼ᵣ p))

theorem star_3_26 (p q : RFormula signature real order) : ⊢ᵣ (p ∧ᵣ q) ⊃ᵣ p := by
  have line1 := star_2_02 negation disjunction q p
  have line2 := detach negation disjunction _ _ line1
    (star_2_31 negation disjunction (∼ᵣ p) (∼ᵣ q) p)
  exact detach negation disjunction _ _ line2
    (star_2_53 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) p)

theorem star_3_27 (p q : RFormula signature real order) : ⊢ᵣ (p ∧ᵣ q) ⊃ᵣ q :=
  detach negation disjunction _ _ (star_3_22 negation disjunction p q)
    (detach negation disjunction _ _ (star_3_26 negation disjunction q p)
      (Derivation.star_1_6_same negation disjunction (∼ᵣ (p ∧ᵣ q)) (q ∧ᵣ p) q))

/-- ✱3·03, the adjunction rule obtained from ✱3·2 by two detachments. -/
theorem star_3_03 (p q : RFormula signature real order) :
    (⊢ᵣ p) → (⊢ᵣ q) → (⊢ᵣ p ∧ᵣ q) := by
  intro hp hq
  exact detach negation disjunction _ _ hq
    (detach negation disjunction _ _ hp (star_3_2 negation disjunction p q))

theorem star_3_31 (p q r : RFormula signature real order) :
    ⊢ᵣ (p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r) := by
  have line1 : ⊢ᵣ (p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((∼ᵣ p) ∨ᵣ ((∼ᵣ q) ∨ᵣ r)) :=
    star_2_08 negation disjunction ((∼ᵣ p) ∨ᵣ ((∼ᵣ q) ∨ᵣ r))
  have line2 := detach negation disjunction _ _ line1
    (detach negation disjunction _ _ (star_2_31 negation disjunction (∼ᵣ p) (∼ᵣ q) r)
      (star_2_05 negation disjunction (p ⊃ᵣ (q ⊃ᵣ r))
        ((∼ᵣ p) ∨ᵣ ((∼ᵣ q) ∨ᵣ r)) (((∼ᵣ p) ∨ᵣ (∼ᵣ q)) ∨ᵣ r)))
  exact detach negation disjunction _ _ line2
    (detach negation disjunction _ _
      (star_2_53 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) r)
      (star_2_05 negation disjunction (p ⊃ᵣ (q ⊃ᵣ r))
        (((∼ᵣ p) ∨ᵣ (∼ᵣ q)) ∨ᵣ r) ((p ∧ᵣ q) ⊃ᵣ r)))

theorem star_3_3 (p q r : RFormula signature real order) :
    ⊢ᵣ ((p ∧ᵣ q) ⊃ᵣ r) ⊃ᵣ (p ⊃ᵣ (q ⊃ᵣ r)) := by
  have line1 := star_2_15 negation disjunction ((∼ᵣ p) ∨ᵣ (∼ᵣ q)) r
  have line2 := star_2_04 negation disjunction (∼ᵣ r) p (∼ᵣ q)
  have line3 := detach negation disjunction _ _ (star_2_17 negation disjunction q r)
    (star_2_05 negation disjunction p ((∼ᵣ r) ⊃ᵣ (∼ᵣ q)) (q ⊃ᵣ r))
  have line4 := detach negation disjunction _ _ line2
    (detach negation disjunction _ _ line1
      (star_2_06 negation disjunction ((p ∧ᵣ q) ⊃ᵣ r)
        ((∼ᵣ r) ⊃ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)))
        (p ⊃ᵣ ((∼ᵣ r) ⊃ᵣ (∼ᵣ q)))))
  exact detach negation disjunction _ _ line3
    (detach negation disjunction _ _ line4
      (star_2_06 negation disjunction ((p ∧ᵣ q) ⊃ᵣ r)
        (p ⊃ᵣ ((∼ᵣ r) ⊃ᵣ (∼ᵣ q))) (p ⊃ᵣ (q ⊃ᵣ r))))

theorem star_3_33 (p q r : RFormula signature real order) :
    ⊢ᵣ ((p ⊃ᵣ q) ∧ᵣ (q ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ r) := by
  have line1 := star_2_05 negation disjunction p q r
  have line2 := detach negation disjunction _ _ line1
    (star_2_04 negation disjunction (q ⊃ᵣ r) (p ⊃ᵣ q) (p ⊃ᵣ r))
  exact detach negation disjunction _ _ line2
    (star_3_31 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ r) (p ⊃ᵣ r))

theorem star_3_34 (p q r : RFormula signature real order) :
    ⊢ᵣ ((q ⊃ᵣ r) ∧ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ r) := by
  have line1 := star_2_06 negation disjunction p q r
  have line2 := detach negation disjunction _ _ line1
    (star_2_04 negation disjunction (p ⊃ᵣ q) (q ⊃ᵣ r) (p ⊃ᵣ r))
  exact detach negation disjunction _ _ line2
    (star_3_31 negation disjunction (q ⊃ᵣ r) (p ⊃ᵣ q) (p ⊃ᵣ r))

theorem star_3_35 (p q : RFormula signature real order) :
    ⊢ᵣ (p ∧ᵣ (p ⊃ᵣ q)) ⊃ᵣ q :=
  detach negation disjunction _ _ (star_2_27 negation disjunction p q)
    (star_3_31 negation disjunction p (p ⊃ᵣ q) q)

theorem star_3_37 (p q r : RFormula signature real order) :
    ⊢ᵣ ((p ∧ᵣ q) ⊃ᵣ r) ⊃ᵣ ((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q)) := by
  have line1 := detach negation disjunction _ _
    (detach negation disjunction _ _ (star_2_16 negation disjunction q r)
      (star_2_02 negation disjunction p ((q ⊃ᵣ r) ⊃ᵣ ((∼ᵣ r) ⊃ᵣ (∼ᵣ q)))))
    (star_2_77 negation disjunction p (q ⊃ᵣ r) ((∼ᵣ r) ⊃ᵣ (∼ᵣ q)))
  have line2 := star_3_3 negation disjunction p q r
  have line3 := star_3_31 negation disjunction p (∼ᵣ r) (∼ᵣ q)
  have composed := detach negation disjunction _ _ line2
    (detach negation disjunction _ _ line1
      (star_2_05 negation disjunction ((p ∧ᵣ q) ⊃ᵣ r) (p ⊃ᵣ (q ⊃ᵣ r))
        (p ⊃ᵣ ((∼ᵣ r) ⊃ᵣ (∼ᵣ q)))))
  exact detach negation disjunction _ _ composed
    (detach negation disjunction _ _ line3
      (star_2_05 negation disjunction ((p ∧ᵣ q) ⊃ᵣ r)
        (p ⊃ᵣ ((∼ᵣ r) ⊃ᵣ (∼ᵣ q))) ((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q))))

theorem star_3_4 (p q : RFormula signature real order) :
    ⊢ᵣ (p ∧ᵣ q) ⊃ᵣ (p ⊃ᵣ q) := by
  have line1 := star_2_51 negation disjunction p q
  have line2 := detach negation disjunction _ _ line1
    (star_2_16 negation disjunction (∼ᵣ (p ⊃ᵣ q)) (p ⊃ᵣ (∼ᵣ q)))
  exact detach negation disjunction _ _ line2
    (detach negation disjunction _ _ (star_2_14 negation disjunction (p ⊃ᵣ q))
      (star_2_05 negation disjunction (p ∧ᵣ q) (∼ᵣ (∼ᵣ (p ⊃ᵣ q))) (p ⊃ᵣ q)))

theorem star_3_41 (p q r : RFormula signature real order) :
    ⊢ᵣ (p ⊃ᵣ r) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r) :=
  detach negation disjunction _ _ (star_3_26 negation disjunction p q)
    (star_2_06 negation disjunction (p ∧ᵣ q) p r)

theorem star_3_42 (p q r : RFormula signature real order) :
    ⊢ᵣ (q ⊃ᵣ r) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r) :=
  detach negation disjunction _ _ (star_3_27 negation disjunction p q)
    (star_2_06 negation disjunction (p ∧ᵣ q) q r)

theorem star_3_43 (p q r : RFormula signature real order) :
    ⊢ᵣ ((p ⊃ᵣ q) ∧ᵣ (p ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ (q ∧ᵣ r)) := by
  have line1 := star_3_2 negation disjunction q r
  have firstSyll := detach negation disjunction _ _ line1
    (star_2_05 negation disjunction p q (r ⊃ᵣ (q ∧ᵣ r)))
  have line2 := detach negation disjunction _ _ firstSyll
    (detach negation disjunction _ _ (star_2_77 negation disjunction p r (q ∧ᵣ r))
      (star_2_05 negation disjunction (p ⊃ᵣ q) (p ⊃ᵣ (r ⊃ᵣ (q ∧ᵣ r)))
        ((p ⊃ᵣ r) ⊃ᵣ (p ⊃ᵣ (q ∧ᵣ r)))))
  exact detach negation disjunction _ _ line2
    (star_3_31 negation disjunction (p ⊃ᵣ q) (p ⊃ᵣ r) (p ⊃ᵣ (q ∧ᵣ r)))

theorem star_3_45 (p q r : RFormula signature real order) :
    ⊢ᵣ (p ⊃ᵣ q) ⊃ᵣ ((p ∧ᵣ r) ⊃ᵣ (q ∧ᵣ r)) := by
  have line1 := star_3_33 negation disjunction p q (∼ᵣ r)
  have line2 := detach negation disjunction _ _ line1
    (star_3_3 negation disjunction (p ⊃ᵣ q)
      (q ⊃ᵣ (∼ᵣ r)) (p ⊃ᵣ (∼ᵣ r)))
  have transp := star_2_16 negation disjunction (q ⊃ᵣ (∼ᵣ r)) (p ⊃ᵣ (∼ᵣ r))
  have lifted := detach negation disjunction _ _ transp
    (star_2_02 negation disjunction (p ⊃ᵣ q)
      (((q ⊃ᵣ (∼ᵣ r)) ⊃ᵣ (p ⊃ᵣ (∼ᵣ r))) ⊃ᵣ
        ((∼ᵣ (p ⊃ᵣ (∼ᵣ r))) ⊃ᵣ (∼ᵣ (q ⊃ᵣ (∼ᵣ r))))))
  have line3 := detach negation disjunction _ _ line2
    (detach negation disjunction _ _ lifted
      (star_2_77 negation disjunction (p ⊃ᵣ q)
        ((q ⊃ᵣ (∼ᵣ r)) ⊃ᵣ (p ⊃ᵣ (∼ᵣ r)))
        ((∼ᵣ (p ⊃ᵣ (∼ᵣ r))) ⊃ᵣ (∼ᵣ (q ⊃ᵣ (∼ᵣ r))))))
  exact line3

theorem star_3_44 (p q r : RFormula signature real order) :
    ⊢ᵣ ((q ⊃ᵣ p) ∧ᵣ (r ⊃ᵣ p)) ⊃ᵣ ((q ∨ᵣ r) ⊃ᵣ p) := by
  have syll : ∀ A B C : RFormula signature real order,
      (⊢ᵣ A ⊃ᵣ B) → (⊢ᵣ B ⊃ᵣ C) → (⊢ᵣ A ⊃ᵣ C) := by
    intro A B C hAB hBC
    exact detach negation disjunction _ _ hAB
      (detach negation disjunction _ _ hBC (star_2_05 negation disjunction A B C))
  have printedSyll := star_3_33 negation disjunction (∼ᵣ q) r p
  have line1 := syll _ _ _ printedSyll (star_2_6 negation disjunction q p)
  have exported := detach negation disjunction _ _ line1
    (star_3_3 negation disjunction ((∼ᵣ q) ⊃ᵣ r)
      (r ⊃ᵣ p) ((q ⊃ᵣ p) ⊃ᵣ p))
  have commInner := syll _ _ _ exported
    (star_2_04 negation disjunction (r ⊃ᵣ p) (q ⊃ᵣ p) p)
  have commOuter := detach negation disjunction _ _ commInner
    (star_2_04 negation disjunction ((∼ᵣ q) ⊃ᵣ r) (q ⊃ᵣ p) ((r ⊃ᵣ p) ⊃ᵣ p))
  have commInner2 := syll _ _ _ commOuter
    (star_2_04 negation disjunction ((∼ᵣ q) ⊃ᵣ r) (r ⊃ᵣ p) p)
  have line2 := detach negation disjunction _ _ commInner2
    (star_3_31 negation disjunction (q ⊃ᵣ p) (r ⊃ᵣ p)
      (((∼ᵣ q) ⊃ᵣ r) ⊃ᵣ p))
  have transfer := detach negation disjunction _ _ (star_2_53 negation disjunction q r)
    (detach negation disjunction _ _
      (star_3_33 negation disjunction (q ∨ᵣ r) ((∼ᵣ q) ⊃ᵣ r) p)
      (star_3_3 negation disjunction
        ((q ∨ᵣ r) ⊃ᵣ ((∼ᵣ q) ⊃ᵣ r))
        (((∼ᵣ q) ⊃ᵣ r) ⊃ᵣ p) ((q ∨ᵣ r) ⊃ᵣ p)))
  exact syll _ _ _ line2 transfer

theorem star_3_47 (p q r s : RFormula signature real order) :
    ⊢ᵣ ((p ⊃ᵣ r) ∧ᵣ (q ⊃ᵣ s)) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ (r ∧ᵣ s)) := by
  let H := (p ⊃ᵣ r) ∧ᵣ (q ⊃ᵣ s)
  have syll : ∀ A B C : RFormula signature real order,
      (⊢ᵣ A ⊃ᵣ B) → (⊢ᵣ B ⊃ᵣ C) → (⊢ᵣ A ⊃ᵣ C) := by
    intro A B C hAB hBC
    exact detach negation disjunction _ _ hAB
      (detach negation disjunction _ _ hBC (star_2_05 negation disjunction A B C))
  have first := star_3_26 negation disjunction (p ⊃ᵣ r) (q ⊃ᵣ s)
  have firstFact := syll _ _ _ first (star_3_45 negation disjunction p r q)
  have perm1 : ⊢ᵣ H ⊃ᵣ ((r ∧ᵣ q) ⊃ᵣ (q ∧ᵣ r)) :=
    detach negation disjunction _ _ (star_3_22 negation disjunction r q)
      (star_2_02 negation disjunction H ((r ∧ᵣ q) ⊃ᵣ (q ∧ᵣ r)))
  have line1 := detach negation disjunction _ _ perm1
    (detach negation disjunction _ _ firstFact
      (star_2_83 negation disjunction H (p ∧ᵣ q) (r ∧ᵣ q) (q ∧ᵣ r)))
  have second := star_3_27 negation disjunction (p ⊃ᵣ r) (q ⊃ᵣ s)
  have secondFact := syll _ _ _ second (star_3_45 negation disjunction q s r)
  have perm2 : ⊢ᵣ H ⊃ᵣ ((s ∧ᵣ r) ⊃ᵣ (r ∧ᵣ s)) :=
    detach negation disjunction _ _ (star_3_22 negation disjunction s r)
      (star_2_02 negation disjunction H ((s ∧ᵣ r) ⊃ᵣ (r ∧ᵣ s)))
  have line2 := detach negation disjunction _ _ perm2
    (detach negation disjunction _ _ secondFact
      (star_2_83 negation disjunction H (q ∧ᵣ r) (s ∧ᵣ r) (r ∧ᵣ s)))
  exact detach negation disjunction _ _ line2
    (detach negation disjunction _ _ line1
      (star_2_83 negation disjunction H (p ∧ᵣ q) (q ∧ᵣ r) (r ∧ᵣ s)))

theorem star_3_48 (p q r s : RFormula signature real order) :
    ⊢ᵣ ((p ⊃ᵣ r) ∧ᵣ (q ⊃ᵣ s)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ s)) := by
  let H := (p ⊃ᵣ r) ∧ᵣ (q ⊃ᵣ s)
  have syll : ∀ A B C : RFormula signature real order,
      (⊢ᵣ A ⊃ᵣ B) → (⊢ᵣ B ⊃ᵣ C) → (⊢ᵣ A ⊃ᵣ C) := by
    intro A B C hAB hBC
    exact detach negation disjunction _ _ hAB
      (detach negation disjunction _ _ hBC (star_2_05 negation disjunction A B C))
  have second := star_3_27 negation disjunction (p ⊃ᵣ r) (q ⊃ᵣ s)
  have propagation1 := Derivation.star_1_6_same negation disjunction p q s
  have secondSum := syll _ _ _ second propagation1
  have permute1 := detach negation disjunction _ _
    (Derivation.star_1_4_same negation disjunction p s)
    (star_2_05 negation disjunction (p ∨ᵣ q) (p ∨ᵣ s) (s ∨ᵣ p))
  have line1 := syll _ _ _ secondSum permute1
  have first := star_3_26 negation disjunction (p ⊃ᵣ r) (q ⊃ᵣ s)
  have propagation2 := Derivation.star_1_6_same negation disjunction s p r
  have firstSum := syll _ _ _ first propagation2
  have permute2 := detach negation disjunction _ _
    (Derivation.star_1_4_same negation disjunction s r)
    (star_2_05 negation disjunction (s ∨ᵣ p) (s ∨ᵣ r) (r ∨ᵣ s))
  have line2 := syll _ _ _ firstSum permute2
  exact detach negation disjunction _ _ line2
    (detach negation disjunction _ _ line1
      (star_2_83 negation disjunction H (p ∨ᵣ q) (s ∨ᵣ p) (r ∨ᵣ s)))

/- Catalogue readings.  The point syntax is retained verbatim in `printed`;
`parsed` is the exact AST occurring in the corresponding theorem above. -/
def star_3_03_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "Given ⊢ . φp and ⊢ . ψp, we have ⊢ . φp . ψp"
  parsed := .assertion (p ∧ᵣ q)
def star_3_1_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . q . ⊃ . ∼(∼p ∨ ∼q)"; parsed := .assertion ((p ∧ᵣ q) ⊃ᵣ (∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))))
def star_3_11_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : ∼(∼p ∨ ∼q) . ⊃ . p . q"; parsed := .assertion ((∼ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q))) ⊃ᵣ (p ∧ᵣ q))
def star_3_12_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : ∼p . ∨ . ∼q . ∨ . p . q"; parsed := .assertion (((∼ᵣ p) ∨ᵣ (∼ᵣ q)) ∨ᵣ (p ∧ᵣ q))
def star_3_13_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : ∼(p . q) . ⊃ . ∼p ∨ ∼q"; parsed := .assertion ((∼ᵣ (p ∧ᵣ q)) ⊃ᵣ ((∼ᵣ p) ∨ᵣ (∼ᵣ q)))
def star_3_14_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : ∼p ∨ ∼q . ⊃ . ∼(p . q)"; parsed := .assertion (((∼ᵣ p) ∨ᵣ (∼ᵣ q)) ⊃ᵣ (∼ᵣ (p ∧ᵣ q)))
def star_3_2_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . ⊃ : q . ⊃ . p . q"; parsed := .assertion (p ⊃ᵣ (q ⊃ᵣ (p ∧ᵣ q)))
def star_3_21_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : q . ⊃ : p . ⊃ . p . q"; parsed := .assertion (q ⊃ᵣ (p ⊃ᵣ (p ∧ᵣ q)))
def star_3_22_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . q . ⊃ . q . p"; parsed := .assertion ((p ∧ᵣ q) ⊃ᵣ (q ∧ᵣ p))
def star_3_24_reading (p : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ . ∼(p . ∼p)"; parsed := .assertion (∼ᵣ (p ∧ᵣ (∼ᵣ p)))
def star_3_26_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . q . ⊃ . p"; parsed := .assertion ((p ∧ᵣ q) ⊃ᵣ p)
def star_3_27_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . q . ⊃ . q"; parsed := .assertion ((p ∧ᵣ q) ⊃ᵣ q)
def star_3_3_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . q . ⊃ . r : ⊃ : p . ⊃ . q ⊃ r"; parsed := .assertion (((p ∧ᵣ q) ⊃ᵣ r) ⊃ᵣ (p ⊃ᵣ (q ⊃ᵣ r)))
def star_3_31_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . ⊃ . q ⊃ r : ⊃ : p . q . ⊃ . r"; parsed := .assertion ((p ⊃ᵣ (q ⊃ᵣ r)) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r))
def star_3_33_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p ⊃ q . q ⊃ r . ⊃ . p ⊃ r"; parsed := .assertion (((p ⊃ᵣ q) ∧ᵣ (q ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ r))
def star_3_34_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : q ⊃ r . p ⊃ q . ⊃ . p ⊃ r"; parsed := .assertion (((q ⊃ᵣ r) ∧ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ r))
def star_3_35_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . p ⊃ q . ⊃ . q"; parsed := .assertion ((p ∧ᵣ (p ⊃ᵣ q)) ⊃ᵣ q)
def star_3_37_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . q . ⊃ . r : ⊃ : p . ∼r . ⊃ . ∼q"; parsed := .assertion (((p ∧ᵣ q) ⊃ᵣ r) ⊃ᵣ ((p ∧ᵣ (∼ᵣ r)) ⊃ᵣ (∼ᵣ q)))
def star_3_4_reading (p q : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p . q . ⊃ . p ⊃ q"; parsed := .assertion ((p ∧ᵣ q) ⊃ᵣ (p ⊃ᵣ q))
def star_3_41_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p ⊃ r . ⊃ : p . q . ⊃ . r"; parsed := .assertion ((p ⊃ᵣ r) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r))
def star_3_42_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : q ⊃ r . ⊃ : p . q . ⊃ . r"; parsed := .assertion ((q ⊃ᵣ r) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ r))
def star_3_43_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p ⊃ q . p ⊃ r . ⊃ : p . ⊃ . q . r"; parsed := .assertion (((p ⊃ᵣ q) ∧ᵣ (p ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ (q ∧ᵣ r)))
def star_3_44_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : q ⊃ p . r ⊃ p . ⊃ : q ∨ r . ⊃ . p"; parsed := .assertion (((q ⊃ᵣ p) ∧ᵣ (r ⊃ᵣ p)) ⊃ᵣ ((q ∨ᵣ r) ⊃ᵣ p))
def star_3_45_reading (p q r : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p ⊃ q . ⊃ : p . r . ⊃ . q . r"; parsed := .assertion ((p ⊃ᵣ q) ⊃ᵣ ((p ∧ᵣ r) ⊃ᵣ (q ∧ᵣ r)))
def star_3_47_reading (p q r s : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p ⊃ r . q ⊃ s . ⊃ : p . q . ⊃ . r . s"; parsed := .assertion (((p ⊃ᵣ r) ∧ᵣ (q ⊃ᵣ s)) ⊃ᵣ ((p ∧ᵣ q) ⊃ᵣ (r ∧ᵣ s)))
def star_3_48_reading (p q r s : RFormula signature real order) : ClaimReading signature real where
  printed := "⊢ : p ⊃ r . q ⊃ s . ⊃ : p ∨ q . ⊃ . r ∨ s"; parsed := .assertion (((p ⊃ᵣ r) ∧ᵣ (q ⊃ᵣ s)) ⊃ᵣ ((p ∨ᵣ q) ⊃ᵣ (r ∨ᵣ s)))

#print axioms star_3_03
#print axioms star_3_01
#print axioms star_3_02
#print axioms star_3_1
#print axioms star_3_11
#print axioms star_3_12
#print axioms star_3_13
#print axioms star_3_14
#print axioms star_3_2
#print axioms star_3_21
#print axioms star_3_22
#print axioms star_3_24
#print axioms star_3_26
#print axioms star_3_27
#print axioms star_3_3
#print axioms star_3_31
#print axioms star_3_33
#print axioms star_3_34
#print axioms star_3_35
#print axioms star_3_37
#print axioms star_3_4
#print axioms star_3_41
#print axioms star_3_42
#print axioms star_3_43
#print axioms star_3_44
#print axioms star_3_45
#print axioms star_3_47
#print axioms star_3_48

end

end PM.RamifiedSyntax
