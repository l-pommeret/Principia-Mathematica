import Principia.Syntax.Ramified
import Principia.Deduction.System

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

/-- The five implication readings occurring in ✱2·05.  The component
implications and the two implications joining them may independently use
✱1·01 or any of the scope definitions ✱9·01--·08. -/
class Star2_05Reading
    {vocabularyOrder pOrder qOrder rOrder : Nat}
    {formulaOrder : outParam Nat}
    (negation : signature.Negation vocabularyOrder)
    (disjunction : signature.Disjunction vocabularyOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    (formula : outParam (Formula signature real [] formulaOrder)) where
  pNegated : Formula signature real [] pOrder
  pNegation : signature.Negation pOrder
  pNegationDefinition :
    ImplicationNegation signature real pNegation p pNegated
  primitiveQNegation : signature.Negation qOrder
  primitiveQRDisjunction : signature.Disjunction (max qOrder rOrder)
  primitiveOuterNegation : signature.Negation (max qOrder rOrder)
  primitiveConsequenceNegation : signature.Negation (max pOrder qOrder)
  primitivePQDisjunction : signature.Disjunction (max pOrder qOrder)
  primitivePRDisjunction : signature.Disjunction (max pOrder rOrder)
  primitiveConsequenceDisjunction : signature.Disjunction
    (max (max pOrder qOrder) (max pOrder rOrder))
  primitiveOuterDisjunction : signature.Disjunction
    (max (max qOrder rOrder)
      (max (max pOrder qOrder) (max pOrder rOrder)))
  sumReading : Star1_6Reading primitiveQNegation primitiveQRDisjunction
    primitiveOuterNegation primitiveConsequenceNegation
    primitivePQDisjunction primitivePRDisjunction
    primitiveConsequenceDisjunction primitiveOuterDisjunction
    pNegated q r formula

/-- The former mono-order statement is inferred as the elementary reading. -/
instance star2_05SameReading
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Star2_05Reading negation disjunction p q r
      (implication negation disjunction
        (implication negation disjunction q r)
        (implication negation disjunction
          (implication negation disjunction p q)
          (implication negation disjunction p r))) := by
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
      disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation (natMaxSelf order).symm) negation
  let consequenceEquality := natMaxCongr (natMaxSelf order) (natMaxSelf order)
  let consequenceDisjunction :=
    Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      disjunction
  let resultEquality := natMaxCongr (natMaxSelf order) consequenceEquality
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEquality.symm) disjunction
  refine {
    pNegated := .neg negation p
    pNegation := negation
    pNegationDefinition := .star_1_01 negation p
    primitiveQNegation := negation
    primitiveQRDisjunction := pairDisjunction
    primitiveOuterNegation := pairNegation
    primitiveConsequenceNegation := pairNegation
    primitivePQDisjunction := pairDisjunction
    primitivePRDisjunction := pairDisjunction
    primitiveConsequenceDisjunction := consequenceDisjunction
    primitiveOuterDisjunction := outerDisjunction
    sumReading := ?_
  }
  exact {
    qrFormulaOrder := order
    pqFormulaOrder := order
    prFormulaOrder := order
    consequenceFormulaOrder := order
    qNegated := .neg negation q
    qrFormula := implication negation disjunction q r
    pqFormula := implication negation disjunction p q
    prFormula := implication negation disjunction p r
    consequenceNegated := .neg negation
      (implication negation disjunction p q)
    consequenceFormula := implication negation disjunction
      (implication negation disjunction p q)
      (implication negation disjunction p r)
    qrNegated := .neg negation (implication negation disjunction q r)
    consequenceNegation := negation
    outerNegation := negation
    qNegationDefinition := .star_1_01 negation q
    qrDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation q) r
    pqDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation p) q
    prDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation p) r
    consequenceNegationDefinition := .star_1_01 negation
      (implication negation disjunction p q)
    consequenceDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation (implication negation disjunction p q))
      (implication negation disjunction p r)
    outerNegationDefinition := .star_1_01 negation
      (implication negation disjunction q r)
    outerDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation (implication negation disjunction q r))
      (implication negation disjunction
        (implication negation disjunction p q)
        (implication negation disjunction p r))
  }

/-- Assemble the ✱2·05 certificate when its three component implications
have one assigned order but independently chosen constructor trees.  The two
outer implications retain the elementary ✱1·01 reading, exactly as in PM's
printed Sum instance. -/
@[reducible] def star2_05ReadingOfSameOrderComponents
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r pNegated qNegated pqFormula qrFormula prFormula :
      Formula signature real [] order)
    (pNegationDefinition :
      ImplicationNegation signature real negation p pNegated)
    (qNegationDefinition :
      ImplicationNegation signature real negation q qNegated)
    (pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula)
    (qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula)
    (prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula) :
    Star2_05Reading negation disjunction p q r
      (implication negation disjunction qrFormula
        (implication negation disjunction pqFormula prFormula)) := by
  let pairDisjunction :=
    Eq.mp (congrArg signature.Disjunction (natMaxSelf order).symm)
      disjunction
  let pairNegation :=
    Eq.mp (congrArg signature.Negation (natMaxSelf order).symm) negation
  let consequenceEquality := natMaxCongr (natMaxSelf order) (natMaxSelf order)
  let consequenceDisjunction :=
    Eq.mp (congrArg signature.Disjunction consequenceEquality.symm)
      disjunction
  let resultEquality := natMaxCongr (natMaxSelf order) consequenceEquality
  let outerDisjunction :=
    Eq.mp (congrArg signature.Disjunction resultEquality.symm) disjunction
  refine {
    pNegated := pNegated
    pNegation := negation
    pNegationDefinition := pNegationDefinition
    primitiveQNegation := negation
    primitiveQRDisjunction := pairDisjunction
    primitiveOuterNegation := pairNegation
    primitiveConsequenceNegation := pairNegation
    primitivePQDisjunction := pairDisjunction
    primitivePRDisjunction := pairDisjunction
    primitiveConsequenceDisjunction := consequenceDisjunction
    primitiveOuterDisjunction := outerDisjunction
    sumReading := ?_
  }
  exact {
    qrFormulaOrder := order
    pqFormulaOrder := order
    prFormulaOrder := order
    consequenceFormulaOrder := order
    qNegated := qNegated
    qrFormula := qrFormula
    pqFormula := pqFormula
    prFormula := prFormula
    consequenceNegated := .neg negation pqFormula
    consequenceFormula := implication negation disjunction pqFormula prFormula
    qrNegated := .neg negation qrFormula
    consequenceNegation := negation
    outerNegation := negation
    qNegationDefinition := qNegationDefinition
    qrDisjunctionDefinition := qrDisjunctionDefinition
    pqDisjunctionDefinition := pqDisjunctionDefinition
    prDisjunctionDefinition := prDisjunctionDefinition
    consequenceNegationDefinition := .star_1_01 negation pqFormula
    consequenceDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation pqFormula) prFormula
    outerNegationDefinition := .star_1_01 negation qrFormula
    outerDisjunctionDefinition := .star_1_01_same disjunction
      (.neg negation qrFormula)
      (implication negation disjunction pqFormula prFormula)
  }

/-- ✱2·05, exactly the printed Sum instance, with every printed implication
carried by its syntax certificate. -/
theorem star_2_05
    {pOrder qOrder rOrder formulaOrder : Nat}
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder)
    {formula : Formula signature real [] formulaOrder}
    [reading : Star2_05Reading negation disjunction p q r formula] :
    ⊢ᵣ formula := by
  exact Derivation.star_1_6 reading.primitiveQNegation
    reading.primitiveQRDisjunction reading.primitiveOuterNegation
    reading.primitiveConsequenceNegation reading.primitivePQDisjunction
    reading.primitivePRDisjunction reading.primitiveConsequenceDisjunction
    reading.primitiveOuterDisjunction reading.pNegated q r
    (reading := reading.sumReading)

/-- Control for the generalized statement: `q ⊃ r` and `p ⊃ r` use the
✱9·04 scope definition and therefore have `Formula.always` at the root. -/
example {signature : Signature} {real : Context}
    (universal : signature.Universal .individual 1)
    (negation : signature.Negation 1)
    (disjunction : signature.Disjunction 1)
    (p q : Formula signature real [] 1)
    (body : Formula signature real [.individual] 1)
    (hQR : ⊢ᵣ star_9_04 universal disjunction (.neg negation q) body)
    (hPQ : ⊢ᵣ implication negation disjunction p q) :
    ⊢ᵣ star_9_04 universal disjunction (.neg negation p) body := by
  let r : Formula signature real [] 1 := .always universal body
  let pNegated : Formula signature real [] 1 := .neg negation p
  let qNegated : Formula signature real [] 1 := .neg negation q
  let pqFormula : Formula signature real [] 1 :=
    implication negation disjunction p q
  let qrFormula : Formula signature real [] 1 :=
    star_9_04 universal disjunction qNegated body
  let prFormula : Formula signature real [] 1 :=
    star_9_04 universal disjunction pNegated body
  have pNegationDefinition :
      ImplicationNegation signature real negation p pNegated :=
    ImplicationNegation.star_1_01 negation p
  have qNegationDefinition :
      ImplicationNegation signature real negation q qNegated :=
    ImplicationNegation.star_1_01 negation q
  have pqDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated q pqFormula :=
    ImplicationDisjunction.star_1_01_same disjunction pNegated q
  have qrDisjunctionDefinition :
      ImplicationDisjunction signature real qNegated r qrFormula := by
    apply ImplicationDisjunction.star_9_04 universal universal
    exact ImplicationDisjunction.star_1_01_same disjunction
      (qNegated.rename (fun v => .succ v)) body
  have prDisjunctionDefinition :
      ImplicationDisjunction signature real pNegated r prFormula := by
    apply ImplicationDisjunction.star_9_04 universal universal
    exact ImplicationDisjunction.star_1_01_same disjunction
      (pNegated.rename (fun v => .succ v)) body
  let syllReading := star2_05ReadingOfSameOrderComponents
    negation disjunction p q r pNegated qNegated pqFormula qrFormula prFormula
    pNegationDefinition qNegationDefinition pqDisjunctionDefinition
    qrDisjunctionDefinition prDisjunctionDefinition
  have syll := star_2_05 negation disjunction p q r
    (reading := syllReading)
  have line1 := detach negation disjunction hQR syll
  exact Derivation.star_9_12_same negation disjunction hPQ line1

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


/-- ✱2·33 (Df): the unbracketed disjunction abbreviates the
left-associated form. -/
def star_2_33 (p q r : Formula signature real [] order) :
    Formula signature real [] order :=
  (p ∨ᵣ q) ∨ᵣ r

theorem star_2_33_unfold (p q r : Formula signature real [] order) :
    star_2_33 disjunction p q r = ((p ∨ᵣ q) ∨ᵣ r) := rfl


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

/-! ## Independent-order propositional transport

The support records which schematic members occur in a formula.  Its order is
the maximum of exactly those member orders.  The normalization equality at
each disjunction is explicit: no formula is cast between unrelated orders.
-/

namespace MixedOrder


structure NegationVocabulary (signature : Signature) (support : Type) where
  order : support → Nat
  meaning : ∀ item, signature.Negation (order item)

structure DisjunctionVocabulary (signature : Signature) (support : Type)
    (combine : support → support → support)
    (negation : NegationVocabulary signature support) where
  orderEquality : ∀ left right,
    max (negation.order left) (negation.order right) =
      negation.order (combine left right)
  meaning : ∀ left right,
    signature.Disjunction (negation.order (combine left right))

def normalizedDisjunction
    (equality : max leftOrder rightOrder = resultOrder)
    (disjunction : signature.Disjunction resultOrder)
    (left : Formula signature real [] leftOrder)
    (right : Formula signature real [] rightOrder) :
    Formula signature real [] resultOrder :=
  Eq.mp (congrArg (Formula signature real []) equality)
    (.disj
      (Eq.mp (congrArg signature.Disjunction equality.symm) disjunction)
      left right)

theorem derive_star_1_2
    (selfEquality : max order order = order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p : Formula signature real [] order) :
    ⊢ᵣ normalizedDisjunction selfEquality disjunction
      (.neg negation (normalizedDisjunction selfEquality disjunction p p)) p := by
  exact Derivation.castAssertion (by rfl)
    (Derivation.star_1_2 negation disjunction p)

theorem derive_star_1_3
    (innerEquality : max pOrder qOrder = innerOrder)
    (outerEquality : max qOrder innerOrder = outerOrder)
    (qNegation : signature.Negation qOrder)
    (innerDisjunction : signature.Disjunction innerOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg qNegation q)
      (normalizedDisjunction innerEquality innerDisjunction p q) := by
  cases innerEquality
  cases outerEquality
  exact Derivation.star_1_3 qNegation innerDisjunction outerDisjunction p q

theorem derive_star_1_4
    (leftEquality : max pOrder qOrder = leftOrder)
    (rightEquality : max qOrder pOrder = rightOrder)
    (outerEquality : max leftOrder rightOrder = outerOrder)
    (leftNegation : signature.Negation leftOrder)
    (leftDisjunction : signature.Disjunction leftOrder)
    (rightDisjunction : signature.Disjunction rightOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg leftNegation
        (normalizedDisjunction leftEquality leftDisjunction p q))
      (normalizedDisjunction rightEquality rightDisjunction q p) := by
  cases leftEquality
  cases rightEquality
  cases outerEquality
  exact Derivation.star_1_4 leftNegation leftDisjunction rightDisjunction
    outerDisjunction p q

theorem derive_star_1_5
    (qrEquality : max qOrder rOrder = qrOrder)
    (leftEquality : max pOrder qrOrder = leftOrder)
    (prEquality : max pOrder rOrder = prOrder)
    (rightEquality : max qOrder prOrder = rightOrder)
    (outerEquality : max leftOrder rightOrder = outerOrder)
    (leftNegation : signature.Negation leftOrder)
    (qrDisjunction : signature.Disjunction qrOrder)
    (leftDisjunction : signature.Disjunction leftOrder)
    (prDisjunction : signature.Disjunction prOrder)
    (rightDisjunction : signature.Disjunction rightOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg leftNegation
        (normalizedDisjunction leftEquality leftDisjunction p
          (normalizedDisjunction qrEquality qrDisjunction q r)))
      (normalizedDisjunction rightEquality rightDisjunction q
        (normalizedDisjunction prEquality prDisjunction p r)) := by
  cases qrEquality
  cases leftEquality
  cases prEquality
  cases rightEquality
  cases outerEquality
  exact Derivation.star_1_5 leftNegation qrDisjunction leftDisjunction
    prDisjunction rightDisjunction outerDisjunction p q r

theorem derive_star_1_6
    (qrEquality : max qOrder rOrder = qrOrder)
    (pqEquality : max pOrder qOrder = pqOrder)
    (prEquality : max pOrder rOrder = prOrder)
    (consequentEquality : max pqOrder prOrder = consequentOrder)
    (outerEquality : max qrOrder consequentOrder = outerOrder)
    (qNegation : signature.Negation qOrder)
    (qrDisjunction : signature.Disjunction qrOrder)
    (qrNegation : signature.Negation qrOrder)
    (pqNegation : signature.Negation pqOrder)
    (pqDisjunction : signature.Disjunction pqOrder)
    (prDisjunction : signature.Disjunction prOrder)
    (consequentDisjunction : signature.Disjunction consequentOrder)
    (outerDisjunction : signature.Disjunction outerOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (r : Formula signature real [] rOrder) :
    ⊢ᵣ normalizedDisjunction outerEquality outerDisjunction
      (.neg qrNegation
        (normalizedDisjunction qrEquality qrDisjunction
          (.neg qNegation q) r))
      (normalizedDisjunction consequentEquality consequentDisjunction
        (.neg pqNegation
          (normalizedDisjunction pqEquality pqDisjunction p q))
        (normalizedDisjunction prEquality prDisjunction p r)) := by
  cases qrEquality
  cases pqEquality
  cases prEquality
  cases consequentEquality
  cases outerEquality
  exact Derivation.star_1_6 qNegation qrDisjunction qrNegation pqNegation
    pqDisjunction prDisjunction consequentDisjunction outerDisjunction p q r

theorem detach
    (equality : max pOrder qOrder = resultOrder)
    (pNegation : signature.Negation pOrder)
    (disjunction : signature.Disjunction resultOrder)
    (p : Formula signature real [] pOrder)
    (q : Formula signature real [] qOrder)
    (line1 : ⊢ᵣ p)
    (line2 : ⊢ᵣ normalizedDisjunction equality disjunction
      (.neg pNegation p) q) : ⊢ᵣ q := by
  cases real with
  | nil =>
      cases equality
      exact Derivation.star_1_1 pNegation disjunction line1 line2
  | cons realSort real =>
      cases equality
      exact Derivation.star_1_11 pNegation disjunction line1 line2

def elementarySupport
    (combine : support → support → support)
    (constantSupport : String → support)
    (valuationSupport : PM.RealVar Γ .elementaryProposition → support) :
    PM.Elementary Γ → support
  | .constant name => constantSupport name
  | .var v => valuationSupport v
  | .neg proposition =>
      elementarySupport combine constantSupport valuationSupport proposition
  | .disj left right =>
      combine
        (elementarySupport combine constantSupport valuationSupport left)
        (elementarySupport combine constantSupport valuationSupport right)

def interpret
    (combine : support → support → support)
    (negation : NegationVocabulary signature support)
    (disjunction : DisjunctionVocabulary signature support combine negation)
    (constantSupport : String → support)
    (constantMeaning : ∀ name,
      Formula signature real [] (negation.order (constantSupport name)))
    (valuationSupport : PM.RealVar Γ .elementaryProposition → support)
    (valuation : ∀ v,
      Formula signature real [] (negation.order (valuationSupport v))) :
    (proposition : PM.Elementary Γ) →
      Formula signature real []
        (negation.order
          (elementarySupport combine constantSupport valuationSupport proposition))
  | .constant name => constantMeaning name
  | .var v => valuation v
  | .neg proposition =>
      .neg
        (negation.meaning
          (elementarySupport combine constantSupport valuationSupport proposition))
        (interpret combine negation disjunction constantSupport constantMeaning
          valuationSupport valuation proposition)
  | .disj left right =>
      normalizedDisjunction
        (disjunction.orderEquality
          (elementarySupport combine constantSupport valuationSupport left)
          (elementarySupport combine constantSupport valuationSupport right))
        (disjunction.meaning
          (elementarySupport combine constantSupport valuationSupport left)
          (elementarySupport combine constantSupport valuationSupport right))
        (interpret combine negation disjunction constantSupport constantMeaning
          valuationSupport valuation left)
        (interpret combine negation disjunction constantSupport constantMeaning
          valuationSupport valuation right)

theorem transport
    (combine : support → support → support)
    (negation : NegationVocabulary signature support)
    (disjunction : DisjunctionVocabulary signature support combine negation)
    (tautology : ∀ item
      (p : Formula signature real [] (negation.order item)),
      ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality (combine item item) item)
        (disjunction.meaning (combine item item) item)
        (.neg (negation.meaning (combine item item))
          (normalizedDisjunction (disjunction.orderEquality item item)
            (disjunction.meaning item item) p p)) p)
    (constantSupport : String → support)
    (constantMeaning : ∀ name,
      Formula signature real [] (negation.order (constantSupport name)))
    (valuationSupport : PM.RealVar Γ .elementaryProposition → support)
    (valuation : ∀ v,
      Formula signature real [] (negation.order (valuationSupport v)))
    {proposition : PM.Elementary Γ} (proof : PM.Derivation proposition) :
    ⊢ᵣ interpret combine negation disjunction constantSupport constantMeaning
      valuationSupport valuation proposition := by
  induction proof with
  | @star_1_1 p q hp hpq ihp ihpq =>
      let pSupport := elementarySupport combine constantSupport valuationSupport p
      let qSupport := elementarySupport combine constantSupport valuationSupport q
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation p
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation q
      have hp' := ihp valuationSupport valuation
      have hpq' := ihpq valuationSupport valuation
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality pSupport qSupport)
        (disjunction.meaning pSupport qSupport)
        (.neg (negation.meaning pSupport) pFormula) qFormula at hpq'
      exact detach (disjunction.orderEquality pSupport qSupport)
        (negation.meaning pSupport) (disjunction.meaning pSupport qSupport)
        pFormula qFormula hp' hpq'
  | @star_1_11 context p q _ hp hpq ihp ihpq =>
      let pSupport := elementarySupport combine constantSupport valuationSupport p
      let qSupport := elementarySupport combine constantSupport valuationSupport q
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation p
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation q
      have hp' := ihp valuationSupport valuation
      have hpq' := ihpq valuationSupport valuation
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality pSupport qSupport)
        (disjunction.meaning pSupport qSupport)
        (.neg (negation.meaning pSupport) pFormula) qFormula at hpq'
      exact detach (disjunction.orderEquality pSupport qSupport)
        (negation.meaning pSupport) (disjunction.meaning pSupport qSupport)
        pFormula qFormula hp' hpq'
  | star_1_2 proposition =>
      let item := elementarySupport combine constantSupport valuationSupport proposition
      let interpreted := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation proposition
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality (combine item item) item)
        (disjunction.meaning (combine item item) item)
        (.neg (negation.meaning (combine item item))
          (normalizedDisjunction (disjunction.orderEquality item item)
            (disjunction.meaning item item) interpreted interpreted)) interpreted
      exact tautology item interpreted
  | star_1_3 left right =>
      let leftSupport := elementarySupport combine constantSupport
        valuationSupport left
      let rightSupport := elementarySupport combine constantSupport
        valuationSupport right
      let leftFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let rightFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality rightSupport
          (combine leftSupport rightSupport))
        (disjunction.meaning rightSupport (combine leftSupport rightSupport))
        (.neg (negation.meaning rightSupport) rightFormula)
        (normalizedDisjunction
          (disjunction.orderEquality leftSupport rightSupport)
          (disjunction.meaning leftSupport rightSupport)
          leftFormula rightFormula)
      exact derive_star_1_3
        (disjunction.orderEquality leftSupport rightSupport)
        (disjunction.orderEquality rightSupport (combine leftSupport rightSupport))
        _ _ _ _ _
  | star_1_4 left right =>
      let leftSupport := elementarySupport combine constantSupport
        valuationSupport left
      let rightSupport := elementarySupport combine constantSupport
        valuationSupport right
      let leftFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let rightFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      let forwardSupport := combine leftSupport rightSupport
      let reverseSupport := combine rightSupport leftSupport
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality forwardSupport reverseSupport)
        (disjunction.meaning forwardSupport reverseSupport)
        (.neg (negation.meaning forwardSupport)
          (normalizedDisjunction
            (disjunction.orderEquality leftSupport rightSupport)
            (disjunction.meaning leftSupport rightSupport)
            leftFormula rightFormula))
        (normalizedDisjunction
          (disjunction.orderEquality rightSupport leftSupport)
          (disjunction.meaning rightSupport leftSupport)
          rightFormula leftFormula)
      exact derive_star_1_4
        (disjunction.orderEquality leftSupport rightSupport)
        (disjunction.orderEquality rightSupport leftSupport)
        (disjunction.orderEquality forwardSupport reverseSupport)
        _ _ _ _ _ _
  | star_1_5 left middle right =>
      let pSupport := elementarySupport combine constantSupport valuationSupport left
      let qSupport := elementarySupport combine constantSupport valuationSupport middle
      let rSupport := elementarySupport combine constantSupport valuationSupport right
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation middle
      let rFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      let qrSupport := combine qSupport rSupport
      let leftSideSupport := combine pSupport qrSupport
      let prSupport := combine pSupport rSupport
      let rightSideSupport := combine qSupport prSupport
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality leftSideSupport rightSideSupport)
        (disjunction.meaning leftSideSupport rightSideSupport)
        (.neg (negation.meaning leftSideSupport)
          (normalizedDisjunction
            (disjunction.orderEquality pSupport qrSupport)
            (disjunction.meaning pSupport qrSupport) pFormula
            (normalizedDisjunction
              (disjunction.orderEquality qSupport rSupport)
              (disjunction.meaning qSupport rSupport) qFormula rFormula)))
        (normalizedDisjunction
          (disjunction.orderEquality qSupport prSupport)
          (disjunction.meaning qSupport prSupport) qFormula
          (normalizedDisjunction
            (disjunction.orderEquality pSupport rSupport)
            (disjunction.meaning pSupport rSupport) pFormula rFormula))
      exact derive_star_1_5
        (disjunction.orderEquality qSupport rSupport)
        (disjunction.orderEquality pSupport qrSupport)
        (disjunction.orderEquality pSupport rSupport)
        (disjunction.orderEquality qSupport prSupport)
        (disjunction.orderEquality leftSideSupport rightSideSupport)
        _ _ _ _ _ _ _ _ _
  | star_1_6 left middle right =>
      let pSupport := elementarySupport combine constantSupport valuationSupport left
      let qSupport := elementarySupport combine constantSupport valuationSupport middle
      let rSupport := elementarySupport combine constantSupport valuationSupport right
      let pFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation left
      let qFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation middle
      let rFormula := interpret combine negation disjunction constantSupport
        constantMeaning valuationSupport valuation right
      let qrSupport := combine qSupport rSupport
      let pqSupport := combine pSupport qSupport
      let prSupport := combine pSupport rSupport
      let consequentSupport := combine pqSupport prSupport
      change ⊢ᵣ normalizedDisjunction
        (disjunction.orderEquality qrSupport consequentSupport)
        (disjunction.meaning qrSupport consequentSupport)
        (.neg (negation.meaning qrSupport)
          (normalizedDisjunction
            (disjunction.orderEquality qSupport rSupport)
            (disjunction.meaning qSupport rSupport)
            (.neg (negation.meaning qSupport) qFormula) rFormula))
        (normalizedDisjunction
          (disjunction.orderEquality pqSupport prSupport)
          (disjunction.meaning pqSupport prSupport)
          (.neg (negation.meaning pqSupport)
            (normalizedDisjunction
              (disjunction.orderEquality pSupport qSupport)
              (disjunction.meaning pSupport qSupport) pFormula qFormula))
          (normalizedDisjunction
            (disjunction.orderEquality pSupport rSupport)
            (disjunction.meaning pSupport rSupport) pFormula rFormula))
      exact derive_star_1_6
        (disjunction.orderEquality qSupport rSupport)
        (disjunction.orderEquality pSupport qSupport)
        (disjunction.orderEquality pSupport rSupport)
        (disjunction.orderEquality pqSupport prSupport)
        (disjunction.orderEquality qrSupport consequentSupport)
        _ _ _ _ _ _ _ _ _ _ _

private theorem maxZeroRight : ∀ order : Nat, max order 0 = order
  | 0 => rfl
  | Nat.succ _ => rfl

private theorem succLeSucc {left right : Nat} :
    left ≤ right → left.succ ≤ right.succ :=
  fun proof => Nat.le.rec
    (motive := fun right _ => left.succ ≤ right.succ)
    Nat.le.refl (fun _ induction => Nat.le.step induction) proof

private theorem predLePred {left right : Nat} (proof : left ≤ right) :
    left.pred ≤ right.pred := by
  induction proof with
  | refl => exact Nat.le.refl
  | @step right proof induction =>
      cases right with
      | zero => exact induction
      | succ right => exact Nat.le.step induction

private theorem leOfSuccLeSucc {left right : Nat}
    (proof : left.succ ≤ right.succ) : left ≤ right :=
  predLePred proof

private theorem maxSuccSucc (left right : Nat) :
    max left.succ right.succ = (max left right).succ := by
  unfold Max.max Nat.instMax maxOfLe
  change (if left.succ ≤ right.succ then right.succ else left.succ) =
    (if left ≤ right then right else left).succ
  by_cases ordering : left ≤ right
  · rw [if_pos ordering, if_pos (succLeSucc ordering)]
  · rw [if_neg ordering]
    have successorOrdering : ¬ left.succ ≤ right.succ :=
      fun proof => ordering (leOfSuccLeSucc proof)
    rw [if_neg successorOrdering]

theorem maxAssoc : ∀ left middle right : Nat,
    max (max left middle) right = max left (max middle right)
  | 0, middle, right => rfl
  | Nat.succ left, 0, right => rfl
  | Nat.succ left, Nat.succ middle, 0 =>
      Eq.trans (maxZeroRight (max left.succ middle.succ))
        (congrArg (max left.succ) (maxZeroRight middle.succ).symm)
  | Nat.succ left, Nat.succ middle, Nat.succ right => by
      rw [maxSuccSucc, maxSuccSucc, maxSuccSucc, maxSuccSucc]
      exact congrArg Nat.succ (maxAssoc left middle right)

theorem maxComm : ∀ left right : Nat, max left right = max right left
  | 0, 0 => rfl
  | 0, Nat.succ right => rfl
  | Nat.succ left, 0 => rfl
  | Nat.succ left, Nat.succ right => by
      rw [maxSuccSucc, maxSuccSucc]
      exact congrArg Nat.succ (maxComm left right)

theorem maxLeftAbsorb (left right : Nat) :
    max left (max left right) = max left right := by
  rw [← maxAssoc, natMaxSelf]

theorem maxRightAbsorb (left right : Nat) :
    max (max left right) right = max left right := by
  rw [maxAssoc, natMaxSelf]

theorem maxRightLeftAbsorb (left right : Nat) :
    max right (max left right) = max left right := by
  rw [maxComm right, maxRightAbsorb]

theorem maxLeftRightAbsorb (left right : Nat) :
    max (max left right) left = max left right := by
  rw [maxComm (max left right) left, maxLeftAbsorb]

inductive BinarySupport where
  | left
  | right
  | both

def BinarySupport.combine : BinarySupport → BinarySupport → BinarySupport
  | .left, .left => .left
  | .left, .right => .both
  | .left, .both => .both
  | .right, .left => .both
  | .right, .right => .right
  | .right, .both => .both
  | .both, .left => .both
  | .both, .right => .both
  | .both, .both => .both

structure BinaryNegations (signature : Signature) where
  leftOrder : Nat
  rightOrder : Nat
  left : signature.Negation leftOrder
  right : signature.Negation rightOrder
  both : signature.Negation (max leftOrder rightOrder)

structure BinaryDisjunctions (signature : Signature)
    (negation : BinaryNegations signature) where
  left : signature.Disjunction negation.leftOrder
  right : signature.Disjunction negation.rightOrder
  both : signature.Disjunction (max negation.leftOrder negation.rightOrder)

def BinaryNegations.order (negation : BinaryNegations signature) :
    BinarySupport → Nat
  | .left => negation.leftOrder
  | .right => negation.rightOrder
  | .both => max negation.leftOrder negation.rightOrder

def BinaryNegations.meaning (negation : BinaryNegations signature) :
    ∀ item, signature.Negation (negation.order item)
  | .left => negation.left
  | .right => negation.right
  | .both => negation.both

def BinaryDisjunctions.meaning
    (disjunction : BinaryDisjunctions signature negation) :
    ∀ item, signature.Disjunction (negation.order item)
  | .left => disjunction.left
  | .right => disjunction.right
  | .both => disjunction.both

theorem binaryOrderCombine
    (negation : BinaryNegations signature)
    (leftSupport rightSupport : BinarySupport) :
    max (negation.order leftSupport) (negation.order rightSupport) =
      negation.order (leftSupport.combine rightSupport) := by
  cases leftSupport <;> cases rightSupport
  · exact natMaxSelf negation.leftOrder
  · rfl
  · exact maxLeftAbsorb negation.leftOrder negation.rightOrder
  · exact maxComm negation.rightOrder negation.leftOrder
  · exact natMaxSelf negation.rightOrder
  · exact maxRightLeftAbsorb negation.leftOrder negation.rightOrder
  · exact maxLeftRightAbsorb negation.leftOrder negation.rightOrder
  · exact maxRightAbsorb negation.leftOrder negation.rightOrder
  · exact natMaxSelf (max negation.leftOrder negation.rightOrder)

def BinaryNegations.toVocabulary (negation : BinaryNegations signature) :
    NegationVocabulary signature BinarySupport where
  order := negation.order
  meaning := negation.meaning

def BinaryDisjunctions.toVocabulary
    (disjunction : BinaryDisjunctions signature negation) :
    DisjunctionVocabulary signature BinarySupport BinarySupport.combine
      negation.toVocabulary where
  orderEquality := binaryOrderCombine negation
  meaning := fun leftSupport rightSupport =>
    disjunction.meaning (leftSupport.combine rightSupport)

theorem binaryTautology
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (item : BinarySupport)
    (p : Formula signature real [] (negation.order item)) :
    ⊢ᵣ normalizedDisjunction
      (binaryOrderCombine negation (item.combine item) item)
      (disjunction.meaning ((item.combine item).combine item))
      (.neg (negation.meaning (item.combine item))
        (normalizedDisjunction (binaryOrderCombine negation item item)
          (disjunction.meaning (item.combine item)) p p)) p := by
  cases item
  · exact derive_star_1_2 (natMaxSelf negation.leftOrder)
      negation.left disjunction.left p
  · exact derive_star_1_2 (natMaxSelf negation.rightOrder)
      negation.right disjunction.right p
  · exact derive_star_1_2
      (natMaxSelf (max negation.leftOrder negation.rightOrder))
      negation.both disjunction.both p

def binaryConstantSupport (_ : String) : BinarySupport := .left

def binaryValuationSupport :
    PM.RealVar [.elementaryProposition, .elementaryProposition]
      .elementaryProposition → BinarySupport
  | .zero => .left
  | .succ .zero => .right

def binaryValuation
    (negation : BinaryNegations signature)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder) :
    ∀ v : PM.RealVar [.elementaryProposition, .elementaryProposition]
      .elementaryProposition,
      Formula signature real [] (negation.order (binaryValuationSupport v))
  | .zero => p
  | .succ .zero => q

def binaryInterpret
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    (proposition : PM.Elementary
      [.elementaryProposition, .elementaryProposition]) :
    Formula signature real []
      (negation.order (elementarySupport BinarySupport.combine
        binaryConstantSupport binaryValuationSupport proposition)) :=
  interpret BinarySupport.combine negation.toVocabulary disjunction.toVocabulary
    binaryConstantSupport (fun _ => p) binaryValuationSupport
    (binaryValuation negation p q) proposition

theorem binaryTransport
    (negation : BinaryNegations signature)
    (disjunction : BinaryDisjunctions signature negation)
    (p : Formula signature real [] negation.leftOrder)
    (q : Formula signature real [] negation.rightOrder)
    {proposition : PM.Elementary
      [.elementaryProposition, .elementaryProposition]}
    (proof : PM.Derivation proposition) :
    ⊢ᵣ binaryInterpret negation disjunction p q proposition :=
  transport BinarySupport.combine negation.toVocabulary disjunction.toVocabulary
    (binaryTautology negation disjunction) binaryConstantSupport (fun _ => p)
    binaryValuationSupport (binaryValuation negation p q) proof

def binaryP : PM.Elementary [.elementaryProposition, .elementaryProposition] :=
  .var .zero

def binaryQ : PM.Elementary [.elementaryProposition, .elementaryProposition] :=
  .var (.succ .zero)


theorem maxSwapLeft (left middle right : Nat) :
    max left (max middle right) = max middle (max left right) := by
  exact Eq.trans (maxAssoc left middle right).symm
    (Eq.trans (congrArg (fun order => max order right) (maxComm left middle))
      (maxAssoc middle left right))

theorem maxThirdPair (left middle right : Nat) :
    max right (max left middle) = max left (max middle right) := by
  exact Eq.trans (maxSwapLeft right left middle)
    (congrArg (max left) (maxComm right middle))

theorem maxPairsSameLeft (left middle right : Nat) :
    max (max left middle) (max left right) =
      max left (max middle right) := by
  rw [maxAssoc, maxSwapLeft middle left right, maxLeftAbsorb]

theorem maxPairsSharedMiddle (left middle right : Nat) :
    max (max left middle) (max middle right) =
      max left (max middle right) := by
  rw [maxAssoc, maxLeftAbsorb]

theorem maxPairsSharedRight (left middle right : Nat) :
    max (max left right) (max middle right) =
      max left (max middle right) := by
  rw [maxAssoc, maxRightLeftAbsorb]

theorem maxMiddleFull (left middle right : Nat) :
    max middle (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxSwapLeft middle left, maxLeftAbsorb]

theorem maxRightFull (left middle right : Nat) :
    max right (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxSwapLeft right left, maxSwapLeft right middle, natMaxSelf]

theorem maxPairLeftFull (left middle right : Nat) :
    max (max left middle) (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxPairsSameLeft, maxLeftAbsorb]

theorem maxPairRightFull (left middle right : Nat) :
    max (max left right) (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxPairsSameLeft, maxRightLeftAbsorb]

theorem maxPairMiddleFull (left middle right : Nat) :
    max (max middle right) (max left (max middle right)) =
      max left (max middle right) := by
  rw [maxComm (max middle right), maxRightAbsorb]

inductive TernarySupport where
  | p
  | q
  | r
  | pq
  | pr
  | qr
  | pqr

def TernarySupport.combine : TernarySupport → TernarySupport → TernarySupport
  | .p, .p => .p
  | .p, .q => .pq
  | .p, .r => .pr
  | .p, .pq => .pq
  | .p, .pr => .pr
  | .p, .qr => .pqr
  | .p, .pqr => .pqr
  | .q, .p => .pq
  | .q, .q => .q
  | .q, .r => .qr
  | .q, .pq => .pq
  | .q, .pr => .pqr
  | .q, .qr => .qr
  | .q, .pqr => .pqr
  | .r, .p => .pr
  | .r, .q => .qr
  | .r, .r => .r
  | .r, .pq => .pqr
  | .r, .pr => .pr
  | .r, .qr => .qr
  | .r, .pqr => .pqr
  | .pq, .p => .pq
  | .pq, .q => .pq
  | .pq, .r => .pqr
  | .pq, .pq => .pq
  | .pq, .pr => .pqr
  | .pq, .qr => .pqr
  | .pq, .pqr => .pqr
  | .pr, .p => .pr
  | .pr, .q => .pqr
  | .pr, .r => .pr
  | .pr, .pq => .pqr
  | .pr, .pr => .pr
  | .pr, .qr => .pqr
  | .pr, .pqr => .pqr
  | .qr, .p => .pqr
  | .qr, .q => .qr
  | .qr, .r => .qr
  | .qr, .pq => .pqr
  | .qr, .pr => .pqr
  | .qr, .qr => .qr
  | .qr, .pqr => .pqr
  | .pqr, .p => .pqr
  | .pqr, .q => .pqr
  | .pqr, .r => .pqr
  | .pqr, .pq => .pqr
  | .pqr, .pr => .pqr
  | .pqr, .qr => .pqr
  | .pqr, .pqr => .pqr

structure TernaryNegations (signature : Signature) where
  pOrder : Nat
  qOrder : Nat
  rOrder : Nat
  p : signature.Negation pOrder
  q : signature.Negation qOrder
  r : signature.Negation rOrder
  pq : signature.Negation (max pOrder qOrder)
  pr : signature.Negation (max pOrder rOrder)
  qr : signature.Negation (max qOrder rOrder)
  pqr : signature.Negation (max pOrder (max qOrder rOrder))

structure TernaryDisjunctions (signature : Signature)
    (negation : TernaryNegations signature) where
  p : signature.Disjunction negation.pOrder
  q : signature.Disjunction negation.qOrder
  r : signature.Disjunction negation.rOrder
  pq : signature.Disjunction (max negation.pOrder negation.qOrder)
  pr : signature.Disjunction (max negation.pOrder negation.rOrder)
  qr : signature.Disjunction (max negation.qOrder negation.rOrder)
  pqr : signature.Disjunction
    (max negation.pOrder (max negation.qOrder negation.rOrder))

def TernaryNegations.order (negation : TernaryNegations signature) :
    TernarySupport → Nat
  | .p => negation.pOrder
  | .q => negation.qOrder
  | .r => negation.rOrder
  | .pq => max negation.pOrder negation.qOrder
  | .pr => max negation.pOrder negation.rOrder
  | .qr => max negation.qOrder negation.rOrder
  | .pqr => max negation.pOrder (max negation.qOrder negation.rOrder)

def TernaryNegations.meaning (negation : TernaryNegations signature) :
    ∀ item, signature.Negation (negation.order item)
  | .p => negation.p
  | .q => negation.q
  | .r => negation.r
  | .pq => negation.pq
  | .pr => negation.pr
  | .qr => negation.qr
  | .pqr => negation.pqr

def TernaryDisjunctions.meaning
    (disjunction : TernaryDisjunctions signature negation) :
    ∀ item, signature.Disjunction (negation.order item)
  | .p => disjunction.p
  | .q => disjunction.q
  | .r => disjunction.r
  | .pq => disjunction.pq
  | .pr => disjunction.pr
  | .qr => disjunction.qr
  | .pqr => disjunction.pqr

theorem ternaryOrderCombine
    (negation : TernaryNegations signature) (left right : TernarySupport) :
    max (negation.order left) (negation.order right) =
      negation.order (left.combine right) := by
  cases left <;> cases right
  · exact natMaxSelf negation.pOrder
  · rfl
  · rfl
  · exact maxLeftAbsorb negation.pOrder negation.qOrder
  · exact maxLeftAbsorb negation.pOrder negation.rOrder
  · rfl
  · exact maxLeftAbsorb negation.pOrder (max negation.qOrder negation.rOrder)
  · exact maxComm negation.qOrder negation.pOrder
  · exact natMaxSelf negation.qOrder
  · rfl
  · exact maxRightLeftAbsorb negation.pOrder negation.qOrder
  · exact maxSwapLeft negation.qOrder negation.pOrder negation.rOrder
  · exact maxLeftAbsorb negation.qOrder negation.rOrder
  · exact maxMiddleFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxComm negation.rOrder negation.pOrder
  · exact maxComm negation.rOrder negation.qOrder
  · exact natMaxSelf negation.rOrder
  · exact maxThirdPair negation.pOrder negation.qOrder negation.rOrder
  · exact maxRightLeftAbsorb negation.pOrder negation.rOrder
  · exact maxRightLeftAbsorb negation.qOrder negation.rOrder
  · exact maxRightFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxLeftRightAbsorb negation.pOrder negation.qOrder
  · exact maxRightAbsorb negation.pOrder negation.qOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder negation.qOrder) negation.rOrder)
      (maxThirdPair negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf (max negation.pOrder negation.qOrder)
  · exact maxPairsSameLeft negation.pOrder negation.qOrder negation.rOrder
  · exact maxPairsSharedMiddle negation.pOrder negation.qOrder negation.rOrder
  · exact maxPairLeftFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxLeftRightAbsorb negation.pOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder negation.rOrder) negation.qOrder)
      (maxSwapLeft negation.qOrder negation.pOrder negation.rOrder)
  · exact maxRightAbsorb negation.pOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder negation.rOrder)
        (max negation.pOrder negation.qOrder))
      (maxPairsSameLeft negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf (max negation.pOrder negation.rOrder)
  · exact maxPairsSharedRight negation.pOrder negation.qOrder negation.rOrder
  · exact maxPairRightFull negation.pOrder negation.qOrder negation.rOrder
  · exact maxComm (max negation.qOrder negation.rOrder) negation.pOrder
  · exact maxLeftRightAbsorb negation.qOrder negation.rOrder
  · exact maxRightAbsorb negation.qOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.qOrder negation.rOrder)
        (max negation.pOrder negation.qOrder))
      (maxPairsSharedMiddle negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.qOrder negation.rOrder)
        (max negation.pOrder negation.rOrder))
      (maxPairsSharedRight negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf (max negation.qOrder negation.rOrder)
  · exact maxPairMiddleFull negation.pOrder negation.qOrder negation.rOrder
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        negation.pOrder)
      (maxLeftAbsorb negation.pOrder (max negation.qOrder negation.rOrder))
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        negation.qOrder)
      (maxMiddleFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        negation.rOrder)
      (maxRightFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        (max negation.pOrder negation.qOrder))
      (maxPairLeftFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        (max negation.pOrder negation.rOrder))
      (maxPairRightFull negation.pOrder negation.qOrder negation.rOrder)
  · exact Eq.trans
      (maxComm (max negation.pOrder (max negation.qOrder negation.rOrder))
        (max negation.qOrder negation.rOrder))
      (maxPairMiddleFull negation.pOrder negation.qOrder negation.rOrder)
  · exact natMaxSelf
      (max negation.pOrder (max negation.qOrder negation.rOrder))

def TernaryNegations.toVocabulary (negation : TernaryNegations signature) :
    NegationVocabulary signature TernarySupport where
  order := negation.order
  meaning := negation.meaning

def TernaryDisjunctions.toVocabulary
    (disjunction : TernaryDisjunctions signature negation) :
    DisjunctionVocabulary signature TernarySupport TernarySupport.combine
      negation.toVocabulary where
  orderEquality := ternaryOrderCombine negation
  meaning := fun left right => disjunction.meaning (left.combine right)

theorem ternaryTautology
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (item : TernarySupport)
    (formula : Formula signature real [] (negation.order item)) :
    ⊢ᵣ normalizedDisjunction
      (ternaryOrderCombine negation (item.combine item) item)
      (disjunction.meaning ((item.combine item).combine item))
      (.neg (negation.meaning (item.combine item))
        (normalizedDisjunction (ternaryOrderCombine negation item item)
          (disjunction.meaning (item.combine item)) formula formula)) formula := by
  cases item
  · exact derive_star_1_2 (natMaxSelf negation.pOrder)
      negation.p disjunction.p formula
  · exact derive_star_1_2 (natMaxSelf negation.qOrder)
      negation.q disjunction.q formula
  · exact derive_star_1_2 (natMaxSelf negation.rOrder)
      negation.r disjunction.r formula
  · exact derive_star_1_2 (natMaxSelf (max negation.pOrder negation.qOrder))
      negation.pq disjunction.pq formula
  · exact derive_star_1_2 (natMaxSelf (max negation.pOrder negation.rOrder))
      negation.pr disjunction.pr formula
  · exact derive_star_1_2 (natMaxSelf (max negation.qOrder negation.rOrder))
      negation.qr disjunction.qr formula
  · exact derive_star_1_2
      (natMaxSelf (max negation.pOrder (max negation.qOrder negation.rOrder)))
      negation.pqr disjunction.pqr formula

def ternaryConstantSupport (_ : String) : TernarySupport := .p

def ternaryValuationSupport :
    PM.RealVar [.elementaryProposition, .elementaryProposition,
      .elementaryProposition] .elementaryProposition → TernarySupport
  | .zero => .p
  | .succ .zero => .q
  | .succ (.succ .zero) => .r

def ternaryValuation
    (negation : TernaryNegations signature)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder) :
    ∀ v : PM.RealVar [.elementaryProposition, .elementaryProposition,
      .elementaryProposition] .elementaryProposition,
      Formula signature real [] (negation.order (ternaryValuationSupport v))
  | .zero => p
  | .succ .zero => q
  | .succ (.succ .zero) => r

def ternaryInterpret
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    (proposition : PM.Elementary [.elementaryProposition,
      .elementaryProposition, .elementaryProposition]) :
    Formula signature real []
      (negation.order (elementarySupport TernarySupport.combine
        ternaryConstantSupport ternaryValuationSupport proposition)) :=
  interpret TernarySupport.combine negation.toVocabulary
    disjunction.toVocabulary ternaryConstantSupport (fun _ => p)
    ternaryValuationSupport (ternaryValuation negation p q r) proposition

theorem ternaryTransport
    (negation : TernaryNegations signature)
    (disjunction : TernaryDisjunctions signature negation)
    (p : Formula signature real [] negation.pOrder)
    (q : Formula signature real [] negation.qOrder)
    (r : Formula signature real [] negation.rOrder)
    {proposition : PM.Elementary [.elementaryProposition,
      .elementaryProposition, .elementaryProposition]}
    (proof : PM.Derivation proposition) :
    ⊢ᵣ ternaryInterpret negation disjunction p q r proposition :=
  transport TernarySupport.combine negation.toVocabulary
    disjunction.toVocabulary (ternaryTautology negation disjunction)
    ternaryConstantSupport (fun _ => p) ternaryValuationSupport
    (ternaryValuation negation p q r) proof

def ternaryP : PM.Elementary [.elementaryProposition, .elementaryProposition,
    .elementaryProposition] := .var .zero

def ternaryQ : PM.Elementary [.elementaryProposition, .elementaryProposition,
    .elementaryProposition] := .var (.succ .zero)

def ternaryR : PM.Elementary [.elementaryProposition, .elementaryProposition,
    .elementaryProposition] := .var (.succ (.succ .zero))



end MixedOrder

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
#print axioms PM.RamifiedSyntax.star_2_33
#print axioms PM.RamifiedSyntax.star_2_33_unfold
