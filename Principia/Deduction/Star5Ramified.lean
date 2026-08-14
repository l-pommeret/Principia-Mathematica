import Principia.Deduction.Star4Ramified
import Principia.FirstEdition.Volume1.Part1.SectionA.Star5Q246
import Principia.FirstEdition.Volume1.Part1.SectionA.Star5Q247

namespace PM.RamifiedSyntax

abbrev RF (signature : Signature) (real : Context) (order : Nat) :=
  Formula signature real [] order

section

variable {signature : Signature} {real : Context} {order : Nat}
variable (negation : signature.Negation order)
variable (disjunction : signature.Disjunction order)

local prefix:75 "∼ᵣ " => Formula.neg negation
local infixl:65 " ∨ᵣ " => sameDisjunction disjunction
local infixr:60 " ⊃ᵣ " => implication negation disjunction
local infixl:64 " ∧ᵣ " => conjunction negation disjunction
local infix:50 " ≡ᵣ " => star_4_01 negation disjunction

@[reducible] private def interpret {Γ : PM.RealContext}
    (constant : String → RF signature real order)
    (valuation : PM.RealVar Γ .elementaryProposition → RF signature real order) :
    PM.Elementary Γ → RF signature real order
  | .constant name => constant name
  | .var v => valuation v
  | .neg p => ∼ᵣ interpret constant valuation p
  | .disj p q => interpret constant valuation p ∨ᵣ interpret constant valuation q

private theorem transport {Γ : PM.RealContext}
    (constant : String → RF signature real order)
    (valuation : PM.RealVar Γ .elementaryProposition → RF signature real order)
    {p : PM.Elementary Γ} (proof : PM.Derivation p) :
    ⊢ᵣ interpret negation disjunction constant valuation p := by
  induction proof with
  | star_1_1 hp hpq ihp ihpq =>
      cases real with
      | nil => exact Derivation.star_1_1 negation disjunction (ihp valuation) (ihpq valuation)
      | cons head tail => exact Derivation.star_1_11 negation disjunction (ihp valuation) (ihpq valuation)
  | star_1_11 _ hp hpq ihp ihpq =>
      cases real with
      | nil => exact Derivation.star_1_1 negation disjunction (ihp valuation) (ihpq valuation)
      | cons head tail => exact Derivation.star_1_11 negation disjunction (ihp valuation) (ihpq valuation)
  | star_1_2 p => exact Derivation.star_1_2 negation disjunction _
  | star_1_3 p q => exact Derivation.star_1_3 negation disjunction _ _
  | star_1_4 p q => exact Derivation.star_1_4 negation disjunction _ _
  | star_1_5 p q r => exact Derivation.star_1_5 negation disjunction _ _ _
  | star_1_6 p q r => exact Derivation.star_1_6 negation disjunction _ _ _

private def atoms (p q r s : RF signature real order) : String → RF signature real order
  | "p" => p
  | "q" => q
  | "r" => r
  | _ => s

private def noVariable : PM.RealVar [] .elementaryProposition → RF signature real order
  | v => nomatch v

private theorem lift
    (p q r s : RF signature real order) {e : PM.Elementary []}
    (proof : PM.Derivation e) :
    ⊢ᵣ interpret negation disjunction (atoms p q r s) noVariable e :=
  transport negation disjunction (atoms p q r s) noVariable proof

theorem star_5_13 (p q : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ q) ∨ᵣ (q ⊃ᵣ p) := by
  exact transport negation disjunction (atoms p q p p) noVariable
    (PM.FirstEdition.Volume1.Star5.star_5_13 (.constant "p") (.constant "q"))

theorem star_5_25 (p q : RF signature real order) :
    ⊢ᵣ (p ∨ᵣ q) ≡ᵣ ((p ⊃ᵣ q) ⊃ᵣ q) := by
  change ⊢ᵣ interpret negation disjunction (atoms p q p p) noVariable
    (((.constant "p" ∨ₚ .constant "q") ≡ₚ
      ((.constant "p" ⊃ₚ .constant "q") ⊃ₚ .constant "q")) : PM.Elementary [])
  exact lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_25 (.constant "p") (.constant "q"))

theorem star_5_1 (p q : RF signature real order) :
    ⊢ᵣ (p ∧ᵣ q) ⊃ᵣ (p ≡ᵣ q) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_1 (.constant "p") (.constant "q"))

theorem star_5_21 (p q : RF signature real order) :
    ⊢ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q)) ⊃ᵣ (p ≡ᵣ q) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_21 (.constant "p") (.constant "q"))

theorem star_5_41 (p q r : RF signature real order) :
    ⊢ᵣ ((p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ r)) ≡ᵣ (p ⊃ᵣ (q ⊃ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_41 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_4 (p q : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ (p ⊃ᵣ q)) ≡ᵣ (p ⊃ᵣ q) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_4 (.constant "p") (.constant "q"))

theorem star_5_31 (p q r : RF signature real order) :
    ⊢ᵣ (r ∧ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ (q ∧ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_31 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_35 (p q r : RF signature real order) :
    ⊢ᵣ ((p ⊃ᵣ q) ∧ᵣ (p ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ (q ≡ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_35 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_5 (p q : RF signature real order) :
    ⊢ᵣ p ⊃ᵣ ((p ⊃ᵣ q) ≡ᵣ q) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_5 (.constant "p") (.constant "q"))

theorem star_5_501 (p q : RF signature real order) :
    ⊢ᵣ p ⊃ᵣ (q ≡ᵣ (p ≡ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_501 (.constant "p") (.constant "q"))

theorem star_5_53 (p q r s : RF signature real order) :
    ⊢ᵣ (((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ s) ≡ᵣ
      (((p ⊃ᵣ s) ∧ᵣ (q ⊃ᵣ s)) ∧ᵣ (r ⊃ᵣ s)) :=
  lift negation disjunction p q r s
    (PM.FirstEdition.Volume1.Star5.star_5_53 (.constant "p") (.constant "q") (.constant "r") (.constant "s"))

theorem star_5_44 (p q r : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ q) ⊃ᵣ ((p ⊃ᵣ r) ≡ᵣ (p ⊃ᵣ (q ∧ᵣ r))) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_44 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_42 (p q r : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ (q ⊃ᵣ r)) ≡ᵣ (p ⊃ᵣ (q ⊃ᵣ (p ∧ᵣ r))) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_42 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_3 (p q r : RF signature real order) :
    ⊢ᵣ ((p ∧ᵣ q) ⊃ᵣ r) ≡ᵣ ((p ∧ᵣ q) ⊃ᵣ (p ∧ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_3 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_36 (p q : RF signature real order) :
    ⊢ᵣ (p ∧ᵣ (p ≡ᵣ q)) ≡ᵣ (q ∧ᵣ (p ≡ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_36 (.constant "p") (.constant "q"))

theorem star_5_11 (p q : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ q) ∨ᵣ ((∼ᵣ p) ⊃ᵣ q) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_11 (.constant "p") (.constant "q"))

theorem star_5_12 (p q : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ (∼ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_12 (.constant "p") (.constant "q"))

theorem star_5_14 (p q r : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ q) ∨ᵣ (q ⊃ᵣ r) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_14 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_61 (p q : RF signature real order) :
    ⊢ᵣ ((p ∨ᵣ q) ∧ᵣ (∼ᵣ q)) ≡ᵣ (p ∧ᵣ (∼ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_61 (.constant "p") (.constant "q"))

theorem star_5_71 (p q r : RF signature real order) :
    ⊢ᵣ (q ⊃ᵣ (∼ᵣ r)) ⊃ᵣ (((p ∨ᵣ q) ∧ᵣ r) ≡ᵣ (p ∧ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_71 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_55 (p q : RF signature real order) :
    ⊢ᵣ ((p ∨ᵣ q) ≡ᵣ p) ∨ᵣ ((p ∨ᵣ q) ≡ᵣ q) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_55 (.constant "p") (.constant "q"))

theorem star_5_62 (p q : RF signature real order) :
    ⊢ᵣ ((p ∧ᵣ q) ∨ᵣ (∼ᵣ q)) ≡ᵣ (p ∨ᵣ (∼ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_62 (.constant "p") (.constant "q"))

theorem star_5_63 (p q : RF signature real order) :
    ⊢ᵣ (p ∨ᵣ q) ≡ᵣ (p ∨ᵣ ((∼ᵣ p) ∧ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_63 (.constant "p") (.constant "q"))

theorem star_5_54 (p q : RF signature real order) :
    ⊢ᵣ ((p ∧ᵣ q) ≡ᵣ p) ∨ᵣ ((p ∧ᵣ q) ≡ᵣ q) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_54 (.constant "p") (.constant "q"))

theorem star_5_6 (p q r : RF signature real order) :
    ⊢ᵣ ((p ∧ᵣ (∼ᵣ q)) ⊃ᵣ r) ≡ᵣ (p ⊃ᵣ (q ∨ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_6 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_7 (p q r : RF signature real order) :
    ⊢ᵣ ((p ∨ᵣ r) ≡ᵣ (q ∨ᵣ r)) ≡ᵣ (r ∨ᵣ (p ≡ᵣ q)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_7 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_74 (p q r : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ (q ≡ᵣ r)) ≡ᵣ ((p ⊃ᵣ q) ≡ᵣ (p ⊃ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_74 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_75 (p q r : RF signature real order) :
    ⊢ᵣ (r ⊃ᵣ (∼ᵣ q)) ⊃ᵣ ((p ≡ᵣ (q ∨ᵣ r)) ⊃ᵣ ((p ∧ᵣ (∼ᵣ q)) ≡ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_75 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_15 (p q : RF signature real order) :
    ⊢ᵣ (p ≡ᵣ q) ∨ᵣ (p ≡ᵣ (∼ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_15 (.constant "p") (.constant "q"))

theorem star_5_16 (p q : RF signature real order) :
    ⊢ᵣ ∼ᵣ ((p ≡ᵣ q) ∧ᵣ (p ≡ᵣ (∼ᵣ q))) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_16 (.constant "p") (.constant "q"))

theorem star_5_17 (p q : RF signature real order) :
    ⊢ᵣ ((p ∨ᵣ q) ∧ᵣ (∼ᵣ (p ∧ᵣ q))) ≡ᵣ (p ≡ᵣ (∼ᵣ q)) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_17 (.constant "p") (.constant "q"))

theorem star_5_22 (p q : RF signature real order) :
    ⊢ᵣ (∼ᵣ (p ≡ᵣ q)) ≡ᵣ ((p ∧ᵣ (∼ᵣ q)) ∨ᵣ (q ∧ᵣ (∼ᵣ p))) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_22 (.constant "p") (.constant "q"))

theorem star_5_18 (p q : RF signature real order) :
    ⊢ᵣ (p ≡ᵣ q) ≡ᵣ (∼ᵣ (p ≡ᵣ (∼ᵣ q))) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_18 (.constant "p") (.constant "q"))

private theorem elementary_star_5_19 (p : PM.Elementary []) :
    PM.Derivation (PM.Elementary.neg (PM.Elementary.equiv p (PM.Elementary.neg p))) := by
  have forward := PM.Derivation.detach
    (PM.FirstEdition.Volume1.Star5.star_5_18 p p)
    (PM.FirstEdition.Volume1.Star3.star_3_26
      ((p ≡ₚ p) ⊃ₚ ∼ₚ (p ≡ₚ ∼ₚ p))
      ((∼ₚ (p ≡ₚ ∼ₚ p)) ⊃ₚ (p ≡ₚ p)))
  exact PM.Derivation.detach (PM.FirstEdition.Volume1.Star4.star_4_2 p) forward

theorem star_5_19 (p : RF signature real order) :
    ⊢ᵣ ∼ᵣ (p ≡ᵣ (∼ᵣ p)) :=
  lift negation disjunction p p p p (elementary_star_5_19 (.constant "p"))

theorem star_5_23 (p q : RF signature real order) :
    ⊢ᵣ (p ≡ᵣ q) ≡ᵣ ((p ∧ᵣ q) ∨ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q))) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_23 (.constant "p") (.constant "q"))

theorem star_5_24 (p q : RF signature real order) :
    ⊢ᵣ (∼ᵣ ((p ∧ᵣ q) ∨ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q)))) ≡ᵣ
      ((p ∧ᵣ (∼ᵣ q)) ∨ᵣ (q ∧ᵣ (∼ᵣ p))) :=
  lift negation disjunction p q p p
    (PM.FirstEdition.Volume1.Star5.star_5_24 (.constant "p") (.constant "q"))

theorem star_5_32 (p q r : RF signature real order) :
    ⊢ᵣ (p ⊃ᵣ (q ≡ᵣ r)) ≡ᵣ ((p ∧ᵣ q) ≡ᵣ (p ∧ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_32 (.constant "p") (.constant "q") (.constant "r"))

theorem star_5_33 (p q r : RF signature real order) :
    ⊢ᵣ (p ∧ᵣ (q ⊃ᵣ r)) ≡ᵣ (p ∧ᵣ ((p ∧ᵣ q) ⊃ᵣ r)) :=
  lift negation disjunction p q r p
    (PM.FirstEdition.Volume1.Star5.star_5_33 (.constant "p") (.constant "q") (.constant "r"))

private def reading (printed : String) (formula : RF signature real order) :
    ClaimReading signature real where
  printed := printed
  parsed := .assertion formula

def star_5_1_reading (p q : RF signature real order) := reading "⊢ : p . q . ⊃ . p ≡ q" ((p ∧ᵣ q) ⊃ᵣ (p ≡ᵣ q))
def star_5_11_reading (p q : RF signature real order) := reading "⊢ : p ⊃ q . ∨ . ∼p ⊃ q" ((p ⊃ᵣ q) ∨ᵣ ((∼ᵣ p) ⊃ᵣ q))
def star_5_12_reading (p q : RF signature real order) := reading "⊢ : p ⊃ q . ∨ . p ⊃ ∼q" ((p ⊃ᵣ q) ∨ᵣ (p ⊃ᵣ (∼ᵣ q)))
def star_5_13_reading (p q : RF signature real order) := reading "⊢ : p ⊃ q . ∨ . q ⊃ p" ((p ⊃ᵣ q) ∨ᵣ (q ⊃ᵣ p))
def star_5_14_reading (p q r : RF signature real order) := reading "⊢ : p ⊃ q . ∨ . q ⊃ r" ((p ⊃ᵣ q) ∨ᵣ (q ⊃ᵣ r))
def star_5_15_reading (p q : RF signature real order) := reading "⊢ : p ≡ q . ∨ . p ≡ ∼q" ((p ≡ᵣ q) ∨ᵣ (p ≡ᵣ (∼ᵣ q)))
def star_5_16_reading (p q : RF signature real order) := reading "⊢ . ∼(p ≡ q . p ≡ ∼q)" (∼ᵣ ((p ≡ᵣ q) ∧ᵣ (p ≡ᵣ (∼ᵣ q))))
def star_5_17_reading (p q : RF signature real order) := reading "⊢ : p ∨ q . ∼(p . q) . ≡ . p ≡ ∼q" (((p ∨ᵣ q) ∧ᵣ (∼ᵣ (p ∧ᵣ q))) ≡ᵣ (p ≡ᵣ (∼ᵣ q)))
def star_5_18_reading (p q : RF signature real order) := reading "⊢ : p ≡ q . ≡ . ∼(p ≡ ∼q)" ((p ≡ᵣ q) ≡ᵣ (∼ᵣ (p ≡ᵣ (∼ᵣ q))))
def star_5_19_reading (p : RF signature real order) := reading "⊢ . ∼(p ≡ ∼p)" (∼ᵣ (p ≡ᵣ (∼ᵣ p)))
def star_5_21_reading (p q : RF signature real order) := reading "⊢ : ∼p . ∼q . ⊃ . p ≡ q" (((∼ᵣ p) ∧ᵣ (∼ᵣ q)) ⊃ᵣ (p ≡ᵣ q))
def star_5_22_reading (p q : RF signature real order) := reading "⊢ : ∼(p ≡ q) . ≡ : p . ∼q . ∨ . q . ∼p" ((∼ᵣ (p ≡ᵣ q)) ≡ᵣ ((p ∧ᵣ (∼ᵣ q)) ∨ᵣ (q ∧ᵣ (∼ᵣ p))))
def star_5_23_reading (p q : RF signature real order) := reading "⊢ : p ≡ q . ≡ : p . q . ∨ . ∼p . ∼q" ((p ≡ᵣ q) ≡ᵣ ((p ∧ᵣ q) ∨ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q))))
def star_5_24_reading (p q : RF signature real order) := reading "⊢ : ∼(p . q . ∨ . ∼p . ∼q) . ≡ : p . ∼q . ∨ . q . ∼p" ((∼ᵣ ((p ∧ᵣ q) ∨ᵣ ((∼ᵣ p) ∧ᵣ (∼ᵣ q)))) ≡ᵣ ((p ∧ᵣ (∼ᵣ q)) ∨ᵣ (q ∧ᵣ (∼ᵣ p))))
def star_5_25_reading (p q : RF signature real order) := reading "⊢ : p ∨ q . ≡ : p ⊃ q . ⊃ . q" ((p ∨ᵣ q) ≡ᵣ ((p ⊃ᵣ q) ⊃ᵣ q))
def star_5_3_reading (p q r : RF signature real order) := reading "⊢ : p . q . ⊃ . r : ≡ : p . q . ⊃ . p . r" (((p ∧ᵣ q) ⊃ᵣ r) ≡ᵣ ((p ∧ᵣ q) ⊃ᵣ (p ∧ᵣ r)))
def star_5_31_reading (p q r : RF signature real order) := reading "⊢ : r . p ⊃ q . ⊃ : p . ⊃ . q . r" ((r ∧ᵣ (p ⊃ᵣ q)) ⊃ᵣ (p ⊃ᵣ (q ∧ᵣ r)))
def star_5_32_reading (p q r : RF signature real order) := reading "⊢ : p . ⊃ . q ≡ r : ≡ : p . q . ≡ . p . r" ((p ⊃ᵣ (q ≡ᵣ r)) ≡ᵣ ((p ∧ᵣ q) ≡ᵣ (p ∧ᵣ r)))
def star_5_33_reading (p q r : RF signature real order) := reading "⊢ : p . q ⊃ r . ≡ : p : p . q . ⊃ . r" ((p ∧ᵣ (q ⊃ᵣ r)) ≡ᵣ (p ∧ᵣ ((p ∧ᵣ q) ⊃ᵣ r)))
def star_5_35_reading (p q r : RF signature real order) := reading "⊢ : p ⊃ q . p ⊃ r . ⊃ : p . ⊃ . q ≡ r" (((p ⊃ᵣ q) ∧ᵣ (p ⊃ᵣ r)) ⊃ᵣ (p ⊃ᵣ (q ≡ᵣ r)))
def star_5_36_reading (p q : RF signature real order) := reading "⊢ : p . p ≡ q . ≡ . q . p ≡ q" ((p ∧ᵣ (p ≡ᵣ q)) ≡ᵣ (q ∧ᵣ (p ≡ᵣ q)))
def star_5_4_reading (p q : RF signature real order) := reading "⊢ : p . ⊃ . p ⊃ q : ≡ . p ⊃ q" ((p ⊃ᵣ (p ⊃ᵣ q)) ≡ᵣ (p ⊃ᵣ q))
def star_5_41_reading (p q r : RF signature real order) := reading "⊢ : p ⊃ q . ⊃ . p ⊃ r : ≡ : p . ⊃ . q ⊃ r" (((p ⊃ᵣ q) ⊃ᵣ (p ⊃ᵣ r)) ≡ᵣ (p ⊃ᵣ (q ⊃ᵣ r)))
def star_5_42_reading (p q r : RF signature real order) := reading "⊢ : :p . ⊃ . q ⊃ r : ≡ : p . ⊃ : q . ⊃ . p . r" ((p ⊃ᵣ (q ⊃ᵣ r)) ≡ᵣ (p ⊃ᵣ (q ⊃ᵣ (p ∧ᵣ r))))
def star_5_44_reading (p q r : RF signature real order) := reading "⊢ : :p ⊃ q . ⊃ : p ⊃ r . ≡ : p . ⊃ . q . r" ((p ⊃ᵣ q) ⊃ᵣ ((p ⊃ᵣ r) ≡ᵣ (p ⊃ᵣ (q ∧ᵣ r))))
def star_5_5_reading (p q : RF signature real order) := reading "⊢ : p . ⊃ : p ⊃ q . ≡ . q" (p ⊃ᵣ ((p ⊃ᵣ q) ≡ᵣ q))
def star_5_501_reading (p q : RF signature real order) := reading "⊢ : p . ⊃ : q . ≡ . p ≡ q" (p ⊃ᵣ (q ≡ᵣ (p ≡ᵣ q)))
def star_5_53_reading (p q r s : RF signature real order) := reading "⊢ : p ∨ q ∨ r . ⊃ . s : ≡ : p ⊃ s . q ⊃ s . r ⊃ s" ((((p ∨ᵣ q) ∨ᵣ r) ⊃ᵣ s) ≡ᵣ (((p ⊃ᵣ s) ∧ᵣ (q ⊃ᵣ s)) ∧ᵣ (r ⊃ᵣ s)))
def star_5_54_reading (p q : RF signature real order) := reading "⊢ : p . q . ≡ . p : ∨ : p . q . ≡ . q" (((p ∧ᵣ q) ≡ᵣ p) ∨ᵣ ((p ∧ᵣ q) ≡ᵣ q))
def star_5_55_reading (p q : RF signature real order) := reading "⊢ : p ∨ q . ≡ . p : ∨ : p ∨ q . ≡ . q" (((p ∨ᵣ q) ≡ᵣ p) ∨ᵣ ((p ∨ᵣ q) ≡ᵣ q))
def star_5_6_reading (p q r : RF signature real order) := reading "⊢ : p . ∼q . ⊃ . r : ≡ : p . ⊃ . q ∨ r" (((p ∧ᵣ (∼ᵣ q)) ⊃ᵣ r) ≡ᵣ (p ⊃ᵣ (q ∨ᵣ r)))
def star_5_61_reading (p q : RF signature real order) := reading "⊢ : p ∨ q . ∼q . ≡ . p . ∼q" (((p ∨ᵣ q) ∧ᵣ (∼ᵣ q)) ≡ᵣ (p ∧ᵣ (∼ᵣ q)))
def star_5_62_reading (p q : RF signature real order) := reading "⊢ : p . q . ∨ . ∼q : ≡ . p ∨ ∼q" (((p ∧ᵣ q) ∨ᵣ (∼ᵣ q)) ≡ᵣ (p ∨ᵣ (∼ᵣ q)))
def star_5_63_reading (p q : RF signature real order) := reading "⊢ : p ∨ q . ≡ : p . ∨ . ∼p . q" ((p ∨ᵣ q) ≡ᵣ (p ∨ᵣ ((∼ᵣ p) ∧ᵣ q)))
def star_5_7_reading (p q r : RF signature real order) := reading "⊢ : p ∨ r . ≡ . q ∨ r : ≡ : r . ∨ . p ≡ q" (((p ∨ᵣ r) ≡ᵣ (q ∨ᵣ r)) ≡ᵣ (r ∨ᵣ (p ≡ᵣ q)))
def star_5_71_reading (p q r : RF signature real order) := reading "⊢ : q ⊃ ∼r . ⊃ : p ∨ q . r . ≡ . p . r" ((q ⊃ᵣ (∼ᵣ r)) ⊃ᵣ (((p ∨ᵣ q) ∧ᵣ r) ≡ᵣ (p ∧ᵣ r)))
def star_5_74_reading (p q r : RF signature real order) := reading "⊢ : p . ⊃ . q ≡ r : ≡ : p ⊃ q . ≡ . p ⊃ r" ((p ⊃ᵣ (q ≡ᵣ r)) ≡ᵣ ((p ⊃ᵣ q) ≡ᵣ (p ⊃ᵣ r)))
def star_5_75_reading (p q r : RF signature real order) := reading "⊢ : r ⊃ ∼q . ⊃ : p ≡ q ∨ r . ⊃ : p . ∼q . ≡ . r" ((r ⊃ᵣ (∼ᵣ q)) ⊃ᵣ ((p ≡ᵣ (q ∨ᵣ r)) ⊃ᵣ ((p ∧ᵣ (∼ᵣ q)) ≡ᵣ r)))

#print axioms star_5_1
#print axioms star_5_11
#print axioms star_5_12
#print axioms star_5_13
#print axioms star_5_14
#print axioms star_5_15
#print axioms star_5_16
#print axioms star_5_17
#print axioms star_5_18
#print axioms star_5_19
#print axioms star_5_21
#print axioms star_5_22
#print axioms star_5_23
#print axioms star_5_24
#print axioms star_5_25
#print axioms star_5_3
#print axioms star_5_31
#print axioms star_5_32
#print axioms star_5_33
#print axioms star_5_35
#print axioms star_5_36
#print axioms star_5_4
#print axioms star_5_41
#print axioms star_5_42
#print axioms star_5_44
#print axioms star_5_5
#print axioms star_5_501
#print axioms star_5_53
#print axioms star_5_54
#print axioms star_5_55
#print axioms star_5_6
#print axioms star_5_61
#print axioms star_5_62
#print axioms star_5_63
#print axioms star_5_7
#print axioms star_5_71
#print axioms star_5_74
#print axioms star_5_75

end
end PM.RamifiedSyntax
