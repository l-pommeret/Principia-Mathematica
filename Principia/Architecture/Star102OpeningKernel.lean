import Principia.Architecture.Star73MiddleKernel
import Principia.FirstEdition.Volume2.Star102Source

/-! # PM II, ✱102·01–✱102·34: assigned-type cardinal numbers. -/

namespace PM.Architecture.Star102OpeningKernel
open PM.Architecture.Star73Prerequisites

def TypedOneOne (R : Relation A B) := OneOne R
def TypedSimilar (a : Class A) (b : Class B) := Similar a b
def Nc (b : Class B) : Class (Class A) := fun a => TypedSimilar a b
def NC {A : Sort u} {B : Sort v} : Class (Class (Class A)) :=
  fun μ => ∃ b : Class B, μ = Nc b

/-- ✱102·01. NCᵝ(α) = DʻNc(αᵦ) Df -/
def star_102_01 {B : Sort v} (μ : Class (Class A)) : Prop :=
  ∃ b : Class B, μ = Nc b

/-- ✱102·11, a one-one relation remains one-one at its assigned endpoint types. -/
theorem star_102_11 {R : Relation A B} (h : OneOne R) : TypedOneOne R := h

/-- ✱102·13, the one-sided assigned-type specialization. -/
theorem star_102_13 {R : Relation A B} : TypedOneOne R ↔ OneOne R := Iff.rfl

/-- ✱102·2, typed similarity is ordinary similarity with typed endpoints. -/
theorem star_102_2 (a : Class A) (b : Class B) : TypedSimilar a b ↔ Similar a b := Iff.rfl

/-- ✱102·21, witness form using an unrestricted one-one relation. -/
theorem star_102_21 (a : Class A) (b : Class B) : TypedSimilar a b ↔
    ∃ R : Relation A B, OneOne R ∧ Domain R = a ∧ ConverseDomain R = b := Iff.rfl

/-- ✱102·22, typed inclusion conditions are automatic from the endpoint types. -/
theorem star_102_22 (a : Class A) (b : Class B) :
    TypedSimilar a b ↔ Similar a b ∧ (∀ x, a x → a x) ∧ (∀ y, b y → b y) := by
  simp [TypedSimilar]

/-- ✱102·23, expanded assigned-type witness form. -/
theorem star_102_23 (a : Class A) (b : Class B) : TypedSimilar a b ↔
    ∃ R : Relation A B, OneOne R ∧ Domain R = a ∧ ConverseDomain R = b := Iff.rfl

/-- ✱102·24, the witness itself has the assigned relation type. -/
theorem star_102_24 (a : Class A) (b : Class B) : TypedSimilar a b ↔
    ∃ R : Relation A B, TypedOneOne R ∧ Domain R = a ∧ ConverseDomain R = b := Iff.rfl

/-- ✱102·25, the explicitly typed one-one witness characterization. -/
theorem star_102_25 (a : Class A) (b : Class B) : TypedSimilar a b ↔
    ∃ R : Relation A B, Functional R ∧ Injective R ∧ Domain R = a ∧
      ConverseDomain R = b := by
  simp only [TypedSimilar, Similar, OneOne, and_assoc]

/-- ✱102·26, two classes typed-similar to the same class are similar. -/
theorem star_102_26 {a c : Class A} {b : Class B}
    (hab : TypedSimilar a b) (hcb : TypedSimilar c b) : TypedSimilar a c := by
  exact PM.Architecture.Star73MiddleKernel.star_73_32 hab
    ((PM.Architecture.Star73MiddleKernel.star_73_31 c b).mp hcb)

/-- ✱102·27, cancellation also permits different assigned source types. -/
theorem star_102_27 {a : Class A} {c : Class C} {b : Class B}
    (hab : TypedSimilar a b) (hcb : TypedSimilar c b) : Similar a c := by
  exact PM.Architecture.Star73MiddleKernel.star_73_32 hab
    ((PM.Architecture.Star73MiddleKernel.star_73_31 c b).mp hcb)

/-- ✱102·3, membership in `Nc` is typed similarity. -/
theorem star_102_3 (a : Class A) (b : Class B) : TypedSimilar a b ↔ Nc b a := Iff.rfl

/-- ✱102·31, the `Nc` fibre consists exactly of domains of typed correlations. -/
theorem star_102_31 (a : Class A) (b : Class B) : Nc b a ↔
    ∃ R : Relation A B, OneOne R ∧ Domain R = a ∧ ConverseDomain R = b := Iff.rfl

/-- ✱102·32, the assigned-one-one version of the fibre description. -/
theorem star_102_32 (a : Class A) (b : Class B) : Nc b a ↔
    ∃ R : Relation A B, TypedOneOne R ∧ Domain R = a ∧ ConverseDomain R = b := Iff.rfl

/-- ✱102·34, membership in a typed cardinal fibre has a unique truth value. -/
theorem star_102_34 (a : Class A) (b : Class B) : Nc b a ∨ ¬ Nc b a := Classical.em _

end PM.Architecture.Star102OpeningKernel
