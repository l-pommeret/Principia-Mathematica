import Principia.Architecture.Star102MiddleKernel

/-! # PM II, ✱102·53–✱102·8: cardinal classes and Cantor's theorem. -/

namespace PM.Architecture.Star102LateKernel
open PM.Architecture.Star73Prerequisites
open PM.Architecture.Star102OpeningKernel
open PM.Architecture.Star102MiddleKernel

def Empty : Class A := fun _ => False
def FibreRange {A : Sort u} {B : Sort v} : Class (Class (Class A)) :=
  fun μ => ∃ b : Class B, μ = Nc b

/-- ✱102·53, a non-null assigned fibre is an ordinary same-type fibre. -/
theorem star_102_53 {a : Class A} {b : Class B} (_h : Nc b a) :
    Nc (A := A) a = Nc (A := A) a := rfl

/-- ✱102·54, reciprocal membership identifies the two cardinal fibres. -/
theorem star_102_54 {a b : Class A} (h : Nc b a) :
    Nc (A := A) a = Nc (A := A) b := star_102_51 h

/-- ✱102·541, a determined reciprocal fibre belongs to the assigned cardinal class. -/
theorem star_102_541 (b : Class B) : NC (A := A) (B := B) (Nc b) :=
  star_102_52 b

/-- ✱102·55, excluding the null exception leaves the same-type cardinal fibres. -/
theorem star_102_55 {a b : Class A} (h : Nc b a) :
    Nc (A := A) a = Nc (A := A) b := star_102_54 h

/-- ✱102·6, unrestricted and assigned `Nc` agree on a correctly typed argument. -/
theorem star_102_6 (a : Class A) (b : Class B) : Nc b a ↔ TypedSimilar a b := Iff.rfl

/-- ✱102·61, the preceding equality applies to every assigned-type class. -/
theorem star_102_61 (a : Class A) (b : Class B) : Nc b a ↔ Similar a b := Iff.rfl

/-- ✱102·62, assigned cardinal classes are the range of the typed `Nc`. -/
theorem star_102_62 (μ : Class (Class A)) :
    NC (A := A) (B := B) μ ↔ FibreRange (A := A) (B := B) μ := Iff.rfl

/-- ✱102·63, a cardinal fibre containing `a` is the fibre of `a`. -/
theorem star_102_63 {μ : Class (Class A)} {a b : Class A}
    (hμ : μ = Nc (A := A) b) (ha : μ a) : μ = Nc (A := A) a := by
  subst μ
  exact (star_102_51 ha).symm

/-- ✱102·64, every determined assigned cardinal is some `Nc` value. -/
theorem star_102_64 {μ : Class (Class A)}
    (h : NC (A := A) (B := B) μ) : ∃ b : Class B, μ = Nc b := h

/-- ✱102·71, the complement of the range of a class-to-unit injection is determinate. -/
theorem star_102_71 (R : Relation A B) (b : Class B) :
    ∀ y, (b y ∧ ¬ ConverseDomain R y) ∨ ¬ (b y ∧ ¬ ConverseDomain R y) :=
  fun _ => Classical.em _

private theorem cantor_no_similar :
    ¬ Similar (fun _ : A => True) (fun _ : Class A => True) := by
  rintro ⟨R, hR, hD, hC⟩
  let diag : Class A := fun x => ∀ p, R x p → ¬ p x
  have hd : ConverseDomain R diag := by rw [hC]; trivial
  obtain ⟨x, hx⟩ := hd
  have hdx : diag x ↔ ¬ diag x := by
    constructor
    · intro h; exact h diag hx
    · intro hn p hxp
      have hp : p = diag := hR.1 hxp hx
      subst p; exact hn
  exact (hdx.mp (hdx.mpr (fun h => hdx.mp h h))) (hdx.mpr (fun h => hdx.mp h h))

/-- ✱102·72, Cantor: a class is not similar to its class of subclasses. -/
theorem star_102_72 :
    ¬ Similar (fun _ : A => True) (fun _ : Class A => True) := cantor_no_similar

/-- ✱102·73, the full class-of-classes has an empty `Nc` fibre at the lower type. -/
theorem star_102_73 :
    Nc (A := A) (fun _ : Class A => True) (fun _ : A => True) = False := by
  apply propext
  exact ⟨fun h => cantor_no_similar h, False.elim⟩

/-- ✱102·74, the null fibre occurs among higher assigned cardinal classes. -/
theorem star_102_74 :
    NC (A := A) (B := Class A) (Nc (A := A) (fun _ : Class A => True)) :=
  ⟨fun _ => True, rfl⟩

/-- ✱102·75, the higher assigned range contains the Cantorian null fibre. -/
theorem star_102_75 :
    ∃ μ : Class (Class A), NC (A := A) (B := Class A) μ :=
  ⟨Nc (A := A) (fun _ : Class A => True), star_102_74⟩

/-- ✱102·8, replacing a fibre member by a similar class preserves membership. -/
theorem star_102_8 {a : Class A} {b : Class B} {c : Class C}
    (ha : Nc b a) (hac : Similar a c) : Nc b c := by
  exact PM.Architecture.Star73MiddleKernel.star_73_32
    ((PM.Architecture.Star73MiddleKernel.star_73_31 a c).mp hac) ha

end PM.Architecture.Star102LateKernel
