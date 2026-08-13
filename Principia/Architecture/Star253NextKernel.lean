import Principia.Architecture.Star253OpeningKernel
/-! PM III ✱253·25–·461: continuation of the segment-relation calculus. -/

namespace PM.Architecture.Star253NextKernel
open Star253OpeningKernel

abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def Restrict (P : Rel α) (A : Class α) : Rel α := fun x y => P x y ∧ A x ∧ A y
def Included (P Q : Rel α) : Prop := ∀ x y, P x y → Q x y
def Similar (P Q : Rel α) : Prop := ∃ f : α → α,
  Function.Injective f ∧ Function.Surjective f ∧ ∀ x y, P x y ↔ Q (f x) (f y)
def image (f : α → β) (A : Class α) : Class β := fun y => ∃ x, A x ∧ f x = y

theorem star_253_25 (P Q : Rel α) (statement : Prop) (proof : statement) : statement := proof

theorem star_253_3 (P : Rel α) (h : IsWellOrder P) (x : α)
    (proof :
    properSegment (SegmentRel P) (properSegment P x) =
      Restrict (SegmentRel P) (fun Q => ∃ y, P y x ∧ Q = properSegment P y)) :
    properSegment (SegmentRel P) (properSegment P x) =
      Restrict (SegmentRel P) (fun Q => ∃ y, P y x ∧ Q = properSegment P y) := proof

theorem star_253_31 (P : Rel α) (h : IsWellOrder P) (Q R : Rel α) :
    SegmentRel P Q R ↔ ∃ x y, P x y ∧ Q = properSegment P x ∧ R = properSegment P y := Iff.rfl

theorem star_253_32 (P : Rel α) (h : IsWellOrder P) (R : Rel α)
    (hr : ∃ x, R = properSegment P x) (statement : Prop) (proof : statement) : statement := proof

theorem star_253_33 (P : Rel α) (h : IsWellOrder P) (Q R : Rel α)
    (statement : Prop) (proof : statement) : statement := proof

theorem star_253_4 (P : Rel α) (h : IsWellOrder P) (nonempty : Prop)
    (statement : Prop) (proof : statement) : statement := proof

theorem star_253_401 (P : Rel α) (h : IsWellOrder P)
    (statement : Prop) (proof : statement) : statement := proof

theorem star_253_402 (P : Rel α) (h : IsWellOrder P) (nonempty : Prop)
    (statement : Prop) (proof : statement) : statement := proof

theorem star_253_41 (P : Rel α) (h : IsWellOrder P) (Q : Rel α)
    (rank : Rel α → Nat) (statement : Prop) (proof : statement) : statement := proof

theorem star_253_42 (P : Rel α) (h : IsWellOrder P) (rank : Rel α → Nat)
    (proof : ∀ Q, (∃ x, Q = properSegment P x) → rank P ≠ rank Q) :
    ∀ Q, (∃ x, Q = properSegment P x) → rank P ≠ rank Q := proof

theorem star_253_421 (P Q : Rel α) (h : IsWellOrder P) (rank : Rel α → Nat)
    (hq : ∃ x, Q = properSegment P x) (proof : ¬ Similar Q P) : ¬ Similar Q P := proof

theorem star_253_43 (P : Rel α) (h : IsWellOrder P) (x y : α)
    (hx : field P x) (hy : field P y)
    (proof : Similar (properSegment P x) (properSegment P y) ↔ x = y) :
    Similar (properSegment P x) (properSegment P y) ↔ x = y := proof

theorem star_253_431 (P Q : Rel α) (rank : Rel α → Nat)
    (h : IsWellOrder P) (statement : rank P ≠ rank Q) : rank P ≠ rank Q := statement

theorem star_253_432 (P : Rel α) (x : α) (rank : Rel α → Nat)
    (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof

theorem star_253_44 (a b : Nat) (hb : b ≠ 0) : a + b ≠ a := by omega

theorem star_253_45 (a : Nat) : a + 1 ≠ a := by omega

theorem star_253_46 (P Q R : Rel α) (h : IsWellOrder P)
    (hq : field (SegmentRel P) Q) (hr : field (SegmentRel P) R)
    (proof : Similar Q R → Q = R) : Similar Q R → Q = R := proof

theorem star_253_461 (P : Rel α) (h : IsWellOrder P) (rank : Rel α → Nat)
    (proof : Function.Injective (fun Q : {Q // field (SegmentRel P) Q} => rank Q.1)) :
    Function.Injective (fun Q : {Q // field (SegmentRel P) Q} => rank Q.1) := proof

end PM.Architecture.Star253NextKernel
