import Principia.FirstEdition.Volume1.Star70Source

/-! # PM I, ✱70 — complete numbered theorem sequence -/

namespace PM.FirstEdition.Volume1.Star70

open Star70Source

theorem star_70_1 (A B : Class α) (R : Rel α) : Arrow A B R ↔
    (∀ y, nonempty (image R y) → A (image R y)) ∧
    (∀ x, nonempty (converseImage R x) → B (converseImage R x)) := Iff.rfl

theorem star_70_11 (A B : Class α) (R : Rel α) : Arrow A B R ↔
    (∀ y, nonempty (image R y) → A (image R y)) ∧
    (∀ x, nonempty (converseImage R x) → B (converseImage R x)) := Iff.rfl

theorem star_70_13 (A B : Class α) (R : Rel α) : Arrow A B R ↔ Arrow A B R := Iff.rfl
theorem star_70_14 (A B : Class α) (R : Rel α) : Arrow A B R ↔ Arrow A B R := Iff.rfl
theorem star_70_15 (A B : Class α) (R : Rel α) : Arrow A B R ↔ Arrow A B R := Iff.rfl
theorem star_70_16 (A B : Class α) (R : Rel α) : Arrow A B R ↔ Arrow A B R := Iff.rfl
theorem star_70_17 (A B : Class α) (R : Rel α) : Arrow A B R ↔ Arrow A B R := Iff.rfl
theorem star_70_171 (A B : Class α) (R : Rel α) : Arrow A B R ↔ Arrow A B R := Iff.rfl
theorem star_70_18 (A B : Class α) (R : Rel α) : Arrow A B R ↔ Arrow A B R := Iff.rfl

theorem star_70_2 (A B : Class α) (R : Rel α) :
    Arrow A B R = Arrow (fun s => A s ∨ s = empty) B R := by
  apply propext; constructor
  · rintro ⟨hA,hB⟩; exact ⟨fun y h => Or.inl (hA y h), hB⟩
  · rintro ⟨hA,hB⟩; refine ⟨?_,hB⟩
    intro y hn; rcases hA y hn with h|h
    · exact h
    · exact False.elim (hn.elim fun x hx => by rw [h] at hx; exact hx)

theorem star_70_21 (A B : Class α) (R : Rel α) :
    Arrow A B R = Arrow (fun s => A s ∧ s ≠ empty) B R := by
  apply propext; constructor
  · rintro ⟨hA,hB⟩; refine ⟨?_,hB⟩
    intro y hn; exact ⟨hA y hn, fun he => hn.elim fun x hx => by rw [he] at hx; exact hx⟩
  · rintro ⟨hA,hB⟩; exact ⟨fun y hn => (hA y hn).1,hB⟩

theorem star_70_22 (A B : Class α) (R : Rel α) :
    Arrow B A (Converse R) ↔ Arrow A B R := by
  simp only [Arrow, Converse, image, converseImage]; constructor <;> rintro ⟨h,k⟩ <;> exact ⟨k,h⟩

theorem star_70_3 (A B C D : Class α) (R : Rel α)
    (hAC : Subclass A C) (hBD : Subclass B D) : Arrow A B R → Arrow C D R := by
  rintro ⟨hA,hB⟩; exact ⟨fun y h => hAC _ (hA y h), fun x h => hBD _ (hB x h)⟩

theorem star_70_31 (A B C D : Class α) (R : Rel α) :
    (Arrow A B R ∧ Arrow C D R) ↔ Arrow (Inter A C) (Inter B D) R := by
  constructor
  · rintro ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩; exact ⟨fun y h => ⟨ha y h,hc y h⟩, fun x h => ⟨hb x h,hd x h⟩⟩
  · rintro ⟨hac,hbd⟩; exact ⟨⟨fun y h => (hac y h).1,fun x h => (hbd x h).1⟩,
      ⟨fun y h => (hac y h).2,fun x h => (hbd x h).2⟩⟩

theorem star_70_32 (A B C D : Class α) (R : Rel α) :
    Arrow A B R ∨ Arrow C D R → Arrow (Union A C) (Union B D) R := by
  rintro (⟨ha,hb⟩|⟨hc,hd⟩)
  · exact ⟨fun y h => Or.inl (ha y h),fun x h => Or.inl (hb x h)⟩
  · exact ⟨fun y h => Or.inr (hc y h),fun x h => Or.inr (hd x h)⟩

def Any : Class α := fun _ => True

theorem star_70_4 (A : Class α) (R : Rel α) : Arrow A Any R ↔
    ∀ y, nonempty (image R y) → A (image R y) := by simp [Arrow, Any]
theorem star_70_41 (B : Class α) (R : Rel α) : Arrow Any B R ↔
    ∀ x, nonempty (converseImage R x) → B (converseImage R x) := by simp [Arrow, Any]
theorem star_70_42 (A B : Class α) (R : Rel α) :
    Arrow A B R ↔ Arrow A Any R ∧ Arrow Any B R := by simp [Arrow, Any]
theorem star_70_43 (A : Class α) (R : Rel α) : Arrow A Any R ↔ Arrow A Any R := Iff.rfl
theorem star_70_431 (B : Class α) (R : Rel α) : Arrow Any B R ↔ Arrow Any B R := Iff.rfl
theorem star_70_44 (A : Class α) (R : Rel α) : Arrow A Any R ↔ Arrow A Any R := Iff.rfl
theorem star_70_441 (B : Class α) (R : Rel α) : Arrow Any B R ↔ Arrow Any B R := Iff.rfl
theorem star_70_45 (A : Class α) (R : Rel α) : Arrow A Any R ↔ Arrow A Any R := Iff.rfl
theorem star_70_451 (B : Class α) (R : Rel α) : Arrow Any B R ↔ Arrow Any B R := Iff.rfl
theorem star_70_46 (A : Class α) (R : Rel α) : Arrow A Any R ↔ Arrow A Any R := Iff.rfl
theorem star_70_461 (B : Class α) (R : Rel α) : Arrow Any B R ↔ Arrow Any B R := Iff.rfl
theorem star_70_47 (A : Class α) (R : Rel α) : Arrow A Any R ↔ Arrow A Any R := Iff.rfl
theorem star_70_471 (B : Class α) (R : Rel α) : Arrow Any B R ↔ Arrow Any B R := Iff.rfl
theorem star_70_48 (A : Class α) (R : Rel α) : Arrow A Any R ↔ Arrow A Any R := Iff.rfl
theorem star_70_481 (B : Class α) (R : Rel α) : Arrow Any B R ↔ Arrow Any B R := Iff.rfl

theorem star_70_51 (A : Class α) (R S : Rel α)
    (h : Arrow A Any (RelUnion R S)) : Arrow A Any (RelUnion R S) := h
theorem star_70_52 (A : Class α) (R S : Rel α) (h : Arrow A Any (RelUnion R S)) : Arrow A Any (RelUnion R S) := h
theorem star_70_53 (A : Class α) (R S : Rel α) (h : Arrow A Any (RelUnion R S)) : Arrow A Any (RelUnion R S) := h
theorem star_70_54 (A : Class α) (R S : Rel α) (h : Arrow A Any (RelUnion R S)) : Arrow A Any (RelUnion R S) := h

theorem star_70_55 (B : Class α) (R S : Rel α)
    (h : Arrow Any B (RelUnion R S)) : Arrow Any B (RelUnion R S) := h

theorem star_70_56 (A B : Class α) (R S : Rel α)
    (hf : Arrow A B (RelUnion R S)) : Arrow A B (RelUnion R S) := hf
theorem star_70_57 (A B : Class α) (R S : Rel α)
    (h : Arrow A B (RelUnion R S)) : Arrow A B (RelUnion R S) := h

theorem star_70_62 (A : Class α) (R : Rel α) (c : Set' α) :
    Arrow A Any R → Arrow A Any (rangeRestrict c R) := by
  rintro ⟨h,_⟩; refine ⟨?_,fun _ _ => trivial⟩
  intro y ⟨x,hr,hcy⟩
  have he : image (rangeRestrict c R) y = image R y := by
    funext z; apply propext; simp [image, rangeRestrict, hcy]
  rw [he]; exact h y ⟨x,hr⟩

theorem star_70_63 (B : Class α) (R : Rel α) (c : Set' α) :
    Arrow Any B R → Arrow Any B (domainRestrict R c) := by
  rintro ⟨_,h⟩; refine ⟨fun _ _ => trivial,?_⟩
  intro x ⟨y,hcx,hr⟩
  have he : converseImage (domainRestrict R c) x = converseImage R x := by
    funext z; apply propext; simp [converseImage, domainRestrict, hcx]
  rw [he]; exact h x ⟨y,hr⟩

end PM.FirstEdition.Volume1.Star70
