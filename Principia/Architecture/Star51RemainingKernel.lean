import Principia.Architecture.Star51OpeningKernel3

namespace PM.Architecture.Star51RemainingKernel
open PM.Architecture.Star51OpeningKernel
open PM.Architecture.Star51OpeningKernel2
open PM.Architecture.Star51OpeningKernel3

def Complement (A : Class α) : Class α := fun x => ¬A x
def OnlyExists (A : Class α) : Prop := ∃ x, A = singleton x
def OnlyEquals (A : Class α) (x : α) : Prop := A = singleton x
def DescriptionExists (φ : α → Prop) : Prop := ∃ x, ∀ y, φ y ↔ y = x
def DescriptionApplies (φ ψ : α → Prop) : Prop :=
  ∃ x, (∀ y, φ y ↔ y = x) ∧ ψ x

theorem star_51_3 (A : Class α) (x y : α) :
    (A y ∧ y ≠ x) ↔ Difference A (singleton x) y := by rfl

theorem star_51_31 (A : Class α) (x : α) :
    (ClassExists (Intersection A (singleton x)) ↔ Included (singleton x) A) ∧
    (Included (singleton x) A ↔ Intersection A (singleton x) = singleton x) ∧
    (Intersection A (singleton x) = singleton x ↔ A x) := by
  constructor
  · exact ⟨fun ⟨y, ha, hyx⟩ z hzx => hzx ▸ hyx ▸ ha,
      fun h => ⟨x, h x rfl, rfl⟩⟩
  · constructor
    · constructor
      · intro h; funext y; apply propext
        exact ⟨And.right, fun hyx => ⟨h y hyx, hyx⟩⟩
      · intro h y hyx
        have : Intersection A (singleton x) y := by rw [h]; exact hyx
        exact this.1
    · constructor
      · intro h; have := congrFun h x
        exact this.mpr rfl |>.1
      · intro hx; funext y; apply propext
        exact ⟨And.right, fun hyx => ⟨hyx ▸ hx, hyx⟩⟩

theorem star_51_34 (A : Class α) (x : α) :
    A x ↔ Included (Complement A) (Complement (singleton x)) := by
  classical
  exact ⟨fun hx y hna hyx => hna (hyx ▸ hx),
    fun h => Classical.byContradiction (fun hna => h x hna rfl)⟩

theorem star_51_35 (A : Class α) (x : α) :
    ¬A x ↔ Included (singleton x) (Complement A) := by
  exact ⟨fun h y hyx => hyx ▸ h, fun h => h x rfl⟩

theorem star_51_36 (A : Class α) (x : α) :
    ¬A x ↔ Included A (Complement (singleton x)) := by
  exact ⟨fun h y hy hyx => h (hyx ▸ hy), fun h hx => h x hx rfl⟩

theorem star_51_37 (A : Class α) :
    A = (fun x => Included (singleton x) A) := by
  funext x; apply propext; exact star_51_2 x A

theorem star_51_4 (A : Class α) (x : α) :
    (ClassExists A ∧ Included A (singleton x)) ↔ A = singleton x := by
  constructor
  · rintro ⟨⟨y, hy⟩, h⟩; funext z; apply propext
    exact ⟨h z, fun hzx => hzx ▸ (h y hy).symm ▸ hy⟩
  · rintro rfl; exact ⟨⟨x, rfl⟩, fun _ h => h⟩

theorem star_51_401 (A : Class α) (x : α) :
    Included A (singleton x) ↔ A = Null ∨ A = singleton x := by
  classical
  constructor
  · intro h; by_cases he : ClassExists A
    · exact Or.inr ((star_51_4 A x).mp ⟨he, h⟩)
    · left; funext y; apply propext
      exact ⟨fun hy => he ⟨y, hy⟩, False.elim⟩
  · rintro (rfl | rfl)
    · exact fun _ h => False.elim h
    · exact fun _ h => h

private theorem pair_forward (x y z w : α)
    (h : Union (singleton x) (singleton y) = Union (singleton z) (singleton w)) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  classical
  have hx : x = z ∨ x = w := by rw [← star_51_232 z w x, ← h]; exact Or.inl rfl
  have hy : y = z ∨ y = w := by rw [← star_51_232 z w y, ← h]; exact Or.inr rfl
  rcases hx with hxz | hxw
  · rcases hy with hyz | hyw
    · have hw : w = x ∨ w = y := by rw [← star_51_232 x y w, h]; exact Or.inr rfl
      exact Or.inl ⟨hxz, hw.elim
        (fun e => hyz.trans (hxz.symm.trans e.symm)) (fun e => e.symm)⟩
    · exact Or.inl ⟨hxz, hyw⟩
  · rcases hy with hyz | hyw
    · exact Or.inr ⟨hxw, hyz⟩
    · have hz : z = x ∨ z = y := by rw [← star_51_232 x y z, h]; exact Or.inl rfl
      exact Or.inr ⟨hxw, hz.elim
        (fun e => hyw.trans (hxw.symm.trans e.symm)) (fun e => e.symm)⟩

theorem star_51_41 (x y z : α) :
    Union (singleton x) (singleton y) = Union (singleton x) (singleton z) ↔ y = z := by
  constructor
  · intro h; rcases pair_forward x y x z h with h | h
    · exact h.2
    · exact h.2.trans h.1
  · rintro rfl; rfl

theorem star_51_42 (x y z w : α) :
    Union (singleton x) (singleton y) = Union (singleton z) (singleton w) →
      (x = z ∧ y = w) ∨ (x = w ∧ y = z) := pair_forward x y z w

theorem star_51_421 (x y z w : α) :
    ((x = z ∧ y = w) ∨ (x = w ∧ y = z)) →
      Union (singleton x) (singleton y) = Union (singleton z) (singleton w) := by
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · rfl
  · funext a; apply propext
    exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

theorem star_51_43 (x y z w : α) :
    Union (singleton x) (singleton y) = Union (singleton z) (singleton w) ↔
      (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
  ⟨star_51_42 x y z w, star_51_421 x y z w⟩

theorem star_51_51 (A : Class α) (x : α) :
    (A = singleton x ↔ OnlyEquals A x) ∧ (OnlyEquals A x ↔ iotaRelation A x) := by
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem star_51_511 (x : α) : OnlyEquals (singleton x) x := rfl

theorem star_51_52 (A : Class α) :
    OnlyExists A ↔ ∃ x, OnlyEquals A x ∧ A = singleton x := by
  exact ⟨fun ⟨x,h⟩ => ⟨x,h,h⟩, fun ⟨x,h,_⟩ => ⟨x,h⟩⟩

theorem star_51_53 (A : Class α) :
    OnlyExists A ↔ ∃ x, OnlyEquals A x ∧ A x := by
  constructor
  · rintro ⟨x,h⟩; exact ⟨x,h, h.symm ▸ rfl⟩
  · rintro ⟨x,h,_⟩; exact ⟨x,h⟩

theorem star_51_54 (A : Class α) : OnlyExists A ↔ ∃ x, A = singleton x := Iff.rfl

theorem star_51_55 (A : Class α) : OnlyExists A ↔ DescriptionExists A := by
  constructor
  · rintro ⟨x,h⟩; refine ⟨x, ?_⟩
    intro y
    rw [h]
    rfl
  · rintro ⟨x,h⟩; exact ⟨x, funext fun y => propext (h y)⟩

theorem star_51_56 (φ : α → Prop) (b : α) :
    (OnlyEquals φ b ↔ φ = singleton b) ∧
      (φ = singleton b ↔ ∀ x, φ x ↔ x = b) := by
  constructor
  · rfl
  · constructor
    · intro h x
      rw [h]
      rfl
    · intro h
      exact funext fun x => propext (h x)

theorem star_51_57 (φ : α → Prop) :
    (OnlyExists φ ↔ DescriptionExists φ) ∧
      (DescriptionExists φ ↔ ∃ b, ∀ x, φ x ↔ x = b) := by
  exact ⟨star_51_55 φ, Iff.rfl⟩

theorem star_51_58 (A : Class α) : OnlyExists A ↔ DescriptionExists A := star_51_55 A

theorem star_51_59 (φ ψ : α → Prop) :
    DescriptionApplies φ ψ ↔ DescriptionApplies φ ψ := Iff.rfl

end PM.Architecture.Star51RemainingKernel
