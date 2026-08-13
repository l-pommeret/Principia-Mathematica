import Principia.FirstEdition.Volume2.Star110Source

/-! # PM II, ✱110·1–202 — first exact kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star110Kernel
open Star110Source

theorem star_110_1 (s : Set' α) (t : Set' β) (z : Sum α β) :
    SumClass s t z ↔
      (∃ x, z = .inl x ∧ s x) ∨ (∃ y, z = .inr y ∧ t y) := by
  cases z with
  | inl x => simp [SumClass]
  | inr y => simp [SumClass]

theorem star_110_101 (s : Set' α) (t : Set' β) :
    (∀ z, ¬ SumClass s t z) ↔ (∀ x, ¬ s x) ∧ (∀ y, ¬ t y) := by
  constructor
  · intro h; exact ⟨fun x hx => h (.inl x) hx,fun y hy => h (.inr y) hy⟩
  · rintro ⟨hs,ht⟩ (x|y) h
    · exact hs x h
    · exact ht y h

theorem star_110_11 (s : Set' α) (t : Set' β) (x : α) :
    SumClass s t (.inl x) ↔ s x := Iff.rfl

theorem star_110_12 (s : Set' α) (t : Set' β) (y : β) :
    SumClass s t (.inr y) ↔ t y := Iff.rfl

theorem star_110_13 (s : Set' α) (t : Set' β) :
    (∃ z, SumClass s t z) ↔ (∃ x, s x) ∨ (∃ y, t y) := by
  constructor
  · rintro ⟨x|y,h⟩
    · exact Or.inl ⟨x,h⟩
    · exact Or.inr ⟨y,h⟩
  · rintro (⟨x,hx⟩|⟨y,hy⟩)
    · exact ⟨.inl x,hx⟩
    · exact ⟨.inr y,hy⟩

def swapSum : Sum α β → Sum β α
  | .inl x => .inr x
  | .inr y => .inl y

theorem swapSum_involutive (z : Sum α β) : swapSum (swapSum z) = z := by cases z <;> rfl

theorem star_110_14 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := by
  let f : {z // SumClass s t z} → {z // SumClass t s z} :=
    fun z => ⟨swapSum z.1, by cases z with | mk z hz => cases z <;> exact hz⟩
  let g : {z // SumClass t s z} → {z // SumClass s t z} :=
    fun z => ⟨swapSum z.1, by cases z with | mk z hz => cases z <;> exact hz⟩
  exact ⟨Bijection.mk f g
    (fun z => Subtype.ext (swapSum_involutive z.1))
    (fun z => Subtype.ext (swapSum_involutive z.1))⟩

theorem star_110_15 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass s t) :=
  ⟨Bijection.mk id id (fun _ => rfl) (fun _ => rfl)⟩

theorem star_110_151 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t

theorem star_110_152 (s : Set' α) (t : Set' β) :
    CardinalAdd s t (Subtype (SumClass s t)) :=
  ⟨Bijection.mk id id (fun _ => rfl) (fun _ => rfl)⟩

theorem star_110_16 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl

theorem star_110_17 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t

theorem star_110_18 (s : Set' α) (t : Set' β) :
    (∃ z, SumClass s t z) → (∃ x, s x) ∨ (∃ y, t y) :=
  (star_110_13 s t).mp

theorem star_110_2 (s : Set' α) (t : Set' β) :
    CardinalAdd s t (Subtype (SumClass s t)) :=
  ⟨Bijection.mk id id (fun _ => rfl) (fun _ => rfl)⟩

theorem star_110_201 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl

theorem star_110_202 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t

end PM.FirstEdition.Volume2.Star110Kernel
