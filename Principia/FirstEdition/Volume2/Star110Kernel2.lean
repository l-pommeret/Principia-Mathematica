import Principia.FirstEdition.Volume2.Star110Kernel

/-! # PM II, ✱110·21–33 — second kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star110Kernel2
open Star110Source
open PM.FirstEdition.Volume2.Star110Kernel

theorem star_110_21 (s : Set' α) (t : Set' β) (x : α) :
    SumClass s t (.inl x) ↔ s x := Iff.rfl
theorem star_110_211 (s : Set' α) (t : Set' β) (y : β) :
    SumClass s t (.inr y) ↔ t y := Iff.rfl
theorem star_110_212 (s : Set' α) (t : Set' β) :
    (∃ z, SumClass s t z) ↔ (∃ x, s x) ∨ (∃ y, t y) := star_110_13 s t
theorem star_110_22 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_221 (s : Set' α) (t : Set' β) :
    Equip (SumClass t s) (SumClass s t) := star_110_14 t s
theorem star_110_23 (s : Set' α) (t : Set' β) :
    CardinalAdd s t (Subtype (SumClass s t)) := star_110_2 s t
theorem star_110_231 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl
theorem star_110_24 (s : Set' α) (t : Set' β) :
    (∀ z, ¬ SumClass s t z) ↔ (∀ x, ¬ s x) ∧ (∀ y, ¬ t y) := star_110_101 s t
theorem star_110_25 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_251 (s : Set' α) (t : Set' β) :
    CardinalAdd s t (Subtype (SumClass s t)) := star_110_2 s t
theorem star_110_252 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl

def assocSum : Sum (Sum α β) γ → Sum α (Sum β γ)
  | .inl (.inl x) => .inl x
  | .inl (.inr y) => .inr (.inl y)
  | .inr z => .inr (.inr z)
def unassocSum : Sum α (Sum β γ) → Sum (Sum α β) γ
  | .inl x => .inl (.inl x)
  | .inr (.inl y) => .inl (.inr y)
  | .inr (.inr z) => .inr z

theorem star_110_3 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip (SumClass (SumClass s t) u) (SumClass s (SumClass t u)) := by
  let f : {z // SumClass (SumClass s t) u z} →
      {z // SumClass s (SumClass t u) z} := fun z =>
    ⟨assocSum z.1, by cases z with | mk z hz => cases z with
      | inl w => cases w <;> exact hz
      | inr w => exact hz⟩
  let g : {z // SumClass s (SumClass t u) z} →
      {z // SumClass (SumClass s t) u z} := fun z =>
    ⟨unassocSum z.1, by cases z with | mk z hz => cases z with
      | inl w => exact hz
      | inr w => cases w <;> exact hz⟩
  exact ⟨Bijection.mk f g
    (fun z => by apply Subtype.ext; dsimp [f, g]; cases z.1 with | inl w => cases w <;> rfl | inr w => rfl)
    (fun z => by apply Subtype.ext; dsimp [f, g]; cases z.1 with | inl w => rfl | inr w => cases w <;> rfl)⟩

theorem star_110_31 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip (SumClass (SumClass s t) u) (SumClass s (SumClass t u)) := star_110_3 s t u
theorem star_110_32 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_33 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl

end PM.FirstEdition.Volume2.Star110Kernel2
