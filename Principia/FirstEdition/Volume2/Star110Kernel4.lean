import Principia.FirstEdition.Volume2.Star110Kernel3

/-! # PM II, ✱110·501–61 — fourth kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star110Kernel4
open Star110Source
open PM.FirstEdition.Volume2.Star110Kernel
open PM.FirstEdition.Volume2.Star110Kernel2
open PM.FirstEdition.Volume2.Star110Kernel3

theorem star_110_501 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl
theorem star_110_51 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_52 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip (SumClass (SumClass s t) u) (SumClass s (SumClass t u)) := star_110_3 s t u
theorem star_110_521 (s : Set' α) (t : Set' β) :
    CardinalAdd s t (Subtype (SumClass s t)) := star_110_2 s t
theorem star_110_53 (s : Set' α) : Equip (SumClass s Empty) s := star_110_4 s
theorem star_110_531 (s : Set' α) : Equip (SumClass Empty s) s := star_110_402 s
theorem star_110_54 (s : Set' α) : Equip s s := equip_refl s
theorem star_110_541 (s : Set' α) (t : Set' β) :
    Equip s t → Equip t s := equip_symm
theorem star_110_55 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip s t → Equip t u → Equip s u := equip_trans
theorem star_110_551 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_56 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass s t) := equip_refl _
theorem star_110_561 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_57 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl
theorem star_110_6 (s : Set' α) (t : Set' β) :
    (∃ z, SumClass s t z) ↔ (∃ x, s x) ∨ (∃ y, t y) := star_110_13 s t
theorem star_110_61 (s : Set' α) (t : Set' β) :
    (∀ z, ¬ SumClass s t z) ↔ (∀ x, ¬ s x) ∧ (∀ y, ¬ t y) := star_110_101 s t

end PM.FirstEdition.Volume2.Star110Kernel4
