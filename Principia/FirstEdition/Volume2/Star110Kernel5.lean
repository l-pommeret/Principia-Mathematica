import Principia.FirstEdition.Volume2.Star110Kernel4

/-! # PM II, ✱110·62–72 — final numbered propositions -/
namespace PM.FirstEdition.Volume2.Star110Kernel5
open Star110Source
open PM.FirstEdition.Volume2.Star110Kernel
open PM.FirstEdition.Volume2.Star110Kernel2
open PM.FirstEdition.Volume2.Star110Kernel3
open PM.FirstEdition.Volume2.Star110Kernel4

theorem star_110_62 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_63 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip (SumClass (SumClass s t) u) (SumClass s (SumClass t u)) := star_110_3 s t u
theorem star_110_631 (s : Set' α) : Equip (SumClass s Empty) s := star_110_4 s
theorem star_110_632 (s : Set' α) : Equip (SumClass Empty s) s := star_110_402 s
theorem star_110_64 (s : Set' α) (t : Set' β) :
    CardinalAdd s t = Cardinal (SumClass s t) := rfl
theorem star_110_641 (s : Set' α) (t : Set' β) :
    CardinalAdd s t (Subtype (SumClass s t)) := star_110_2 s t
theorem star_110_642 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_643 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass s t) := equip_refl _
theorem star_110_7 (s : Set' α) (t : Set' β) :
    (∃ z, SumClass s t z) ↔ (∃ x, s x) ∨ (∃ y, t y) := star_110_13 s t
theorem star_110_71 (s : Set' α) (t : Set' β) :
    Equip (SumClass s t) (SumClass t s) := star_110_14 s t
theorem star_110_72 (s : Set' α) (t : Set' β) (u : Set' γ) :
    Equip (SumClass (SumClass s t) u) (SumClass s (SumClass t u)) := star_110_3 s t u

end PM.FirstEdition.Volume2.Star110Kernel5
