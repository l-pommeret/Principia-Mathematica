import Principia.FirstEdition.Volume2.Star103Source

/-! # PM II, ✱103·1–27 — first exact kernel macro-lot -/
namespace PM.FirstEdition.Volume2.Star103Kernel
open Star103Source

theorem equinumerous_refl (s : Set' α) : Equinumerous s s := by
  exact ⟨id,id,fun _ h => h,fun _ h => h,fun _ _ => rfl,fun _ _ => rfl⟩

theorem equinumerous_symm {s t : Set' α} : Equinumerous s t → Equinumerous t s := by
  rintro ⟨f,g,hf,hg,hgf,hfg⟩; exact ⟨g,f,hg,hf,hfg,hgf⟩

/-- ✱103·1. Membership in the represented cardinal class. -/
theorem star_103_1 (s t : Set' α) : CardinalClass s t ↔ Equinumerous s t := Iff.rfl

theorem star_103_11 (s : Set' α) : CardinalClass s s := equinumerous_refl s

theorem star_103_12 (s t : Set' α) :
    CardinalClass s t → CardinalClass t s := equinumerous_symm

theorem star_103_13 (s t : Set' α) :
    CardinalClass s t ↔ CardinalClass t s :=
  ⟨equinumerous_symm,equinumerous_symm⟩

theorem star_103_14 (s : Set' α) : Homogeneous (CardinalClass s) := by
  intro a ha b hb
  rcases ha with ⟨f,g,hf,hg,hgf,hfg⟩
  rcases hb with ⟨p,q,hp,hq,hqp,hpq⟩
  refine ⟨fun x => p (g x), fun y => f (q y), ?_, ?_, ?_, ?_⟩
  · intro x hx; exact hp _ (hg _ hx)
  · intro y hy; exact hf _ (hq _ hy)
  · intro x hx; simp only; rw [hqp _ (hg _ hx), hfg _ hx]
  · intro y hy; simp only; rw [hgf _ (hq _ hy), hpq _ hy]

theorem star_103_15 (K : Set' (Set' α)) (hK : Homogeneous K)
    {s t} (hs : K s) (ht : K t) : Equinumerous s t := hK s hs t ht

theorem star_103_16 (s t : Set' α) (h : Equinumerous s t) :
    CardinalClass s t := h

/-- ✱103·2. A represented cardinal class is nonempty. -/
theorem star_103_2 (s : Set' α) : ∃ t, CardinalClass s t := ⟨s,equinumerous_refl s⟩

theorem star_103_21 (s : Set' α) : Homogeneous (CardinalClass s) := star_103_14 s

theorem star_103_22 (s t : Set' α) (h : CardinalClass s t) :
    CardinalClass t s := equinumerous_symm h

theorem star_103_23 (s t : Set' α) (h : CardinalClass s t) :
    Equinumerous s t := h

theorem star_103_24 (s : Set' α) : CardinalClass s s := equinumerous_refl s

theorem star_103_25 (s t : Set' α) :
    CardinalClass s t ↔ Equinumerous t s := by
  constructor <;> exact equinumerous_symm

theorem star_103_26 (s t : Set' α) (h : Equinumerous s t) :
    Homogeneous (CardinalClass t) := star_103_14 t

theorem star_103_27 (s t : Set' α) (h : CardinalClass s t) :
    ∃ K, Homogeneous K ∧ K s ∧ K t := by
  refine ⟨CardinalClass s,star_103_14 s,equinumerous_refl s,h⟩

end PM.FirstEdition.Volume2.Star103Kernel
