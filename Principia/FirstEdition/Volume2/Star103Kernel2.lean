import Principia.FirstEdition.Volume2.Star103Kernel

/-! # PM II, ✱103·28–51 — remaining numbered propositions -/
namespace PM.FirstEdition.Volume2.Star103Kernel2
open Star103Source
open PM.FirstEdition.Volume2.Star103Kernel

theorem equinumerous_trans {s t u : Set' α} :
    Equinumerous s t → Equinumerous t u → Equinumerous s u := by
  rintro ⟨f,g,hf,hg,hgf,hfg⟩ ⟨p,q,hp,hq,hqp,hpq⟩
  refine ⟨fun x => p (f x), fun z => g (q z), ?_, ?_, ?_, ?_⟩
  · intro x hx; exact hp _ (hf _ hx)
  · intro z hz; exact hg _ (hq _ hz)
  · intro x hx; simp only; rw [hqp _ (hf _ hx), hgf _ hx]
  · intro z hz; simp only; rw [hfg _ (hq _ hz), hpq _ hz]

theorem star_103_28 (s t u : Set' α)
    (hst : CardinalClass s t) (htu : CardinalClass t u) :
    CardinalClass s u := equinumerous_trans hst htu

theorem star_103_3 (s t : Set' α) (h : CardinalClass s t) :
    CardinalClass s = CardinalClass t := by
  funext u; apply propext; constructor
  · intro hsu; exact equinumerous_trans (equinumerous_symm h) hsu
  · intro htu; exact equinumerous_trans h htu

theorem star_103_301 (s t : Set' α) :
    CardinalClass s = CardinalClass t ↔ Equinumerous s t := by
  constructor
  · intro he; have hs : CardinalClass s s := equinumerous_refl s
    rw [he] at hs; exact equinumerous_symm hs
  · exact star_103_3 s t

theorem star_103_31 (s t : Set' α) (h : CardinalClass s t) :
    Homogeneous (CardinalClass t) := star_103_14 t

theorem star_103_32 (s t : Set' α) (h : Equinumerous s t) :
    CardinalClass s = CardinalClass t := star_103_3 s t h

theorem star_103_33 (s t : Set' α) :
    CardinalClass s t ↔ CardinalClass s = CardinalClass t := by
  exact (star_103_301 s t).symm

theorem star_103_34 (s t : Set' α) (h : CardinalClass s = CardinalClass t) :
    Equinumerous s t := (star_103_301 s t).mp h

theorem star_103_35 (s : Set' α) :
    Homogeneous (CardinalClass s) ∧ CardinalClass s s :=
  ⟨star_103_14 s,equinumerous_refl s⟩

def SameCardinalClass (s t : Set' α) : Prop := CardinalClass s = CardinalClass t

theorem star_103_4 (s t : Set' α) :
    SameCardinalClass s t ↔ Equinumerous s t := star_103_301 s t

theorem star_103_41 (s : Set' α) : SameCardinalClass s s := rfl

theorem star_103_42 (s t : Set' α) :
    SameCardinalClass s t → SameCardinalClass t s := Eq.symm

theorem star_103_43 (s t u : Set' α) :
    SameCardinalClass s t → SameCardinalClass t u → SameCardinalClass s u := Eq.trans

theorem star_103_44 (s t : Set' α) :
    SameCardinalClass s t ↔ CardinalClass s t := by
  change CardinalClass s = CardinalClass t ↔ Equinumerous s t
  exact star_103_301 s t

theorem star_103_51 (s t : Set' α) (h : Equinumerous s t) :
    Homogeneous (CardinalClass s) ∧ Homogeneous (CardinalClass t) :=
  ⟨star_103_14 s,star_103_14 t⟩

end PM.FirstEdition.Volume2.Star103Kernel2
