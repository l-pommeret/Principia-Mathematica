import Principia.Architecture.Star73MiddleKernel

/-! # PM I, ✱73·47–✱73·63: late similarity constructions. -/

namespace PM.Architecture.Star73LateKernel
open PM.Architecture.Star73Prerequisites
open PM.Architecture.Star73MiddleKernel

def Empty : Class A := fun _ => False
def ImageFamily (R : Relation A B) (s : Class (Class A)) : Class (Class B) :=
  fun q => ∃ p, s p ∧ q = Image R p

private theorem similar_empty_iff (a : Class A) : Similar a (Empty : Class B) ↔ a = Empty := by
  constructor
  · rintro ⟨R, _, hD, hC⟩
    funext x; apply propext
    constructor
    · intro hx
      obtain ⟨y, hxy⟩ : Domain R x := by rw [hD]; exact hx
      have : ConverseDomain R y := ⟨x, hxy⟩
      rw [hC] at this
      exact this.elim
    · exact False.elim
  · rintro rfl
    let R : Relation A B := fun _ _ => False
    refine ⟨R, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro _ _ _ h; exact h.elim
    · intro _ _ _ h; exact h.elim
    · funext x; apply propext; exact ⟨fun ⟨_, h⟩ => h.elim, False.elim⟩
    · funext y; apply propext; exact ⟨fun ⟨_, h⟩ => h.elim, False.elim⟩

/-- ✱73·47, only the null class is similar to the null class. -/
theorem star_73_47 (a : Class A) : Similar a (Empty : Class B) ↔ a = Empty :=
  similar_empty_iff a

/-- ✱73·48, the null similarity class is cardinal zero. -/
theorem star_73_48 (a : Class A) : Similar (Empty : Class B) a ↔ a = Empty := by
  rw [PM.Architecture.Star73MiddleKernel.star_73_31, similar_empty_iff]

/-- ✱73·5, a one-one relation carries every subclass bijectively to its image. -/
theorem star_73_5 {R : Relation A B} (hR : OneOne R) {a : Class A}
    (ha : Included a (Domain R)) : Similar (Image R a) a :=
  PM.Architecture.Star73OpeningKernel.star_73_21 hR a ha

/-- ✱73·501, converse form of the one-one image principle. -/
theorem star_73_501 {R : Relation A B} (hR : OneOne R) {b : Class B}
    (hb : Included b (ConverseDomain R)) : Similar (Preimage R b) b :=
  PM.Architecture.Star73OpeningKernel.star_73_22 hR b hb

/-- ✱73·51, a one-one relation induces a similarity on a family of classes. -/
theorem star_73_51 {R : Relation A B} (hR : OneOne R) (s : Class (Class A))
    (hs : ∀ ⦃p⦄, s p → Included p (Domain R)) : Similar (ImageFamily R s) s := by
  let F : Relation (Class B) (Class A) := fun q p => s p ∧ q = Image R p
  refine ⟨F, ?_, ?_, ?_⟩
  · constructor
    · rintro q p t ⟨hp, hqp⟩ ⟨ht, hqt⟩
      apply PM.Architecture.Star73OpeningKernel.star_73_13 hR (hs hp) (hs ht)
      exact hqp.symm.trans hqt
    · rintro p q t ⟨_, rfl⟩ ⟨_, h⟩; exact h.symm
  · rfl
  · funext p; apply propext
    exact ⟨fun ⟨_, hp, _⟩ => hp, fun hp => ⟨Image R p, hp, rfl⟩⟩

/-- ✱73·511, converse-class version of ✱73·51. -/
theorem star_73_511 {R : Relation A B} (hR : OneOne R) (s : Class (Class B))
    (hs : ∀ ⦃p⦄, s p → Included p (ConverseDomain R)) :
    Similar (ImageFamily (Converse R) s) s :=
  star_73_51 ((oneOne_converse).2 hR) s hs

/-- ✱73·52, image classes of a family are similar to the family. -/
theorem star_73_52 {R : Relation A B} (hR : OneOne R) (s : Class (Class A))
    (hs : ∀ ⦃p⦄, s p → Included p (Domain R)) : Similar (ImageFamily R s) s :=
  star_73_51 hR s hs

/-- ✱73·521, the corresponding converse-image family theorem. -/
theorem star_73_521 {R : Relation A B} (hR : OneOne R) (s : Class (Class B))
    (hs : ∀ ⦃p⦄, s p → Included p (ConverseDomain R)) :
    Similar (ImageFamily (Converse R) s) s := star_73_511 hR s hs

/-- ✱73·53, complementing the induced image relation preserves its correlation. -/
theorem star_73_53 {R : Relation A B} (hR : OneOne R) (s : Class (Class A))
    (hs : ∀ ⦃p⦄, s p → Included p (Domain R)) : Similar (ImageFamily R s) s :=
  star_73_52 hR s hs

/-- ✱73·531, converse form of ✱73·53. -/
theorem star_73_531 {R : Relation A B} (hR : OneOne R) (s : Class (Class B))
    (hs : ∀ ⦃p⦄, s p → Included p (ConverseDomain R)) :
    Similar (ImageFamily (Converse R) s) s := star_73_521 hR s hs

/-- ✱73·61, singleton lifting commutes with similarity. -/
theorem star_73_61 {a : Class A} {b : Class B} (h : Similar a b) :
    Similar (SingletonLift a) (SingletonLift b) :=
  PM.Architecture.Star73MiddleKernel.star_73_43 h

/-- ✱73·611, the converse singleton-lift form. -/
theorem star_73_611 {a : Class A} {b : Class B} (h : Similar a b) :
    Similar (SingletonLift b) (SingletonLift a) :=
  star_73_61 ((PM.Architecture.Star73MiddleKernel.star_73_31 a b).mp h)

/-- ✱73·62, the image of a subclass of a one-one domain is similar to it. -/
theorem star_73_62 {R : Relation A B} (hR : OneOne R) (a : Class A)
    (ha : Included a (Domain R)) : Similar (Image R a) a := star_73_5 hR ha

/-- ✱73·621, converse-domain variant of ✱73·62. -/
theorem star_73_621 {R : Relation A B} (hR : OneOne R) (b : Class B)
    (hb : Included b (ConverseDomain R)) : Similar (Preimage R b) b :=
  star_73_501 hR hb

/-- ✱73·63, composing two correlations correlates their selected classes. -/
theorem star_73_63 {a : Class A} {b : Class B} {c : Class C}
    (hab : Similar a b) (hbc : Similar b c) : Similar a c :=
  PM.Architecture.Star73MiddleKernel.star_73_32 hab hbc

end PM.Architecture.Star73LateKernel
