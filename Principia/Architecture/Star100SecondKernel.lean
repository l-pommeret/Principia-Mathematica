import Principia.Architecture.Star100OpeningKernel

namespace PM.Architecture.Star100SecondKernel
open Star100OpeningKernel

def MeetNonempty (m n : Class (Class α)) := ∃ c, m c ∧ n c
def SmImage (m : Class (Class α)) : Class (Class α) := fun b => ∃ a, m a ∧ Similar b a

theorem star_100_34 {a b : Class α} : MeetNonempty (Nc a) (Nc b) → Nc a = Nc b := by
  rintro ⟨c, hc, hd⟩
  exact star_100_321 (similar_trans (similar_symm hc) hd)
theorem star_100_35 (a b : Class α) : Nc a = Nc b ↔ Nc b a ∧ Nc a b ∧ Similar a b :=
  Star100OpeningKernel.star_100_35 a b
theorem star_100_36 {a b : Class α} : Nc a b → (NonemptyClass a ↔ NonemptyClass b) :=
  Star100OpeningKernel.star_100_36
theorem star_100_4 (m : Class (Class α)) : NC m ↔ ∃ a, m = Nc a := Iff.rfl
theorem star_100_41 (a : Class α) : NC (Nc a) := ⟨a, rfl⟩
theorem star_100_42 {m n : Class (Class α)} : NC m → NC n → MeetNonempty m n → m = n := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩ h; exact star_100_34 h
theorem star_100_43 {m n : Class (Class α)} : NC m → NC n → MeetNonempty m n → m = n :=
  star_100_42
theorem star_100_44 {m : Class (Class α)} (hm : NC m) (a : Class α) :
    m a ↔ Nc a = m := by
  obtain ⟨b, rfl⟩ := hm
  constructor
  · intro h; exact star_100_321 h
  · intro h; rw [← h]; exact similar_refl a
theorem star_100_45 {m : Class (Class α)} (hm : NC m) {a : Class α} : m a → Nc a = m :=
  (star_100_44 hm a).1
theorem star_100_5 {m : Class (Class α)} (hm : NC m) {a b : Class α} :
    m a → m b → Similar a b := by
  rintro ha hb; obtain ⟨c, rfl⟩ := hm
  exact similar_trans ha (similar_symm hb)
theorem star_100_51 {m : Class (Class α)} (hm : NC m) {a : Class α} (ha : m a) :
    SmImage m = Nc a := by
  funext b; apply propext; constructor
  · rintro ⟨c, hc, hbc⟩; exact similar_trans hbc (star_100_5 hm hc ha)
  · intro hba; exact ⟨a, ha, hba⟩
theorem star_100_511 {a : Class α} (ha : NonemptyClass (Nc a)) : SmImage (Nc a) = Nc a := by
  obtain ⟨b, hb⟩ := ha
  exact (star_100_51 (a := b) (star_100_41 a) hb).trans (star_100_321 hb)
theorem star_100_52 {m : Class (Class α)} (hm : NC m) (hne : NonemptyClass m) : NC (SmImage m) := by
  obtain ⟨a, ha⟩ := hne; rw [star_100_51 hm ha]; exact star_100_41 a
theorem star_100_521 {m : Class (Class α)} (hm : NC m) (hne : NonemptyClass m) :
    SmImage (SmImage m) = m := by
  obtain ⟨a, ha⟩ := hne
  rw [star_100_51 hm ha, star_100_51 (star_100_41 a) (similar_refl a)]
  exact (star_100_44 hm a).1 ha
theorem star_100_53 {m n : Class (Class α)} (hm : NC m) (hne : NonemptyClass m) :
    n = SmImage m ↔ NC n ∧ m = SmImage n := by
  constructor
  · rintro rfl; exact ⟨star_100_52 hm hne, (star_100_521 hm hne).symm⟩
  · rintro ⟨hn, hmn⟩
    have hnen : NonemptyClass n := by
      obtain ⟨b, hb⟩ := hne
      rw [hmn] at hb
      obtain ⟨a, ha, _⟩ := hb
      exact ⟨a, ha⟩
    rw [hmn, star_100_521 hn hnen]

end PM.Architecture.Star100SecondKernel
