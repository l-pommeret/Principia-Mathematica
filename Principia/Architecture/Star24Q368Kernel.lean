import Principia.Architecture.Star22Q341Definitions

namespace PM.Architecture.Star24Q368Kernel

open PM.Architecture.Star22Q341Definitions

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x
  exact propext (h x)

/-- PM I ✱24·41: every class decomposes into its part inside and outside a
second class. -/
theorem star_24_41 (a b : Class α) :
    a = Union (Intersection a b) (Difference a b) := by
  classical
  apply class_ext
  intro x
  constructor
  · intro ha
    by_cases hb : b x
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha

/-- PM I ✱24·411: when `b` is included in `a`, the intersection component
of ✱24·41 is exactly `b`. -/
theorem star_24_411 (a b : Class α) :
    Included b a → a = Union b (Difference a b) := by
  classical
  intro hba
  apply class_ext
  intro x
  constructor
  · intro ha
    by_cases hb : b x
    · exact Or.inl hb
    · exact Or.inr ⟨ha, hb⟩
  · rintro (hb | ⟨ha, _⟩)
    · exact hba x hb
    · exact ha

/-- PM I ✱24·412: adjacent differences telescope along nested inclusions. -/
theorem star_24_412 (a b c : Class α) :
    Included b a → Included c b →
      Union (Difference a b) (Difference b c) = Difference a c := by
  classical
  intro hba hcb
  apply class_ext
  intro x
  constructor
  · rintro (⟨ha, _⟩ | ⟨hb, hnc⟩)
    · exact ⟨ha, fun hc => ‹¬ b x› (hcb x hc)⟩
    · exact ⟨hba x hb, hnc⟩
  · rintro ⟨ha, hnc⟩
    by_cases hb : b x
    · exact Or.inr ⟨hb, hnc⟩
    · exact Or.inl ⟨ha, hb⟩

/-- PM I ✱24·42: inclusion of both decomposition components is equivalent
to inclusion of the original class. -/
theorem star_24_42 (a b c : Class α) :
    (Included (Intersection a b) c ∧ Included (Difference a b) c) ↔
      Included a c := by
  classical
  constructor
  · rintro ⟨hin, hout⟩ x ha
    by_cases hb : b x
    · exact hin x ⟨ha, hb⟩
    · exact hout x ⟨ha, hb⟩
  · intro hac
    exact ⟨fun x h => hac x h.1, fun x h => hac x h.1⟩

/-- PM I ✱24·43: inclusion of a difference is equivalent to inclusion in
the union with the subtracted class. -/
theorem star_24_43 (a b c : Class α) :
    Included (Difference a b) c ↔ Included a (Union b c) := by
  classical
  constructor
  · intro h x ha
    by_cases hb : b x
    · exact Or.inl hb
    · exact Or.inr (h x ⟨ha, hb⟩)
  · intro h x hdiff
    exact (h x hdiff.1).resolve_left hdiff.2

end PM.Architecture.Star24Q368Kernel
