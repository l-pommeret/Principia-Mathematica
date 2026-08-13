import Principia.Architecture.Star25LaterKernel

/-! Ten consecutive PM I propositions ✱25·39–✱25·431 (pp. 243–244). -/

namespace PM.Architecture.Star25FurtherKernel

open PM.Architecture.Star25OpeningKernel
open PM.Architecture.Star25MiddleKernel

/-- PM I ✱25·39. -/
theorem star_25_39 (relation other : Relation Left Right) :
    intersection relation other = nullRelation Left Right ↔
      Included relation (complement other) :=
  (PM.Architecture.Star25LaterKernel.star_25_311 relation other).symm

/-- PM I ✱25·4: the three printed propositions form one equivalence chain. -/
theorem star_25_4 (p q : Relation Left Right) :
    (intersection p q = nullRelation Left Right ↔
      difference (union p q) p = q) ∧
    (difference (union p q) p = q ↔
      difference (union p q) q = p) := by
  have first : intersection p q = nullRelation Left Right ↔
      difference (union p q) p = q := by
    constructor
    · intro disjoint
      funext x y
      apply propext
      constructor
      · rintro ⟨hp | hq, hnp⟩
        · exact False.elim (hnp hp)
        · exact hq
      · intro hq
        refine ⟨Or.inr hq, ?_⟩
        intro hp
        have : nullRelation Left Right x y := by
          rw [← disjoint]
          exact ⟨hp, hq⟩
        exact this
    · intro equation
      funext x y
      apply propext
      constructor
      · rintro ⟨hp, hq⟩
        have inDifference : difference (union p q) p x y := by
          rw [equation]
          exact hq
        exact inDifference.2 hp
      · intro impossible
        exact False.elim impossible
  have second : intersection p q = nullRelation Left Right ↔
      difference (union p q) q = p := by
    constructor
    · intro disjoint
      funext x y
      apply propext
      constructor
      · rintro ⟨hp | hq, hnq⟩
        · exact hp
        · exact False.elim (hnq hq)
      · intro hp
        refine ⟨Or.inl hp, ?_⟩
        intro hq
        have : nullRelation Left Right x y := by
          rw [← disjoint]
          exact ⟨hp, hq⟩
        exact this
    · intro equation
      funext x y
      apply propext
      constructor
      · rintro ⟨hp, hq⟩
        have inDifference : difference (union p q) q x y := by
          rw [equation]
          exact hp
        exact inDifference.2 hq
      · intro impossible
        exact False.elim impossible
  exact ⟨first, first.symm.trans second⟩

/-- PM I ✱25·401. -/
theorem star_25_401 (p q r : Relation Left Right) :
    Included q p → difference (union q r) p = difference r p := by
  intro included
  funext x y
  apply propext
  constructor
  · rintro ⟨hq | hr, hnp⟩
    · exact False.elim (hnp (included x y hq))
    · exact ⟨hr, hnp⟩
  · rintro ⟨hr, hnp⟩
    exact ⟨Or.inr hr, hnp⟩

/-- PM I ✱25·402. -/
theorem star_25_402 (p q r s : Relation Left Right) :
    intersection p q = nullRelation Left Right →
    Included r p → Included s q →
      intersection r s = nullRelation Left Right := by
  intro disjoint hr hs
  funext x y
  apply propext
  constructor
  · rintro ⟨hxr, hxs⟩
    have : nullRelation Left Right x y := by
      rw [← disjoint]
      exact ⟨hr x y hxr, hs x y hxs⟩
    exact this
  · intro impossible
    exact False.elim impossible

/-- PM I ✱25·41. -/
theorem star_25_41 (r s : Relation Left Right) :
    r = union (intersection r s) (difference r s) := by
  funext x y
  apply propext
  constructor
  · intro hr
    by_cases hs : s x y
    · exact Or.inl ⟨hr, hs⟩
    · exact Or.inr ⟨hr, hs⟩
  · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr

/-- PM I ✱25·411. -/
theorem star_25_411 (r s : Relation Left Right) :
    Included s r → r = union s (difference r s) := by
  intro included
  funext x y
  apply propext
  constructor
  · intro hr
    by_cases hs : s x y
    · exact Or.inl hs
    · exact Or.inr ⟨hr, hs⟩
  · rintro (hs | ⟨hr, _⟩)
    · exact included x y hs
    · exact hr

/-- PM I ✱25·412. -/
theorem star_25_412 (p q s : Relation Left Right) :
    Included q p → Included s q →
      union (difference p q) (difference q s) = difference p s := by
  intro hqp hsq
  funext x y
  apply propext
  constructor
  · rintro (⟨hp, hnq⟩ | ⟨hq, hns⟩)
    · exact ⟨hp, fun hs => hnq (hsq x y hs)⟩
    · exact ⟨hqp x y hq, hns⟩
  · rintro ⟨hp, hns⟩
    by_cases hq : q x y
    · exact Or.inr ⟨hq, hns⟩
    · exact Or.inl ⟨hp, hq⟩

/-- PM I ✱25·42. -/
theorem star_25_42 (p q r : Relation Left Right) :
    (Included (intersection p q) r ∧ Included (difference p q) r) ↔
      Included p r := by
  constructor
  · rintro ⟨hi, hd⟩ x y hp
    by_cases hq : q x y
    · exact hi x y ⟨hp, hq⟩
    · exact hd x y ⟨hp, hq⟩
  · intro hp
    exact ⟨fun x y h => hp x y h.1, fun x y h => hp x y h.1⟩

/-- PM I ✱25·43. -/
theorem star_25_43 (p q r : Relation Left Right) :
    Included (difference p q) r ↔ Included p (union q r) := by
  constructor
  · intro included x y hp
    by_cases hq : q x y
    · exact Or.inl hq
    · exact Or.inr (included x y ⟨hp, hq⟩)
  · intro included x y h
    rcases h with ⟨hp, hnq⟩
    cases included x y hp with
    | inl hq => exact False.elim (hnq hq)
    | inr hr => exact hr

/-- PM I ✱25·431. -/
theorem star_25_431 (p q r : Relation Left Right) :
    intersection (union p r) (union q (complement r)) =
      union (union (intersection p q) (difference p r))
        (intersection q r) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hp | hr, hq | hnr⟩
    · exact Or.inl (Or.inl ⟨hp, hq⟩)
    · exact Or.inl (Or.inr ⟨hp, hnr⟩)
    · exact Or.inr ⟨hq, hr⟩
    · exact False.elim (hnr hr)
  · rintro ((⟨hp, hq⟩ | ⟨hp, hnr⟩) | ⟨hq, hr⟩)
    · exact ⟨Or.inl hp, Or.inl hq⟩
    · exact ⟨Or.inl hp, Or.inr hnr⟩
    · exact ⟨Or.inr hr, Or.inl hq⟩

end PM.Architecture.Star25FurtherKernel
