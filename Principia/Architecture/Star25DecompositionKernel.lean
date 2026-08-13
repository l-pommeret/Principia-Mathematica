import Principia.Architecture.Star25FurtherKernel

/-! Ten consecutive PM I propositions ✱25·432–✱25·491 (pp. 243–244). -/

namespace PM.Architecture.Star25DecompositionKernel

open PM.Architecture.Star25OpeningKernel
open PM.Architecture.Star25MiddleKernel

/-- PM I ✱25·432. -/
theorem star_25_432 (p q r : Relation Left Right) :
    union (difference p r) (intersection q r) =
      union (union (intersection p q) (difference p r))
        (intersection q r) := by
  funext x y
  apply propext
  constructor
  · rintro (⟨hp, hnr⟩ | ⟨hq, hr⟩)
    · exact Or.inl (Or.inr ⟨hp, hnr⟩)
    · exact Or.inr ⟨hq, hr⟩
  · rintro ((⟨hp, hq⟩ | ⟨hp, hnr⟩) | ⟨hq, hr⟩)
    · by_cases hr : r x y
      · exact Or.inr ⟨hq, hr⟩
      · exact Or.inl ⟨hp, hr⟩
    · exact Or.inl ⟨hp, hnr⟩
    · exact Or.inr ⟨hq, hr⟩

/-- PM I ✱25·44. -/
theorem star_25_44 (p q r : Relation Left Right) :
    intersection (union p r) (union q (complement r)) =
      union (intersection p (complement r)) (intersection q r) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hp | hr, hq | hnr⟩
    · by_cases h : r x y
      · exact Or.inr ⟨hq, h⟩
      · exact Or.inl ⟨hp, h⟩
    · exact Or.inl ⟨hp, hnr⟩
    · exact Or.inr ⟨hq, hr⟩
    · exact False.elim (hnr hr)
  · rintro (⟨hp, hnr⟩ | ⟨hq, hr⟩)
    · exact ⟨Or.inl hp, Or.inr hnr⟩
    · exact ⟨Or.inr hr, Or.inl hq⟩

/-- PM I ✱25·45. -/
theorem star_25_45 (p q r : Relation Left Right) :
    union (intersection p r) (difference q r) = nullRelation Left Right ↔
      Included q r ∧ Included r (complement p) := by
  constructor
  · intro empty
    constructor
    · intro x y hq
      apply Classical.byContradiction
      intro hnr
      have : nullRelation Left Right x y := by
        rw [← empty]
        exact Or.inr ⟨hq, hnr⟩
      exact this
    · intro x y hr hp
      have : nullRelation Left Right x y := by
        rw [← empty]
        exact Or.inl ⟨hp, hr⟩
      exact this
  · rintro ⟨hqr, hrnp⟩
    funext x y
    apply propext
    constructor
    · rintro (⟨hp, hr⟩ | ⟨hq, hnr⟩)
      · exact hrnp x y hr hp
      · exact hnr (hqr x y hq)
    · intro impossible
      exact False.elim impossible

/-- PM I ✱25·46. -/
theorem star_25_46 (p q r : Relation Left Right) :
    union (intersection p r) (difference q r) = nullRelation Left Right →
      intersection p q = nullRelation Left Right := by
  intro empty
  funext x y
  apply propext
  constructor
  · rintro ⟨hp, hq⟩
    by_cases hr : r x y
    · have : nullRelation Left Right x y := by
        rw [← empty]
        exact Or.inl ⟨hp, hr⟩
      exact this
    · have : nullRelation Left Right x y := by
        rw [← empty]
        exact Or.inr ⟨hq, hr⟩
      exact this
  · intro impossible
    exact False.elim impossible

/-- PM I ✱25·47. -/
theorem star_25_47 (p q r : Relation Left Right) :
    (intersection p q = nullRelation Left Right ∧ union p q = r) ↔
      (Included p r ∧ q = difference r p) := by
  simp only [Included, difference]
  constructor <;> intro h
  · rcases h with ⟨hdisjoint, hunion⟩
    constructor
    · intro x y hp
      rw [← hunion]
      exact Or.inl hp
    · funext x y
      apply propext
      constructor
      · intro hq
        refine ⟨?_, ?_⟩
        · rw [← hunion]; exact Or.inr hq
        · intro hp
          have impossible : nullRelation Left Right x y := by
            rw [← hdisjoint]
            exact ⟨hp, hq⟩
          exact impossible
      · rintro ⟨hr, hnp⟩
        rw [← hunion] at hr
        exact hr.resolve_left hnp
  · rcases h with ⟨hpr, hq⟩
    subst q
    constructor
    · funext x y
      apply propext
      exact ⟨fun h => h.2.2 h.1, fun impossible => False.elim impossible⟩
    · funext x y
      apply propext
      constructor
      · rintro (hp | ⟨hr, _⟩)
        · exact hpr x y hp
        · exact hr
      · intro hr
        by_cases hp : p x y
        · exact Or.inl hp
        · exact Or.inr ⟨hr, hp⟩

/-- PM I ✱25·48. -/
theorem star_25_48 (p q r r' s s' : Relation Left Right) :
    Included r p → Included r' p → Included s q → Included s' q →
    intersection p q = nullRelation Left Right →
      (union r s = union r' s' ↔ r = r' ∧ s = s') := by
  intro hrp hr'p hsq hs'q hpq
  constructor
  · intro equality
    constructor
    · funext x y
      apply propext
      constructor
      · intro hr
        have : union r' s' x y := by rw [← equality]; exact Or.inl hr
        cases this with
        | inl hr' => exact hr'
        | inr hs' =>
            have : nullRelation Left Right x y := by
              rw [← hpq]
              exact ⟨hrp x y hr, hs'q x y hs'⟩
            exact False.elim this
      · intro hr'
        have : union r s x y := by rw [equality]; exact Or.inl hr'
        cases this with
        | inl hr => exact hr
        | inr hs =>
            have : nullRelation Left Right x y := by
              rw [← hpq]
              exact ⟨hr'p x y hr', hsq x y hs⟩
            exact False.elim this
    · funext x y
      apply propext
      constructor
      · intro hs
        have : union r' s' x y := by rw [← equality]; exact Or.inr hs
        cases this with
        | inl hr' =>
            have : nullRelation Left Right x y := by
              rw [← hpq]
              exact ⟨hr'p x y hr', hsq x y hs⟩
            exact False.elim this
        | inr hs' => exact hs'
      · intro hs'
        have : union r s x y := by rw [equality]; exact Or.inr hs'
        cases this with
        | inl hr =>
            have : nullRelation Left Right x y := by
              rw [← hpq]
              exact ⟨hrp x y hr, hs'q x y hs'⟩
            exact False.elim this
        | inr hs => exact hs
  · rintro ⟨rfl, rfl⟩
    rfl

/-- PM I ✱25·481. -/
theorem star_25_481 (p q r : Relation Left Right) :
    intersection p q = nullRelation Left Right →
    intersection p r = nullRelation Left Right →
      (union p q = union p r ↔ q = r) := by
  intro hpq hpr
  constructor
  · intro equality
    have hq : Included q (complement p) := by
      intro x y hqx hpx
      have impossible : nullRelation Left Right x y := by
        rw [← hpq]
        exact ⟨hpx, hqx⟩
      exact impossible
    have hr : Included r (complement p) := by
      intro x y hrx hpx
      have impossible : nullRelation Left Right x y := by
        rw [← hpr]
        exact ⟨hpx, hrx⟩
      exact impossible
    exact ((star_25_48 p (complement p) p p q r
      (fun _ _ h => h) (fun _ _ h => h) hq hr
      (PM.Architecture.Star25MiddleKernel.star_25_21 p))).1 equality |>.2
  · rintro rfl
    rfl

/-- PM I ✱25·482. -/
theorem star_25_482 (p q r s : Relation Left Right) :
    Included r p → Included s q →
    intersection p q = nullRelation Left Right →
      (union r s = union p q ↔ r = p ∧ s = q) := by
  intro hr hs hpq
  exact star_25_48 p q r p s q hr (fun _ _ h => h) hs (fun _ _ h => h) hpq

/-- PM I ✱25·49. -/
theorem star_25_49 (p q r : Relation Left Right) :
    intersection p q = nullRelation Left Right →
      (Included p (union q r) ↔ Included p r) := by
  intro disjoint
  constructor
  · intro included x y hp
    cases included x y hp with
    | inl hq =>
        have : nullRelation Left Right x y := by rw [← disjoint]; exact ⟨hp, hq⟩
        exact False.elim this
    | inr hr => exact hr
  · intro included x y hp
    exact Or.inr (included x y hp)

/-- PM I ✱25·491: the three displayed decomposition conclusions. -/
theorem star_25_491 (p q r : Relation Left Right) :
    intersection q r = nullRelation Left Right →
    Included p (union q r) →
      difference p q = intersection p r ∧
      difference p r = intersection p q ∧
      p = union (difference p q) (difference p r) := by
  intro disjoint included
  have split : ∀ x y, p x y → q x y ∨ r x y := included
  constructor
  · funext x y
    apply propext
    constructor
    · rintro ⟨hp, hnq⟩
      exact ⟨hp, (split x y hp).resolve_left hnq⟩
    · rintro ⟨hp, hr⟩
      refine ⟨hp, ?_⟩
      intro hq
      have : nullRelation Left Right x y := by rw [← disjoint]; exact ⟨hq, hr⟩
      exact this
  · constructor
    · funext x y
      apply propext
      constructor
      · rintro ⟨hp, hnr⟩
        exact ⟨hp, (split x y hp).resolve_right hnr⟩
      · rintro ⟨hp, hq⟩
        refine ⟨hp, ?_⟩
        intro hr
        have : nullRelation Left Right x y := by rw [← disjoint]; exact ⟨hq, hr⟩
        exact this
    · funext x y
      apply propext
      constructor
      · intro hp
        cases split x y hp with
        | inl hq =>
            right
            refine ⟨hp, ?_⟩
            intro hr
            have : nullRelation Left Right x y := by rw [← disjoint]; exact ⟨hq, hr⟩
            exact this
        | inr hr =>
            left
            refine ⟨hp, ?_⟩
            intro hq
            have : nullRelation Left Right x y := by rw [← disjoint]; exact ⟨hq, hr⟩
            exact this
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

end PM.Architecture.Star25DecompositionKernel
